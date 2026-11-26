"""Read records of `leantools prove` without a model provider or a Lean process.

The fixtures are records that `leantools prove` wrote with the scripted model of
pkgs/leantools/Test/mock_http.py. A record cut after a line is the record of a run in progress.
"""
from dataclasses import replace
import json
import os
from pathlib import Path
import random
import signal
import subprocess
import sys
import tempfile
import unittest

from Coordinator import prove_watch, watch

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = Path(__file__).resolve().parent / "fixtures" / "prove-watch"
A, B = "Nx/Proof/CastToArray.lean", "Nx/Proof/ValueAssign.lean"


def flat(file):
    return file.replace("/", "_")


class ProveWatchTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.runs = self.root / ".leantools" / "runs"
        self.runs.mkdir(parents=True)
        self.log = self.root / "prove.log"

    def write_log(self, *lines, start=1, files=(A,)):
        head = [f"batch start {start}"] + [f"file {f}" for f in files]
        self.log.write_text("".join(line + "\n" for line in head + list(lines)))

    def record(self, fixture, file=A, events=None, summary=True, stamp="2026-11-12T23-08-48.026055000"):
        run = self.runs / f"{stamp}-{flat(file)}"
        run.mkdir()
        data = (FIXTURES / fixture / "events.jsonl").read_bytes()
        if events is not None:
            data = b"".join(data.splitlines(keepends=True)[:events])
        (run / "events.jsonl").write_bytes(data)
        if summary and events is None:
            (run / "summary.json").write_bytes((FIXTURES / fixture / "summary.json").read_bytes())
        return run

    def view(self):
        monitor = prove_watch.Monitor(self.log)
        return monitor.refresh()

    def test_log_lines_parse_to_a_batch(self):
        batch = prove_watch.parse_log(
            "batch start 17\nfile a/X.lean\nfile a/Y.lean\n[a/X.lean] first\n[a/X.lean] second\n"
            "exit a/X.lean 0\nexit a/Y.lean 2\nbatch end 30\n")
        self.assertEqual(batch.start, 17)
        self.assertEqual(batch.files, ("a/X.lean", "a/Y.lean"))
        self.assertEqual(batch.exits, {"a/X.lean": 0, "a/Y.lean": 2})
        self.assertEqual(batch.output, {"a/X.lean": ("first", "second")})
        self.assertTrue(batch.ended)
        self.assertEqual(batch.skipped, 0)

    def test_log_lines_of_other_forms_are_counted(self):
        batch = prove_watch.parse_log("batch start x\nnoise\nexit a/X.lean zero\n[b] text of a file not in the batch\n"
                                      "exit b 1\nfile a/X.lean\nbatch end")
        self.assertEqual((batch.start, batch.files, batch.exits, batch.ended), (0, ("a/X.lean",), {}, False))
        self.assertEqual(batch.skipped, 6)
        self.assertEqual(prove_watch.parse_log(""), prove_watch.Batch())

    def test_names_drop_the_common_directory(self):
        self.assertEqual(prove_watch.names((A, B)), ("CastToArray", "ValueAssign"))
        self.assertEqual(prove_watch.names((A,)), ("CastToArray",))
        self.assertEqual(prove_watch.names(("X.lean", "a/X.lean")), ("X", "a/X"))
        self.assertEqual(prove_watch.names(()), ())

    def test_a_file_without_a_record_is_queued(self):
        self.write_log(files=(A, B))
        view = self.view()
        self.assertEqual(view.roots, ((0, "CastToArray"), (1, "ValueAssign")))
        self.assertEqual([(w.goal, w.status, w.replies) for w in view.workers], [(0, "queued", 0), (1, "queued", 0)])
        self.assertEqual((view.phase, view.exit_code, view.spent, view.accepted), ("running", None, 0, frozenset()))

    def test_no_log_gives_an_empty_running_view(self):
        view = self.view()
        self.assertEqual((view.roots, view.workers, view.phase, view.exit_code), ((), (), "running", None))

    def test_first_iteration_before_a_reply(self):
        self.write_log()
        self.record("accepted-second", events=2)
        view = self.view()
        self.assertEqual([(w.id, w.status, w.replies, w.limit) for w in view.workers], [(1, "running", 0, 5)])
        self.assertEqual((view.pending_requests, view.budget), (1, 20_000_000))

    def test_context_limit_shows_activity_without_charging_a_reply(self):
        for reason in ("input context threshold reached", "provider refused the input context"):
            with self.subTest(reason=reason):
                run = prove_watch.step(prove_watch.Run(), {"event": "iteration", "iteration": 1, "turns": 100})
                before = run.attempts[-1]
                after = prove_watch.step(run, {"event": "context-limit", "reason": reason})
                self.assertEqual(after.last, "context-limit")
                self.assertEqual(after.attempts[-1].activity, "context limit: " + reason)
                self.assertEqual(replace(after.attempts[-1], activity=before.activity), before)

    def test_unknown_event_is_still_rejected(self):
        run = prove_watch.step(prove_watch.Run(), {"event": "iteration", "iteration": 1, "turns": 100})
        with self.assertRaises(ValueError):
            prove_watch.step(run, {"event": "unknown"})

    def test_second_iteration_in_progress(self):
        self.write_log()
        self.record("accepted-second", events=13)
        view = self.view()
        first, second = view.workers
        self.assertEqual((first.id, first.status, first.replies, first.spent), (1, "rejected", 1, 2560))
        self.assertIn("Not accepted", first.detail)
        self.assertEqual((second.id, second.status, second.replies, second.spent), (2, "running", 1, 1280))
        self.assertEqual((second.tool, second.tool_errors, second.model), ("edit_working_file", 0, "mock-effective"))
        self.assertIn("No errors.", second.detail)
        self.assertGreater(second.last_reply, 0)
        self.assertEqual((view.spent, view.replies, view.accepted), (3840, 2, frozenset()))
        self.assertAlmostEqual(view.cache_fraction, 0.8)

    def test_accepted_run(self):
        self.write_log(f"[{A}] accepted after 2 iterations, 3 turns, 0.005120 USD", f"exit {A} 0", "batch end 9")
        self.record("accepted-second")
        view = self.view()
        self.assertEqual([w.status for w in view.workers], ["rejected", "accepted"])
        self.assertEqual((view.accepted, view.phase, view.exit_code, view.spent), (frozenset({0}), "complete", 0, 5120))
        self.assertEqual(view.log, str(self.log))
        self.assertIn("Accepted: touch_go proved", view.workers[1].detail)

    def test_three_rejections_and_a_tool_error(self):
        self.write_log(f"exit {A} 1", "batch end 9")
        self.record("rejected-thrice")
        view = self.view()
        self.assertEqual([(w.status, w.replies, w.tool_errors) for w in view.workers],
                         [("rejected", 2, 1), ("rejected", 1, 0), ("rejected", 1, 0)])
        self.assertEqual((view.accepted, view.phase, view.exit_code), (frozenset(), "stopped", 1))

    def test_tool_error_is_marked_until_the_next_tool(self):
        self.write_log()
        self.record("rejected-thrice", events=6)
        (worker,) = self.view().workers
        self.assertEqual((worker.tool, worker.tool_errors), ("edit_working_file !", 1))
        self.assertIn('unknown argument "bogus"', worker.detail)

    def test_refused_request(self):
        self.write_log(f"[{A}] failed after 1 iterations, 0 turns, 0.000000 USD", f"[{A}] HTTP 400: bad request: no model",
                       f"exit {A} 1")
        self.record("refused")
        view = self.view()
        (worker,) = view.workers
        self.assertEqual((worker.status, worker.replies), ("failed", 0))
        self.assertIn("HTTP 400", worker.detail)
        self.assertEqual((view.phase, view.exit_code), ("running", None))

    def test_refused_request_shows_the_status_while_the_run_is_live(self):
        self.write_log()
        self.record("refused", summary=False)
        (worker,) = self.view().workers
        self.assertEqual(worker.status, "running")
        self.assertIn("400", worker.activity)

    def test_exit_without_a_record_shows_the_output(self):
        self.write_log(f"[{A}] leantools prove: the variable MOCK_KEY is not set", f"exit {A} 2", "batch end 3")
        view = self.view()
        (worker,) = view.workers
        self.assertEqual(worker.status, "failed")
        self.assertIn("MOCK_KEY is not set", worker.detail)
        self.assertEqual((view.phase, view.exit_code), ("stopped", 2))
        self.assertEqual(view.feed, ("CastToArray: exit 2 · leantools prove: the variable MOCK_KEY is not set",
                                     "batch end: 0 of 1 accepted"))

    def test_batch_end_without_an_exit_stops_the_live_iteration(self):
        self.write_log("batch end 9")
        self.record("accepted-second", events=13)
        view = self.view()
        self.assertEqual([w.status for w in view.workers], ["rejected", "stopped"])
        self.assertEqual((view.phase, view.exit_code, view.pending_requests), ("stopped", 1, 0))

    def test_record_from_before_the_batch_is_not_used(self):
        run = self.record("accepted-second")
        os.utime(run / "events.jsonl", (1000, 1000))
        self.write_log(start=1001)
        self.assertEqual([w.status for w in self.view().workers], ["queued"])
        self.write_log(start=1000)
        self.assertEqual([w.status for w in self.view().workers], ["rejected", "accepted"])

    def test_newest_record_of_the_file_is_used(self):
        self.write_log(files=(A, B))
        self.record("rejected-thrice", stamp="2026-11-12T23-08-48.026055000")
        self.record("accepted-second", stamp="2026-11-12T23-10-18.211223000")
        self.record("refused", file="lib-" + A)
        view = self.view()
        self.assertEqual([(w.goal, w.status) for w in view.workers],
                         [(0, "rejected"), (0, "accepted"), (1, "queued")])

    def test_a_newer_record_replaces_the_cursor(self):
        self.write_log()
        self.record("rejected-thrice", stamp="2026-11-12T23-08-48.026055000")
        monitor = prove_watch.Monitor(self.log)
        self.assertEqual(len(monitor.refresh().workers), 3)
        self.record("accepted-second", stamp="2026-11-12T23-10-18.211223000")
        self.assertEqual([w.status for w in monitor.refresh().workers], ["rejected", "accepted"])

    def test_a_new_batch_in_the_log_starts_the_view_again(self):
        old = self.record("rejected-thrice", stamp="2026-11-12T23-08-48.026055000")
        os.utime(old / "events.jsonl", (1000, 1000))
        self.write_log(f"exit {A} 1", "batch end 1500", start=1000)
        monitor = prove_watch.Monitor(self.log)
        self.assertEqual((len(monitor.refresh().workers), len(monitor.notes)), (3, 9))
        self.write_log(start=2000)
        view = monitor.refresh()
        self.assertEqual(([w.status for w in view.workers], view.budget, view.spent, view.exit_code, monitor.notes),
                         (["queued"], 0, 0, None, []))
        new = self.record("accepted-second", stamp="2026-11-12T23-10-18.211223000", events=2)
        view = monitor.refresh()
        self.assertEqual(([w.status for w in view.workers], view.budget), (["running"], 20_000_000))
        self.assertEqual(monitor.notes, [f"CastToArray: run record {new}",
                                         "CastToArray: iteration 1 starts (limit 5 replies)"])

    def test_totals_agree_with_the_summary_of_the_harness(self):
        for fixture in ("accepted-second", "rejected-thrice", "refused"):
            with self.subTest(fixture):
                run = self.record(fixture, stamp="2026-11-12T23-08-48.026055000")
                self.write_log()
                view = self.view()
                summary = json.loads((run / "summary.json").read_text())
                self.assertEqual(view.spent, round(summary["cost_usd"] * 1_000_000))
                self.assertEqual(sum(w.spent for w in view.workers), view.spent)
                self.assertEqual(view.replies, summary["turns"])
                self.assertEqual(len(view.workers), summary["iterations"])
                self.assertEqual(sum(w.prompt for w in view.workers), summary["prompt_tokens"])
                self.assertEqual(sum(w.cached for w in view.workers), summary["cached_tokens"])
                self.assertEqual(sum(w.output for w in view.workers), summary["completion_tokens"])
                for child in run.iterdir():
                    child.unlink()
                run.rmdir()

    def test_record_read_in_parts_gives_the_view_of_one_read(self):
        rng = random.Random(20261112)
        for fixture in ("accepted-second", "rejected-thrice", "refused"):
            data = (FIXTURES / fixture / "events.jsonl").read_bytes()
            self.write_log()
            run = self.record(fixture, summary=False)
            whole = replace(self.view(), updated=0)
            for _ in range(40):
                cuts = sorted(rng.randrange(len(data) + 1) for _ in range(rng.randrange(1, 4)))
                (run / "events.jsonl").write_bytes(b"")
                monitor = prove_watch.Monitor(self.log)
                for cut in cuts + [len(data)]:
                    (run / "events.jsonl").write_bytes(data[:cut])
                    view = monitor.refresh()
                with self.subTest(fixture=fixture, cuts=cuts):
                    self.assertEqual(replace(view, updated=0, workers=tuple(replace(w, last_reply=0) for w in view.workers)),
                                     replace(whole, workers=tuple(replace(w, last_reply=0) for w in whole.workers)))
                    self.assertEqual(view.skipped, 0)
            for child in run.iterdir():
                child.unlink()
            run.rmdir()

    def test_damaged_record_lines_are_counted_and_skipped(self):
        self.write_log()
        run = self.record("accepted-second", summary=False)
        lines = (run / "events.jsonl").read_bytes().splitlines(keepends=True)
        damaged = lines[:3] + [b"{not json\n", b"[1, 2]\n", b'{"event": "reply"}\n', b"\xff\xfe\n"] + lines[3:]
        (run / "events.jsonl").write_bytes(b"".join(damaged))
        view = self.view()
        self.assertEqual(view.skipped, 4)
        self.assertEqual(([w.status for w in view.workers], view.spent), (["rejected", "accepted"], 5120))

    def test_long_record_needs_more_than_one_refresh(self):
        self.write_log()
        run = self.record("accepted-second", summary=False)
        filler = json.dumps({"event": "request-attempt", "status": 200, "attempt": 1, "pad": "x" * 1000}).encode() + b"\n"
        with (run / "events.jsonl").open("ab") as record:
            record.write(filler * (prove_watch.CHUNK // len(filler) + 2))
        monitor = prove_watch.Monitor(self.log)
        self.assertTrue(monitor.refresh().behind)
        view = monitor.refresh()
        self.assertFalse(view.behind)
        self.assertEqual([w.status for w in view.workers], ["rejected", "accepted"])

    def test_screen_of_watch_shows_the_batch(self):
        self.write_log(f"exit {A} 0", f"exit {B} 1", "batch end 9", files=(A, B))
        self.record("accepted-second")
        self.record("rejected-thrice", file=B)
        view = self.view()
        for width, height in ((120, 42), (80, 30), (59, 10)):
            text = "\n".join(line.text for line in watch.render(view, width, height))
            with self.subTest(width=width):
                self.assertIn("FINAL STOPPED" if width < 60 else "FINAL · STOPPED", text)
                if width >= 60:
                    self.assertIn("CastToArray", text)
                    self.assertIn("ValueAssign", text)
                    self.assertIn("1 / 2 accepted" if width >= 105 else "1/2 accepted", text)
                    self.assertIn("rejected", text)
                    self.assertIn("$0.015", text)

    def test_follow_writes_each_note_once(self):
        self.write_log(files=(A, B))
        data = (FIXTURES / "accepted-second" / "events.jsonl").read_bytes().splitlines(keepends=True)
        run = self.record("accepted-second", events=2)
        steps = [lambda: (run / "events.jsonl").write_bytes(b"".join(data[:13])),
                 lambda: None,
                 lambda: ((run / "events.jsonl").write_bytes(b"".join(data)),
                          (run / "summary.json").write_bytes((FIXTURES / "accepted-second" / "summary.json").read_bytes()),
                          self.write_log(f"exit {A} 0", files=(A, B))),
                 lambda: (self.record("refused", file=B),
                          self.write_log(f"exit {A} 0", f"exit {B} 1", "batch end 5", files=(A, B)))]
        clock, written = [0.0], []

        def sleep(seconds):
            clock[0] += seconds
            steps.pop(0)()

        code = prove_watch.follow(prove_watch.Monitor(self.log), written.append, interval=1, heartbeat=2,
                                  sleep=sleep, now=lambda: clock[0])
        self.assertEqual(code, 1)
        self.assertEqual(steps, [])
        notes = [line for line in written if "accepted ·" not in line]
        self.assertEqual(notes, [
            f"CastToArray: run record {run}",
            "CastToArray: iteration 1 starts (limit 5 replies)",
            "CastToArray: iteration 1 rejected after 1 replies",
            "CastToArray: iteration 2 starts (limit 5 replies)",
            "CastToArray: iteration 2 accepted after 2 replies",
            "CastToArray: exit 0 · accepted",
            f"ValueAssign: run record {self.runs / ('2026-11-12T23-08-48.026055000-' + flat(B))}",
            "ValueAssign: iteration 1 starts (limit 5 replies)",
            "ValueAssign: exit 1 · failed · HTTP 400: bad request: no model",
            "batch end: 1 of 2 accepted"])
        totals = [line for line in written if "accepted ·" in line]
        self.assertEqual(totals, ["0/2 accepted · 2 active · 2 replies · $0.004"])

    def test_follow_returns_zero_when_each_file_is_accepted(self):
        self.write_log(f"exit {A} 0", "batch end 9")
        self.record("accepted-second")
        written = []
        self.assertEqual(prove_watch.follow(prove_watch.Monitor(self.log), written.append, sleep=self.fail), 0)
        self.assertEqual(written[-1], "batch end: 1 of 1 accepted")

    def command(self, *args):
        return subprocess.run([sys.executable, "-m", "Coordinator.prove_watch", *args], cwd=ROOT,
                              text=True, capture_output=True, timeout=60)

    def test_command_once_prints_the_overview(self):
        self.write_log(f"exit {A} 0", "batch end 9")
        self.record("accepted-second")
        done = self.command("--once", str(self.log))
        self.assertEqual((done.returncode, done.stderr), (0, ""))
        self.assertIn("1 / 1 accepted", done.stdout)
        self.assertIn("CastToArray", done.stdout)

    def test_command_plain_gives_the_exit_status_of_the_batch(self):
        self.write_log(f"exit {A} 1", "batch end 9")
        self.record("rejected-thrice")
        done = self.command("--plain", "--runs", str(self.runs), str(self.log))
        self.assertEqual((done.returncode, done.stderr), (1, ""))
        self.assertIn("CastToArray: iteration 3 rejected after 1 replies", done.stdout)
        self.assertIn("batch end: 0 of 1 accepted", done.stdout)
        self.assertIn("0 / 1 accepted", done.stdout)

    def test_command_plain_stops_on_an_interrupt(self):
        self.write_log()
        self.record("accepted-second", events=2)
        child = subprocess.Popen([sys.executable, "-m", "Coordinator.prove_watch", "--plain", str(self.log)], cwd=ROOT,
                                 text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(child.kill)
        self.assertIn("run record", child.stdout.readline())
        child.send_signal(signal.SIGINT)
        out, err = child.communicate(timeout=30)
        self.assertEqual((child.returncode, err), (130, ""))
        self.assertNotIn("PROOF WATCH", out)

    def test_command_refuses_a_screen_without_a_terminal(self):
        self.write_log()
        done = self.command(str(self.log))
        self.assertEqual(done.returncode, 2)
        self.assertIn("--plain", done.stderr)


if __name__ == "__main__":
    unittest.main()
