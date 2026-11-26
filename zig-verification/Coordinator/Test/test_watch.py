"""Read production run records without a model provider or a Lean process."""
import hashlib
import json
from pathlib import Path
from dataclasses import replace
import tempfile
import unittest
import subprocess
import sys

from Coordinator import watch


def certificate(rules):
    value = json.dumps({"rules": rules, "finalProof": False, "finalDisproof": False}).encode()
    number = 0
    for byte in reversed(value):
        number = byte + 1 + 257 * number
    return number


class WatchTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.run = Path(self.temp.name)
        (self.run / "artifacts").mkdir()
        self.registry = [{"names": ["first_go"], "root": True},
                         {"names": ["second_go"], "root": True}]
        manifest = {"settings": {"budget": 1000000, "turns": 100,
                    "model": "test-worker", "coordinator": {"model": "test-plan", "turns": 8}},
                    "initial": {"registry": self.registry, "roots": [0, 1],
                                "revision": {"source": certificate([])}}}
        (self.run / "manifest.json").write_text(json.dumps(self.artifact(manifest)))
        self.events = self.run / "events.jsonl"
        self.events.touch()
        self.monitor = watch.Monitor(self.run)

    def artifact(self, value):
        text = json.dumps(value)
        digest = hashlib.sha256(text.encode()).hexdigest()
        (self.run / "artifacts" / digest).write_text(text)
        return digest

    def event(self, value):
        with self.events.open("a") as output:
            output.write(json.dumps({"payload": value}) + "\n")

    def model(self, value):
        self.event({"event": "model", "input": value})

    def worker(self, value, job=0):
        self.event({"event": "worker", "job": job, "artifact": self.artifact(value)})

    def start(self):
        kind = {"proof": {"goal": 0}}
        self.model({"start": {"kind": kind}})
        self.model({"reserve": {"owner": 0, "bound": 500000}})
        self.event({"event": "spawn", "job": 0, "spec": self.artifact({"kind": kind})})

    def result(self, job=0):
        self.event({"event": "result", "result": {"job": job, "kind": {"proof": {"goal": 0}},
                    "report": {"artifact": {"source": 1}}, "memory": "Checked.",
                    "receipt": {"revision": {"source": certificate([])}}}})

    def test_accepted_proof_is_not_published_until_publication(self):
        self.start()
        self.result()
        view = self.monitor.refresh()
        self.assertEqual(view.accepted, frozenset({0}))
        self.assertEqual(view.published, frozenset())
        self.event({"event": "revision", "commit": "abc", "receipt": {
            "registry": self.registry, "revision": {"source": certificate([
                {"target": 0, "premises": [2]}, {"target": 2, "premises": []}])}}})
        self.assertFalse(self.monitor.refresh().published)
        self.event({"event": "published", "commit": "abc"})
        self.assertEqual(self.monitor.refresh().published, frozenset({0}))

    def test_duplicate_results_and_charges_do_not_inflate_progress_or_cost(self):
        self.start()
        self.result()
        self.result()
        for _ in range(2):
            self.event({"event": "grant", "job": 0, "request": 0})
            self.event({"event": "charge", "job": 0, "request": 0, "charge": 120})
            self.worker({"event": "usage", "request": 0, "prompt": 100,
                         "cached": 90, "completion": 20})
        view = self.monitor.refresh()
        self.assertEqual(len(view.accepted), 1)
        self.assertEqual(view.spent, 120)
        self.assertEqual(view.replies, 1)
        self.assertEqual(view.cache_fraction, 0.9)
        self.assertEqual(view.pending_requests, 0)
        self.assertEqual(self.monitor.refresh(), view)

    def test_partial_journal_line_is_read_only_after_it_is_complete(self):
        kind = {"proof": {"goal": 0}}
        self.monitor.pending_kind = kind
        value = json.dumps({"payload": {"event": "spawn", "job": 0,
                                       "spec": self.artifact({"kind": kind})}})
        self.events.write_text(value[:20])
        self.assertEqual(len(self.monitor.refresh().workers), 0)
        with self.events.open("a") as output:
            output.write(value[20:] + "\n")
        self.assertEqual(len(self.monitor.refresh().workers), 1)

    def test_large_and_invalid_artifacts_are_skipped_without_reading_them(self):
        digest = "a" * 64
        with (self.run / "artifacts" / digest).open("wb") as output:
            output.truncate(128 * 1024 * 1024)
        self.event({"event": "worker", "job": 0, "artifact": digest})
        self.event({"event": "worker", "job": 0, "artifact": "../../outside"})
        view = self.monitor.refresh()
        self.assertEqual(view.skipped, 2)
        self.assertEqual(view.replies, 0)

    def test_tool_error_is_visible_and_does_not_finish_the_worker(self):
        self.start()
        self.worker({"event": "tool", "name": "edit", "reply": {
            "ok": False, "error": "heartbeat limit"}})
        worker = self.monitor.refresh().workers[0]
        self.assertEqual(worker.status, "running")
        self.assertIn("heartbeat limit", worker.detail)
        self.assertEqual(worker.tool_errors, 1)

    def test_terminal_checkpoint_and_missing_checkpoint(self):
        self.start()
        self.assertEqual(self.monitor.refresh().phase, "running")
        (self.run / "checkpoint.json").write_text(json.dumps({
            "state": {"phase": {"done": {"reason": "cancelled"}}}}))
        self.assertEqual(self.monitor.refresh().phase, "cancelled")
        self.assertEqual(self.monitor.refresh().workers[0].status, "stopped")

    def test_launcher_error_overrides_a_proved_checkpoint(self):
        self.start()
        (self.run / "checkpoint.json").write_text(json.dumps({
            "state": {"phase": {"done": {"reason": "proved"}}}}))
        (self.run / "launcher-result.json").write_text(json.dumps({
            "exitCode": 2, "log": "/tmp/proof-run.log"}))
        view = self.monitor.refresh()
        self.assertEqual(view.phase, "infrastructure error")
        self.assertEqual(view.exit_code, 2)
        text = "\n".join(line.text for line in watch.render(view, 120, 30))
        self.assertIn("FINAL", text)
        self.assertIn("exit 2", text)
        self.assertIn("q close", text)

    def test_finished_view_keeps_proof_and_worker_results(self):
        self.start()
        self.result()
        (self.run / "checkpoint.json").write_text(json.dumps({
            "state": {"phase": {"done": {"reason": "exhausted"}}}}))
        (self.run / "launcher-result.json").write_text(json.dumps({
            "exitCode": 1, "log": "/tmp/proof-run.log"}))
        view = self.monitor.refresh()
        self.assertEqual(view.phase, "exhausted")
        self.assertEqual(view.accepted, frozenset({0}))
        self.assertEqual(len(view.workers), 1)
        self.assertEqual(view.workers[0].status, "accepted")
        self.assertEqual(self.monitor.refresh(), view)

    def test_reservations_are_replaced_by_settled_charges(self):
        self.model({"reserve": {"owner": 0, "bound": 500000}})
        self.model({"settle": {"id": 0, "amount": 120}})
        self.assertEqual(self.monitor.refresh().committed, 120)

    def test_unaccepted_start_input_does_not_create_a_phantom_worker(self):
        self.model({"start": {"kind": "coordinator"}})
        self.assertEqual(self.monitor.refresh().workers, ())

    def test_large_manifest_keeps_budget_and_worker_limits(self):
        ref = json.loads((self.run / "manifest.json").read_text())
        manifest = json.loads((self.run / "artifacts" / ref).read_text())
        manifest["proverPrompt"] = "x" * 300000
        (self.run / "manifest.json").write_text(json.dumps(self.artifact(manifest)))
        self.start()
        view = self.monitor.refresh()
        self.assertEqual(view.budget, 1000000)
        self.assertEqual(view.workers[0].limit, 100)
        self.assertEqual(view.skipped, 0)

    def test_journal_truncation_resets_the_cursor_and_counters(self):
        self.start()
        self.result()
        self.assertTrue(self.monitor.refresh().accepted)
        self.events.write_text("")
        view = self.monitor.refresh()
        self.assertEqual(view.workers, ())
        self.assertFalse(view.accepted)

    def test_terminal_control_characters_are_not_rendered(self):
        self.start()
        self.worker({"event": "failed", "reason": "\x1b[31merror\x07"})
        lines = watch.render(self.monitor.refresh(), 100, 30)
        self.assertTrue(all("\x1b" not in line.text and "\x07" not in line.text for line in lines))

    def test_once_command_does_not_modify_run_records(self):
        self.start()
        before = {str(p): p.read_bytes() for p in self.run.rglob("*") if p.is_file()}
        result = subprocess.run([sys.executable, watch.__file__, str(self.run), "--once"],
                                capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("PROOF OVERVIEW", result.stdout)
        self.assertIn("test-worker", result.stdout)
        after = {str(p): p.read_bytes() for p in self.run.rglob("*") if p.is_file()}
        self.assertEqual(before, after)

    def test_invalid_run_and_refresh_interval_report_errors(self):
        for args in [[str(self.run / "missing"), "--once"], [str(self.run), "--interval", "0"]]:
            result = subprocess.run([sys.executable, watch.__file__, *args],
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 2)

    def test_layout_fits_small_and_large_terminals(self):
        self.start()
        view = self.monitor.refresh()
        for width, height in [(120, 42), (80, 24), (40, 12), (10, 3)]:
            with self.subTest(width=width, height=height):
                for worker_view in (False, True):
                    lines = watch.render(view, width, height, selected=0, offset=0,
                                         active_only=False, worker_view=worker_view)
                    self.assertLessEqual(len(lines), height)
                    self.assertTrue(all(watch.cell_width(line.text) <= width for line in lines))

    def test_compact_overview_shows_all_nine_roots(self):
        self.start()
        view = replace(self.monitor.refresh(), roots=tuple((g, f"root_{g}") for g in range(9)))
        text = "\n".join(line.text for line in watch.render(view, 80, 24))
        for goal in range(9):
            self.assertIn(f"root_{goal}", text)
        self.assertIn("q quit", text)

    def test_certificate_cycles_and_missing_dependencies_stay_open(self):
        self.assertEqual(watch.closed_goals(certificate([
            {"target": 0, "premises": [1]}, {"target": 1, "premises": [0]},
            {"target": 2, "premises": [3]}])), frozenset())
        self.assertEqual(watch.closed_goals(12), frozenset())


if __name__ == "__main__":
    unittest.main()
