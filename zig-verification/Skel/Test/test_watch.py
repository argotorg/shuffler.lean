"""Read Skel campaign records without Lean processes or model calls."""
from collections import defaultdict
from dataclasses import FrozenInstanceError, is_dataclass
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import Mock, patch

from Coordinator import watch as terminal_watch
from Skel import watch


FIXTURES = Path(__file__).resolve().parents[2] / "Coordinator" / "Test" / "fixtures" / "prove-watch"
STAMP = "2026-11-21T20-00-00.000000000"


def raw_row(fn="workspaceSize", name="block.entry", status="closed", detail=""):
    states = {
        "closed": {"closed": {"how": "tactics", "rung": "liftBlock/lift_block_split"}},
        "open": {"open": {"firstError": detail}},
        "not generated": {"notGenerated": {"cause": detail}},
    }
    return {"fn": fn, "name": name, "st": states[status], "model": "", "costMicro": 0}


def line(value):
    return json.dumps(value, separators=(",", ":")) + "\n"


class RowTests(unittest.TestCase):
    def test_raw_production_statuses(self):
        closed = watch.Row.parse(raw_row())
        self.assertEqual((closed.fn, closed.name, closed.status, closed.rung, closed.detail),
                         ("workspaceSize", "block.entry", "closed", "liftBlock/lift_block_split", ""))
        opened = watch.Row.parse(raw_row(status="open", detail="blocked: a dependency is not closed"))
        self.assertEqual((opened.status, opened.rung, opened.detail),
                         ("open", "", "blocked: a dependency is not closed"))
        absent = watch.Row.parse(raw_row(status="not generated", detail="no statement"))
        self.assertEqual((absent.status, absent.rung, absent.detail), ("not generated", "", "no statement"))

    def test_row_is_a_frozen_dataclass(self):
        row = watch.Row.parse(raw_row())
        self.assertTrue(is_dataclass(row))
        with self.assertRaises(FrozenInstanceError):
            row.status = "open"

    def test_invalid_shapes_and_field_types_are_rejected(self):
        values = [None, [], "closed", {}, {"fn": "f", "name": "x"}]
        for key, value in (("fn", None), ("fn", 1), ("name", False), ("name", []),
                           ("st", "closed"), ("st", None), ("st", {}),
                           ("st", {"unknown": {}}),
                           ("st", {"closed": {}}), ("st", {"open": {}}),
                           ("st", {"notGenerated": {}}),
                           ("st", {"closed": {"how": "tactics", "rung": 1}}),
                           ("st", {"closed": {"how": [], "rung": "closing"}}),
                           ("st", {"open": {"firstError": False}}),
                           ("st", {"notGenerated": {"cause": []}}),
                           ("model", 1), ("costMicro", "0"), ("costMicro", -1), ("costMicro", True)):
            values.append({**raw_row(), key: value})
        for value in values:
            with self.subTest(value=value), self.assertRaises(ValueError):
                watch.Row.parse(value)


class MonitorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.run = self.campaign("20261121T193016Z-full")
        self.journal = self.run / "rows.jsonl"
        self.records = self.root / ".leantools" / "runs"
        self.records.mkdir(parents=True)

    def campaign(self, name):
        run = self.root / ".skel" / "runs" / name
        run.mkdir(parents=True)
        return run

    def monitor(self, **kwargs):
        return watch.Monitor(self.run, root=self.root, **kwargs)

    def write_rows(self, *rows):
        self.journal.write_text("".join(line(r) for r in rows))

    def record(self, fixture="accepted-second", fn="workspaceSize", name="block.entry",
               campaign=None, stamp=STAMP, events=None, summary=True, link=None):
        campaign = campaign or self.run
        parent = campaign / "prove" / fn
        if link:
            parent /= link
        parent.mkdir(parents=True, exist_ok=True)
        frozen = parent / f"{name}.lean"
        frozen.write_text("-- Frozen file for the monitor test.\n")
        encoded = frozen.relative_to(self.root).as_posix().replace("/", "_")
        target = self.records / f"{stamp}-{encoded}"
        target.mkdir()
        data = (FIXTURES / fixture / "events.jsonl").read_bytes()
        if events is not None:
            data = b"".join(data.splitlines(keepends=True)[:events])
        (target / "events.jsonl").write_bytes(data)
        if summary and events is None:
            shutil.copyfile(FIXTURES / fixture / "summary.json", target / "summary.json")
        return target

    def test_empty_and_missing_paths(self):
        for run in (self.run, self.root / "missing"):
            with self.subTest(run=run):
                view = watch.Monitor(run, root=self.root).refresh()
                self.assertEqual((view.rows, view.workers, view.skipped), ({}, (), 0))
                self.assertIsNone(view.ledger)

    def test_auto_discovery_can_wait_for_a_campaign(self):
        empty = self.root / "empty"
        empty.mkdir()
        monitor = watch.Monitor(root=empty)
        self.assertIsNone(monitor.refresh().run)
        run = empty / ".skel" / "runs" / "20261121T210000Z-full"
        run.mkdir(parents=True)
        self.assertEqual(monitor.refresh().run, run)

    def test_auto_discovery_selects_latest_full_suffix_then_stays_pinned(self):
        os.utime(self.run, (1000, 1000))
        latest = self.campaign("20261121T193016Z-full-1")
        os.utime(latest, (2000, 2000))
        other = self.campaign("20261121T220000Z-discover")
        os.utime(other, (4000, 4000))
        monitor = watch.Monitor(root=self.root)
        self.assertEqual(monitor.refresh().run, latest)
        newer = self.campaign("20261121T230000Z-full")
        os.utime(newer, (5000, 5000))
        self.assertEqual(monitor.refresh().run, latest)

    def test_last_row_wins_and_other_functions_remain_distinct(self):
        self.write_rows(raw_row(status="open"), raw_row(fn="other"), raw_row())
        view = self.monitor().refresh()
        self.assertEqual(set(view.rows), {("workspaceSize", "block.entry"), ("other", "block.entry")})
        self.assertEqual(view.rows[("workspaceSize", "block.entry")].status, "closed")
        self.assertEqual(view.skipped, 0)

    def test_partial_final_json_waits_for_a_newline(self):
        encoded = line(raw_row())
        self.journal.write_text(encoded[:-4])
        monitor = self.monitor()
        self.assertEqual((monitor.refresh().rows, monitor.refresh().skipped), ({}, 0))
        with self.journal.open("a") as target:
            target.write(encoded[-4:-1])
        self.assertEqual(monitor.refresh().rows, {})
        with self.journal.open("a") as target:
            target.write("\n")
        view = monitor.refresh()
        self.assertEqual(len(view.rows), 1)
        self.assertEqual(view.skipped, 0)

    def test_malformed_complete_lines_are_counted_once(self):
        self.journal.write_text("{broken\nnull\n" + line({**raw_row(), "fn": 3}) + line(raw_row()))
        monitor = self.monitor()
        first = monitor.refresh()
        self.assertEqual((len(first.rows), first.skipped), (1, 3))
        self.assertEqual(monitor.refresh().skipped, 3)

    def test_journal_truncation_removes_old_rows_and_partial_tail(self):
        self.journal.write_text(line(raw_row(fn="longFunctionName")) + line(raw_row(fn="other")) + "{partial")
        monitor = self.monitor()
        self.assertEqual(len(monitor.refresh().rows), 2)
        self.write_rows(raw_row(fn="new"))
        view = monitor.refresh()
        self.assertEqual(set(view.rows), {("new", "block.entry")})
        self.assertEqual(view.skipped, 0)

    def test_atomic_journal_replacement_of_the_same_size_resets(self):
        self.write_rows(raw_row(fn="old"))
        monitor = self.monitor()
        self.assertIn(("old", "block.entry"), monitor.refresh().rows)
        replacement = self.run / "replacement.jsonl"
        replacement.write_text(line(raw_row(fn="new")))
        self.assertEqual(replacement.stat().st_size, self.journal.stat().st_size)
        os.replace(replacement, self.journal)
        self.assertEqual(set(monitor.refresh().rows), {("new", "block.entry")})

    def test_h1_acceptance_does_not_close_an_open_skel_row(self):
        self.write_rows(raw_row(status="open", detail="awaiting the row check"))
        record = self.record()
        view = self.monitor().refresh()
        self.assertEqual(view.rows[("workspaceSize", "block.entry")].status, "open")
        self.assertEqual(len(view.workers), 1)
        proof = view.workers[0]
        self.assertEqual((proof.path, proof.fn, proof.name, proof.outcome),
                         (record, "workspaceSize", "block.entry", "accepted"))
        self.assertEqual(len(proof.run.attempts), 2)
        self.assertTrue(proof.run.attempts[-1].verdict)

    def test_context_limit_is_read_before_reflection_without_skipping(self):
        record = self.record(events=2, summary=False)
        with (record / "events.jsonl").open("a") as target:
            target.write(line({"event": "context-limit", "reason": "input context threshold reached",
                               "iteration": 1, "estimated_input_tokens": 557056, "input_limit_tokens": 557056}))
        monitor = self.monitor()
        view = monitor.refresh()
        self.assertEqual(view.skipped, 0)
        self.assertEqual(view.workers[0].run.last, "context-limit")
        self.assertEqual(view.workers[0].run.attempts[-1].activity,
                         "context limit: input context threshold reached")
        self.assertEqual(monitor.refresh().skipped, 0)

    def test_checked_disproof_is_shown_without_closing_the_row(self):
        self.write_rows(raw_row(status="open", detail="blocked: a dependency is not closed"))
        record = self.record()
        summary = record / "summary.json"
        value = json.loads(summary.read_text())
        value["report"] = ("Accepted: Other.helper proved; "
                           "Skel.Gen.Level3.Shuffler.workspaceSize.block.entry disproved, "
                           "with the statements of the original and the standard axioms only.\n")
        summary.write_text(json.dumps(value))
        view = self.monitor().refresh()
        proof = view.workers[0]
        self.assertEqual(proof.result, "disproof")
        self.assertEqual(watch.proof_status(proof), "disproved")
        self.assertEqual(view.rows[("workspaceSize", "block.entry")].status, "open")
        text = "\n".join(item.text for item in watch.render(view, 180, 40))
        self.assertIn("1 disproved", text)
        self.assertIn("block.entry: disproved", text)

    def test_disproof_report_must_identify_the_checked_target(self):
        self.record()
        record = next(self.records.iterdir())
        for outcome, report in [
            ("accepted", "Accepted: Other.block.entry disproved, with the standard axioms only."),
            ("accepted", "Accepted: T.workspaceSize.other disproved, with the standard axioms only."),
            ("failed", "T.workspaceSize.block.entry disproved, with the standard axioms only."),
            ("accepted", "The prover says workspaceSize.block.entry is disproved."),
        ]:
            with self.subTest(outcome=outcome, report=report):
                (record / "summary.json").write_text(json.dumps({"outcome": outcome, "report": report}))
                proof = self.monitor().refresh().workers[0]
                self.assertNotEqual(proof.result, "disproof")

    def test_malformed_summary_does_not_hide_workers(self):
        record = self.record()
        for value in (None, [], "bad", {"outcome": "accepted", "report": []}):
            with self.subTest(value=value):
                (record / "summary.json").write_text(json.dumps(value))
                self.assertEqual(len(self.monitor().refresh().workers), 1)
                self.assertEqual(watch.summary_result(value, "f", "row"), "")

    def test_proof_result_header_uses_one_table_slot(self):
        proof = watch.Proof(self.root, "f", "row", result="disproof")
        plain = watch.View()
        failed = watch.View(workers=(proof,))
        self.assertEqual(watch.table_slots(failed, 40), watch.table_slots(plain, 40) - 1)

    def test_import_result_matches_exact_worker_record(self):
        self.write_rows(raw_row(status="open"))
        record = self.record()
        parent = self.run / "prove/workspaceSize/invocations/one"
        parent.mkdir(parents=True)
        result = parent / "result.json"
        reply = {"runDir": str(record), "result": "extraction-failure", "proof": None,
                 "why": "a helper has the word 'set_option'"}
        result.write_text(json.dumps({"row": "block.entry", "result": {"kind": "reply", "reply": reply}}))
        proof = self.monitor().refresh().workers[0]
        self.assertEqual(watch.proof_status(proof), "import rejected")
        self.assertIn("set_option", proof.detail)
        reply["runDir"] = str(record) + "-other"
        result.write_text(json.dumps({"row": "block.entry", "result": {"kind": "reply", "reply": reply}}))
        self.assertNotEqual(watch.proof_status(self.monitor().refresh().workers[0]), "import rejected")

    def test_malformed_import_results_do_not_hide_worker_records(self):
        self.record()
        parent = self.run / "prove/workspaceSize/invocations/one"
        parent.mkdir(parents=True)
        for value in (None, [], {}, {"result": []}, {"result": {"kind": "reply", "reply": []}}):
            with self.subTest(value=value):
                (parent / "result.json").write_text(json.dumps(value))
                self.assertEqual(len(self.monitor().refresh().workers), 1)

    def test_foreign_h1_records_are_ignored(self):
        foreign = self.campaign("20261121T170000Z-full")
        self.record(campaign=foreign)
        self.assertEqual(self.monitor().refresh().workers, ())

    def test_nonmatching_record_names_are_ignored(self):
        record = self.record()
        record.rename(record.with_name("prefix-" + record.name))
        self.assertEqual(self.monitor().refresh().workers, ())

    def test_retries_are_kept_as_separate_proof_records(self):
        first = self.record("rejected-thrice")
        second = self.record(stamp="2026-11-21T21-00-00.000000000")
        view = self.monitor().refresh()
        self.assertEqual({p.path for p in view.workers}, {first, second})
        self.assertEqual({p.outcome for p in view.workers}, {"iterations", "accepted"})

    def test_extra_model_link_is_associated_with_its_function(self):
        record = self.record(link="link1")
        (proof,) = self.monitor().refresh().workers
        self.assertEqual((proof.path, proof.fn, proof.name), (record, "workspaceSize", "block.entry"))

    def test_map_revision_worker_and_import_result_are_visible(self):
        record = self.record(link="revision-1/link1")
        parent = self.run / "prove/workspaceSize/revision-1/link1/invocations/one"
        parent.mkdir(parents=True)
        reply = {"runDir": str(record), "result": "extraction-failure", "proof": None,
                 "why": "fixture import rejection"}
        (parent / "result.json").write_text(json.dumps(
            {"row": "block.entry", "result": {"kind": "reply", "reply": reply}}))
        workers = self.monitor().refresh().workers
        self.assertEqual(len(workers), 1)
        proof = workers[0]
        self.assertEqual((proof.path, proof.fn, proof.name), (record, "workspaceSize", "block.entry"))
        self.assertEqual(watch.proof_status(proof), "import rejected")

    def test_partial_h1_record_reports_live_progress(self):
        record = self.record(events=13, summary=False)
        (proof,) = self.monitor().refresh().workers
        self.assertEqual((proof.path, proof.outcome), (record, ""))
        self.assertEqual(len(proof.run.attempts), 2)
        self.assertIsNone(proof.run.attempts[-1].verdict)
        self.assertEqual(proof.run.attempts[-1].replies, 1)

    def test_partial_h1_event_waits_for_its_newline(self):
        record = self.record(events=2, summary=False)
        data = (FIXTURES / "accepted-second" / "events.jsonl").read_bytes().splitlines(keepends=True)[2]
        monitor = self.monitor()
        self.assertEqual(monitor.refresh().workers[0].run.last, "iteration")
        with (record / "events.jsonl").open("ab") as target:
            target.write(data[:-1])
        view = monitor.refresh()
        self.assertEqual((view.workers[0].run.last, view.skipped), ("iteration", 0))
        with (record / "events.jsonl").open("ab") as target:
            target.write(b"\n")
        view = monitor.refresh()
        self.assertEqual((view.workers[0].run.last, view.skipped), ("request-attempt", 0))

    def test_oversized_complete_event_is_skipped_without_losing_later_events(self):
        record = self.record(events=0, summary=False)
        data = (FIXTURES / "accepted-second" / "events.jsonl").read_bytes()
        (record / "events.jsonl").write_bytes(b"x" * (watch.LIMIT + 1) + b"\n" + data)
        monitor = self.monitor()
        view = monitor.refresh()
        self.assertEqual((view.skipped, len(view.workers[0].run.attempts)), (1, 2))
        self.assertTrue(view.workers[0].run.attempts[-1].verdict)
        self.assertEqual(monitor.refresh().skipped, 1)

    def test_oversized_partial_event_is_counted_once_then_discarded_until_newline(self):
        record = self.record(events=0, summary=False)
        events = record / "events.jsonl"
        events.write_bytes(b"x" * (watch.LIMIT + 1))
        monitor = self.monitor()
        self.assertEqual(monitor.refresh().skipped, 1)
        with events.open("ab") as target:
            target.write(b"more partial data")
        self.assertEqual(monitor.refresh().skipped, 1)
        data = (FIXTURES / "accepted-second" / "events.jsonl").read_bytes().splitlines(keepends=True)
        with events.open("ab") as target:
            target.write(b"\n" + b"".join(data[:2]))
        view = monitor.refresh()
        self.assertEqual((view.skipped, len(view.workers[0].run.attempts)), (1, 1))
        self.assertEqual(view.workers[0].run.last, "iteration")

    def test_render_stays_within_small_terminal_dimensions(self):
        self.write_rows(raw_row(status="open", detail="first line\nsecond line"))
        self.record(events=13, summary=False)
        view = self.monitor().refresh()
        for width, height in ((0, 0), (0, 5), (1, 1), (10, 3), (80, 8), (140, 40)):
            for worker_view in (False, True):
                with self.subTest(width=width, height=height, worker_view=worker_view):
                    lines = watch.render(view, width, height, worker_view=worker_view)
                    self.assertLessEqual(len(lines), height)
                    self.assertTrue(all(terminal_watch.cell_width(item.text) <= width for item in lines))

    def test_stale_final_ledger_is_not_attached_to_a_new_campaign(self):
        self.write_rows(raw_row())
        out = self.root / "report"
        out.mkdir()
        ledger = out / "ledger.json"
        ledger.write_text(json.dumps({"obligations": [], "composition": {"state": "blocked"}}))
        os.utime(ledger, (1000, 1000))
        os.utime(self.run, (2000, 2000))
        os.utime(self.journal, (2100, 2100))
        monitor = self.monitor(out=out)
        self.assertIsNone(monitor.refresh().ledger)
        os.utime(ledger, (2200, 2200))
        self.assertEqual(monitor.refresh().ledger["composition"], {"state": "blocked"})

    def test_malformed_final_ledger_shapes_are_ignored(self):
        self.write_rows(raw_row())
        out = self.root / "report"
        out.mkdir()
        ledger = out / "ledger.json"
        updated = max(self.run.stat().st_mtime, self.journal.stat().st_mtime) + 10
        values = [[], None, {}, {"obligations": {}}, {"obligations": [1]},
                  {"obligations": [None]}, {"obligations": [], "composition": []},
                  {"obligations": [], "composition": None}]
        for value in values:
            with self.subTest(value=value):
                ledger.write_text(json.dumps(value))
                os.utime(ledger, (updated, updated))
                view = self.monitor(out=out).refresh()
                self.assertIsNone(view.ledger)
                watch.render(view, 140, 40)

    def test_refresh_does_not_write_or_start_a_process(self):
        self.write_rows(raw_row())
        self.record()
        before = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        with patch("subprocess.Popen", side_effect=AssertionError("the watcher must not start processes")):
            view = self.monitor().refresh()
        after = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        self.assertEqual(before, after)
        self.assertEqual(len(view.rows), 1)


class TerminalTests(unittest.TestCase):
    def frames(self, counts, sizes):
        views = [watch.View(workers=tuple(
            watch.Proof(Path(str(i)), "f", f"row{i}") for i in range(count)))
            for count in counts]
        monitor, screen = Mock(), Mock()
        monitor.refresh.side_effect = views
        screen.getmaxyx.side_effect = sizes
        screen.getch.side_effect = (watch.curses.KEY_END, -1, ord("q"))
        lines, frames = {}, []
        screen.erase.side_effect = lines.clear
        screen.addstr.side_effect = lambda row, _col, text, _style: lines.update({row: text})
        screen.refresh.side_effect = lambda: frames.append("\n".join(lines.values()))
        with patch.object(watch.curses, "curs_set"), \
                patch.object(terminal_watch, "make_styles", return_value=defaultdict(int)):
            watch.terminal(screen, monitor, 1, mode="workers")
        return frames

    def test_finished_jobs_fill_the_visible_worker_table(self):
        frames = self.frames((8, 8, 3), ((24, 160),) * 3)
        for i in range(3):
            self.assertIn(f"f/row{i}", frames[-1])
        self.assertNotIn("f/row3", frames[-1])
        self.assertIn(">f/row2", frames[-1])

    def test_larger_terminal_fills_the_visible_worker_table(self):
        frames = self.frames((8, 8, 8), ((20, 160), (20, 160), (40, 160)))
        for i in range(8):
            self.assertIn(f"f/row{i}", frames[-1])
        self.assertIn(">f/row7", frames[-1])

    def test_empty_single_and_full_pages_keep_selection_in_view(self):
        for count in (0, 1, 8):
            with self.subTest(count=count):
                frames = self.frames((8, 8, count), ((24, 160),) * 3)
                if count:
                    self.assertIn(f">f/row{count - 1}", frames[-1])
                    if count == 8:
                        self.assertNotIn("f/row0", frames[-1])
                else:
                    self.assertIn("Waiting for records.", frames[-1])
                    self.assertNotIn("f/row", frames[-1])


class BudgetTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.book = self.root / "budget.json"

    def write_book(self, value):
        self.book.write_text(json.dumps(value))

    def test_spend_and_each_live_reservation_are_counted(self):
        self.write_book({"spentUsd": 4.25, "reservations": [
            {"run": "one", "boundUsd": 0.75}, {"run": "two", "boundUsd": 1.5}]})
        path, spent, reserved, error = watch.read_book(self.book)
        self.assertEqual((path, spent, reserved, error), (str(self.book), 4.25, 2.25, ""))

    def test_absent_or_null_reservations_mean_no_live_calls(self):
        for value in ({"spentUsd": 0}, {"spentUsd": 0, "reservations": None}):
            with self.subTest(value=value):
                self.write_book(value)
                self.assertEqual(watch.read_book(self.book)[1:], (0, 0, ""))

    def test_missing_and_malformed_books_report_an_error(self):
        self.assertTrue(watch.read_book(self.book)[3])
        for text in ("{broken", "null", "[]", "{}"):
            with self.subTest(text=text):
                self.book.write_text(text)
                self.assertTrue(watch.read_book(self.book)[3])

    def test_invalid_amounts_do_not_produce_account_totals(self):
        values = [
            {"spentUsd": -1}, {"spentUsd": float("nan")}, {"spentUsd": float("inf")},
            {"spentUsd": "1"}, {"spentUsd": True}, {"spentUsd": 10 ** 400},
            {"spentUsd": 0, "reservations": {}},
            {"spentUsd": 0, "reservations": [{"boundUsd": float("nan")}]},
            {"spentUsd": 0, "reservations": [{"boundUsd": float("inf")}]},
            {"spentUsd": 0, "reservations": [{"boundUsd": "1"}]},
            {"spentUsd": 0, "reservations": [{"boundUsd": True}]},
            {"spentUsd": 0, "reservations": [{"boundUsd": -1}, {"boundUsd": 2}]},
        ]
        for value in values:
            with self.subTest(value=value):
                self.write_book(value)
                _, spent, reserved, error = watch.read_book(self.book)
                self.assertTrue(error)
                self.assertEqual((spent, reserved), (0, 0))

    def test_aliased_books_are_counted_once(self):
        self.write_book({"spentUsd": 4.25, "reservations": [{"boundUsd": 1.5}]})
        alias = self.root / "alias.json"
        alias.symlink_to(self.book)
        monitor = watch.Monitor(root=self.root, budgets=(self.book, alias, Path("budget.json")))
        self.assertEqual(len(monitor.refresh().books), 1)
        self.assertEqual(monitor.refresh().books[0][1:], (4.25, 1.5, ""))

    def test_one_bad_book_makes_combined_totals_unavailable(self):
        self.write_book({"spentUsd": 4.25})
        monitor = watch.Monitor(root=self.root, budgets=(self.book, self.root / "missing.json"))
        view = monitor.refresh()
        text = "\n".join(item.text for item in watch.render(view, 140, 40))
        self.assertIn("totals unavailable", text)
        self.assertNotIn("$4.250 spent", text)


if __name__ == "__main__":
    unittest.main()
