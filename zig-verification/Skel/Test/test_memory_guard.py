"""Test the production memory guard without sending process signals."""
from dataclasses import replace
import json
from pathlib import Path
import signal
import tempfile
import unittest
from unittest.mock import patch

from Skel import memory_guard as guard


class GuardTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.proc = self.root / "proc"
        self.proc.mkdir()
        self.limits = guard.Limits()
        self.campaign = guard.Identity(10, 100)
        self.daemon = guard.Identity(20, 100)

    def process(self, pid, parent, name="lean", rss=1, start=101, args=(), cwd=None):
        return guard.Process(guard.Identity(pid, start), parent, name,
                             cwd or self.root, rss * guard.GIB, tuple(args))

    def snapshot(self, workers=()):
        return (self.process(10, 1, "skel", start=100, args=("skel", "full")),
                self.process(20, 1, "leantools", start=100,
                             args=("leantools", "daemon", "--root", str(self.root))),
                *workers)

    def choose(self, workers=(), available=30, pressure=False, attempted=frozenset()):
        return guard.select_victim(self.snapshot(workers), self.root,
                                   (self.campaign, self.daemon),
                                   None if available is None else available * guard.GIB,
                                   self.limits, pressure, attempted)

    def test_low_pressure_does_not_kill(self):
        decision = self.choose((self.process(30, 20, rss=8),))
        self.assertIsNone(decision.victim)
        self.assertFalse(decision.pressure)

    def test_cap_is_strict_and_largest_worker_is_selected(self):
        decision = self.choose((self.process(30, 20, rss=9), self.process(31, 10, rss=12)))
        self.assertEqual(decision.victim.identity.pid, 31)
        self.assertEqual(decision.reason, "rss-cap")

    def test_pressure_starts_below_floor_and_stops_at_recovery(self):
        worker = self.process(30, 20)
        self.assertIsNone(self.choose((worker,), available=20).victim)
        self.assertTrue(self.choose((worker,), available=19).pressure)
        self.assertTrue(self.choose((worker,), available=23, pressure=True).pressure)
        self.assertFalse(self.choose((worker,), available=24, pressure=True).pressure)
        self.assertEqual(self.choose((worker,), available=19).reason, "available-floor")

    def test_unrelated_model_and_server_processes_are_never_selected(self):
        workers = (self.process(30, 99, rss=50),
                   self.process(31, 20, rss=50, cwd=self.root / "foreign"),
                   self.process(32, 10, "leantools", rss=50, args=("leantools", "prove")),
                   self.process(33, 10, "leantools", rss=50, args=("leantools", "ask")),
                   self.process(34, 20, rss=50, args=("lean", "--server")))
        self.assertIsNone(self.choose(workers, available=1).victim)

    def test_workers_and_validators_in_both_trees_are_eligible(self):
        workers = (self.process(30, 20, "lake"), self.process(31, 30, "lean-worker", rss=9),
                   self.process(32, 10, "leantools", rss=10, args=("leantools", "validate", "a", "b")))
        self.assertEqual({p.identity.pid for p in guard.eligible_processes(
            self.snapshot(workers), self.root, (self.campaign, self.daemon))}, {31, 32})

    def test_pid_reuse_does_not_retain_old_root_or_old_attempt(self):
        workers = (self.process(30, 10, rss=9),)
        self.assertEqual(guard.eligible_processes(self.snapshot(workers), self.root,
                                               (guard.Identity(10, 99),)), ())
        self.assertIsNone(self.choose(workers, attempted=frozenset({guard.Identity(30, 101)})).victim)
        self.assertIsNotNone(self.choose(workers, attempted=frozenset({guard.Identity(30, 100)})).victim)

    def test_reused_parent_younger_than_child_is_not_an_ancestor(self):
        workers = (self.process(30, 20, "lake", start=105),
                   self.process(31, 30, rss=10, start=104))
        self.assertIsNone(self.choose(workers).victim)

    def test_missing_meminfo_does_not_create_pressure_but_cap_remains(self):
        self.assertIsNone(self.choose((self.process(30, 20),), available=None).victim)
        self.assertIsNotNone(self.choose((self.process(30, 20, rss=9),), available=None).victim)

    def fake_process(self, pid=30, state="S", start=101, rss=4096, args=("lean",), cwd=None):
        directory = self.proc / str(pid)
        directory.mkdir(exist_ok=True)
        fields = [state, "20"] + ["0"] * 17 + [str(start), "0", str(rss)]
        (directory / "stat").write_text(f"{pid} (name with ) spaces) " + " ".join(fields))
        (directory / "cmdline").write_bytes(b"\0".join(a.encode() for a in args) + b"\0")
        (directory / "exe").symlink_to("/bin/" + Path(args[0]).name)
        (directory / "cwd").symlink_to(cwd or self.root)
        return directory

    def test_proc_reader_uses_starttime_and_rss_and_handles_parentheses(self):
        path = self.fake_process()
        p = guard.read_process(path, page_size=4096)
        self.assertEqual((p.identity, p.parent, p.rss, p.name),
                         (guard.Identity(30, 101), 20, 4096 * 4096, "lean"))

    def test_replaced_executable_keeps_its_original_name(self):
        path = self.fake_process(args=("skel", "full"))
        (path / "exe").unlink()
        (path / "exe").symlink_to("/build/skel (deleted)")
        process = guard.read_process(path)
        self.assertEqual(process.name, "skel")
        self.assertTrue(guard.command(process, "skel", "full"))
        (path / "exe").unlink()
        (path / "exe").symlink_to("/build/lean-worker (deleted)")
        self.assertTrue(guard.elaborator(guard.read_process(path)))

    def test_proc_reader_excludes_zombies_missing_and_malformed_processes(self):
        self.assertIsNone(guard.read_process(self.fake_process(state="Z")))
        self.assertIsNone(guard.read_process(self.proc / "99"))
        (self.proc / "30/stat").write_text("bad")
        self.assertIsNone(guard.read_process(self.proc / "30"))

    def test_missing_proc_and_meminfo_are_supported(self):
        self.assertEqual(guard.read_processes(self.root / "missing"), ())
        self.assertIsNone(guard.read_available(self.proc))
        (self.proc / "meminfo").write_text("MemFree: 1 kB\nMemAvailable: 123 kB\n")
        self.assertEqual(guard.read_available(self.proc), 123 * 1024)

    def test_daemon_metadata_requires_correct_process_identity_and_root(self):
        metadata = self.root / ".leantools" / "daemon.json"
        metadata.parent.mkdir()
        self.assertIsNone(guard.daemon_identity(self.root, self.snapshot()))
        metadata.write_text(json.dumps({"pid": 20, "token": "do-not-log"}))
        self.assertEqual(guard.daemon_identity(self.root, self.snapshot()), self.daemon)
        processes = tuple(replace(p, cwd=self.root / "foreign") for p in self.snapshot())
        self.assertIsNone(guard.daemon_identity(self.root, processes))
        metadata.write_text("broken")
        self.assertIsNone(guard.daemon_identity(self.root, self.snapshot()))

    def test_pidfd_signal_checks_identity_after_open(self):
        self.fake_process()
        with patch.object(guard.os, "pidfd_open", return_value=99), \
             patch.object(guard.os, "close") as close, \
             patch.object(guard.signal, "pidfd_send_signal") as send:
            self.assertEqual(guard.signal_process(guard.Identity(30, 101), signal.SIGTERM, self.proc), "sent")
            send.assert_called_once_with(99, signal.SIGTERM)
            close.assert_called_once_with(99)

    def test_pidfd_signal_rejects_pid_reuse_and_missing_process(self):
        self.fake_process()
        with patch.object(guard.os, "pidfd_open", return_value=99), \
             patch.object(guard.os, "close"), \
             patch.object(guard.signal, "pidfd_send_signal") as send:
            self.assertEqual(guard.signal_process(guard.Identity(30, 100), signal.SIGKILL, self.proc), "gone")
            send.assert_not_called()

    def test_fallback_checks_identity_before_signal(self):
        self.fake_process()
        with patch.object(guard.os, "pidfd_open", side_effect=OSError(38, "not supported")), \
             patch.object(guard.os, "kill") as send:
            self.assertEqual(guard.signal_process(guard.Identity(30, 100), signal.SIGTERM, self.proc), "gone")
            send.assert_not_called()
            self.assertEqual(guard.signal_process(guard.Identity(30, 101), signal.SIGTERM, self.proc), "sent")
            send.assert_called_once_with(30, signal.SIGTERM)

    def test_signal_rechecks_worker_kind_and_cwd(self):
        self.fake_process(args=("leantools", "prove", "private-path"))
        with patch.object(guard.os, "pidfd_open", return_value=99), \
             patch.object(guard.os, "close"), \
             patch.object(guard.signal, "pidfd_send_signal") as send:
            self.assertEqual(guard.signal_process(guard.Identity(30, 101), signal.SIGTERM,
                                                 self.proc, self.root), "out-of-scope")
            send.assert_not_called()

    def test_cycle_and_missing_parent_are_not_eligible(self):
        workers = (self.process(30, 31, rss=10), self.process(31, 30, rss=9))
        self.assertIsNone(self.choose(workers).victim)

    def test_snapshot_contains_no_arguments_or_secrets(self):
        worker = self.process(30, 20, rss=10, args=("lean", "credential-must-stay-private"))
        text = json.dumps(guard.decision_record(self.choose((worker,)), 10 * guard.GIB))
        self.assertIn('"pid": 30', text)
        self.assertIn('"rssBytes":', text)
        self.assertNotIn("credential", text)
        self.assertNotIn("credential", repr(worker))

    def test_invalid_limits_are_rejected(self):
        with patch("sys.stderr"):
            for args in (("--rss-gib", "0"), ("--interval", "nan"),
                         ("--recovery-gib", "19"), ("--floor-gib", "inf")):
                with self.assertRaises(SystemExit) as stopped:
                    guard.main(["--root", str(self.root), "--once", *args])
                self.assertEqual(stopped.exception.code, 2)

    def test_once_is_report_only_and_does_not_write_state(self):
        self.fake_process()
        with patch.object(guard, "signal_process") as send, patch("builtins.print"):
            self.assertEqual(guard.main(["--root", str(self.root), "--once", "--proc-root", str(self.proc)]), 0)
        send.assert_not_called()
        self.assertFalse((self.root / ".skel").exists())

    def test_live_loop_waits_escalates_once_and_tracks_supervisor(self):
        metadata = self.root / ".leantools" / "daemon.json"
        metadata.parent.mkdir()
        metadata.write_text(json.dumps({"pid": 20}))
        workers = (self.process(30, 20, rss=10), self.process(31, 10, rss=9))
        snapshot = self.snapshot(workers)
        log = self.root / "guard.jsonl"
        own = self.process(99, 1, "python3")
        # Two pending cycles cannot select a second worker. A still-live target
        # gets one KILL, then stays excluded even if /proc still lists it.
        reads = [snapshot, snapshot, snapshot, snapshot, snapshot, ()]
        with patch.object(guard, "read_processes", side_effect=reads), \
             patch.object(guard, "read_process", return_value=own), \
             patch.object(guard, "read_available", return_value=30 * guard.GIB), \
             patch.object(guard, "signal_process", return_value="sent") as send, \
             patch.object(guard.signal, "signal", return_value=signal.SIG_DFL), \
             patch.object(guard.time, "monotonic", side_effect=[0, 0.1, 0.6, 1]), \
             patch.object(guard.time, "sleep"):
            self.assertEqual(guard.main(["--root", str(self.root), "--campaign", "10",
                                         "--log", str(log)]), 0)
        self.assertEqual([(call.args[0].pid, call.args[1]) for call in send.call_args_list],
                         [(30, signal.SIGTERM), (30, signal.SIGKILL), (31, signal.SIGTERM)])
        saved = json.loads(Path(str(log) + ".state.json").read_text())
        self.assertEqual((saved["state"], saved["campaign"], saved["campaignStart"]),
                         ("stopped", 10, 100))
        self.assertEqual([json.loads(line)["event"] for line in log.read_text().splitlines()],
                         ["start", "term", "kill", "term", "stop"])

    def test_campaign_pid_reuse_ends_loop_without_signals(self):
        snapshot = self.snapshot((self.process(30, 10, rss=10),))
        reused = tuple(replace(p, identity=guard.Identity(10, 110))
                       if p.identity.pid == 10 else p for p in snapshot)
        with patch.object(guard, "read_processes", side_effect=[snapshot, reused]), \
             patch.object(guard, "read_process", return_value=self.process(99, 1, "python3")), \
             patch.object(guard, "signal_process") as send, \
             patch.object(guard.signal, "signal", return_value=signal.SIG_DFL):
            self.assertEqual(guard.main(["--root", str(self.root), "--campaign", "10",
                                         "--log", str(self.root / "guard.jsonl")]), 0)
        send.assert_not_called()


if __name__ == "__main__":
    unittest.main()
