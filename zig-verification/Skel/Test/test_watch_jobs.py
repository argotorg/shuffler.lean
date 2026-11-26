"""Live model jobs come from matching local processes, not budget reservations."""
import json
from pathlib import Path
import tempfile
import unittest

from Skel import watch, watch_jobs


class JobTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.proc = self.root / "proc"
        self.proc.mkdir()
        (self.proc / "uptime").write_text("200 100\n")
        self.run = self.root / "run"
        self.run.mkdir()
        self.out = self.root / "out"
        self.process(10, 1, [".lake/build/bin/skel", "full", "--out", "out",
                             "--procs", "3", "--ask-parallel", "8"])
        self.prompt = self.root / "prompt"
        self.prompt.write_text("You propose loop triples for a proof.\n"
                               "SysV.ExecRange p Lift.Ex.codePC Lift.Ex.endPC\n"
                               "Lift.Ex.workerPC\n## Slot statement\n"
                               "blocksP.Returns noCall .LBB1_2 state result\n## Reply format\n")
        self.config = self.root / "ask.json"
        self.config.write_text(json.dumps({"model": "model-test", "apiKey": "must-not-appear"}))

    def process(self, pid, parent, args, state="S", cwd=None):
        directory = self.proc / str(pid)
        directory.mkdir(exist_ok=True)
        (directory / "cmdline").write_bytes(b"\0".join(a.encode() for a in args) + b"\0")
        # Field 22 is starttime, in clock ticks. The command can contain spaces and ')'.
        fields = [state, str(parent)] + ["0"] * 17 + ["100"]
        (directory / "stat").write_text(f"{pid} (a command ) name) " + " ".join(fields))
        link = directory / "cwd"
        if link.is_symlink(): link.unlink()
        link.symlink_to(cwd or self.root)

    def ask(self, pid=11, parent=10):
        self.process(pid, parent, ["leantools", "ask", "--config", "ask.json",
                                  "--budget", "private-book", "--max-usd", "0.15", str(self.prompt)])

    def read(self):
        return watch_jobs.read_jobs(self.root, self.run, self.out, self.proc)

    def test_running_asks_are_named_and_share_the_proof_limit(self):
        self.ask()
        self.process(12, 10, ["leantools", "prove", str(self.run / "prove/f/row.lean"), "--config", "prove.json"])
        jobs = self.read()
        self.assertEqual((jobs.pid, jobs.limit, jobs.procs, jobs.proofs), (10, 8, 3, 1))
        (ask,) = jobs.asks
        self.assertEqual((ask.pid, ask.fn, ask.name, ask.model, ask.kind),
                         (11, "worker", "loop.LBB1_2", "model-test", "loop proposal"))
        self.assertGreaterEqual(ask.elapsed, 0)
        self.assertNotIn("must-not-appear", repr(jobs))

    def test_foreign_jobs_zombies_and_foreign_roots_are_ignored(self):
        self.ask(parent=99)
        self.ask(pid=12)
        (self.proc / "12/stat").write_text((self.proc / "12/stat").read_text().replace(" S ", " Z "))
        self.assertEqual(self.read().asks, ())
        self.process(10, 1, ["skel", "full", "--out", "out"], cwd=self.root / "elsewhere")
        self.assertIsNone(self.read().pid)

    def test_same_output_from_two_campaigns_is_ambiguous(self):
        self.ask()
        self.process(20, 1, ["skel", "full", "--out", "out"])
        self.assertIsNone(self.read().pid)
        self.assertEqual(self.read().asks, ())

    def test_missing_prompt_config_and_process_races_do_not_break_view(self):
        self.ask()
        self.prompt.unlink()
        self.config.write_text("{broken")
        (ask,) = self.read().asks
        self.assertEqual((ask.fn, ask.name, ask.model), ("unknown", "proposal", ""))
        (self.proc / "11/stat").unlink()
        self.assertEqual(self.read().asks, ())

    def test_without_out_a_matching_proof_child_identifies_campaign(self):
        self.ask()
        self.process(12, 10, ["leantools", "prove", str(self.run / "prove/f/row.lean")])
        jobs = watch_jobs.read_jobs(self.root, self.run, None, self.proc)
        self.assertEqual((jobs.pid, len(jobs.asks)), (10, 1))

    def test_monitor_and_terminal_show_asks(self):
        self.ask()
        view = watch.Monitor(self.run, root=self.root, out=self.out, proc_root=self.proc).refresh()
        self.assertEqual(len(view.asks), 1)
        text = "\n".join(x.text for x in watch.render(view, 160, 40, worker_view=True))
        self.assertIn("worker/loop.LBB1_2", text)
        self.assertIn("ask", text)
        self.assertIn("1 ask", text)
        self.assertIn("/ 8", text)

    def test_non_linux_host_is_supported(self):
        self.assertIsNone(watch_jobs.read_jobs(self.root, self.run, self.out, self.root / "missing").pid)

    def test_entry_identifies_function_without_a_range_declaration(self):
        self.prompt.write_text("You propose loop triples for a proof.\n"
                               "SysV.Entry p Lift.Ex.lowPC Lift.Ex.highPC Lift.Ex.targetPC s\n"
                               "## Slot statement\nblocksP.Returns noCall .head s r\n")
        self.ask()
        (ask,) = self.read().asks
        self.assertEqual((ask.fn, ask.name), ("target", "loop.head"))
        self.prompt.write_text(self.prompt.read_text() +
                               "SysV.Entry p Lift.Ex.lowPC Lift.Ex.highPC Lift.Ex.otherPC s\n")
        self.assertEqual(self.read().asks[0].fn, "unknown")

    def test_campaign_metadata_identifies_asks_before_first_proof(self):
        self.ask()
        (self.run / "campaign.json").write_text(json.dumps({"pid": 10, "out": "out"}))
        jobs = watch_jobs.read_jobs(self.root, self.run, None, self.proc)
        self.assertEqual((jobs.pid, len(jobs.asks)), (10, 1))
        (self.run / "campaign.json").write_text(json.dumps({"pid": 99, "out": "out"}))
        self.assertIsNone(watch_jobs.read_jobs(self.root, self.run, None, self.proc).pid)

    def test_metadata_supports_default_output_without_a_command_flag(self):
        self.process(10, 1, ["skel", "full", "--ask-parallel", "8"])
        self.ask()
        (self.run / "campaign.json").write_text(json.dumps({"pid": 10, "out": "default-report"}))
        jobs = watch_jobs.read_jobs(self.root, self.run, None, self.proc)
        self.assertEqual((jobs.pid, len(jobs.asks)), (10, 1))


if __name__ == "__main__":
    unittest.main()
