"""Test concurrent tool calls through the production daemon in a temporary project.

Run after ``lake build leantools``, with the project's Lean toolchain on PATH.
"""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import tempfile
import time
import unittest


BINARY = Path(__file__).resolve().parents[1] / ".lake/build/bin/leantools"


def descendants(pid):
    """Find the test daemon's children, including workers in separate sessions."""
    parents = {}
    for path in Path("/proc").iterdir():
        if not path.name.isdecimal():
            continue
        try:
            status = (path / "status").read_text().splitlines()
            parents[int(path.name)] = int(
                next(line for line in status if line.startswith("PPid:")).split()[1]
            )
        except (OSError, StopIteration):
            continue
    found = {pid}
    while True:
        expanded = found | {child for child, parent in parents.items() if parent in found}
        if expanded == found:
            return found
        found = expanded


class ParallelDaemon(unittest.TestCase):
    def setUp(self):
        self.fixture = tempfile.TemporaryDirectory(prefix="leantools-daemon-test-")
        self.addCleanup(self.fixture.cleanup)
        self.root = Path(self.fixture.name)
        (self.root / "lakefile.toml").write_text('name = "daemonFixture"\n')
        (self.root / "leantools.json").write_text(
            json.dumps({"checkSeconds": 2, "maxOpen": 40})
        )
        for i in range(8):
            (self.root / f"File{i}.lean").write_text(
                f"import Lean\ntheorem target{i} : True := by sorry\n"
            )
        self.log = (self.root / "daemon.log").open("w")
        self.addCleanup(self.log.close)
        self.process = subprocess.Popen(
            [str(BINARY), "daemon", "--root", str(self.root)],
            cwd=BINARY.parents[3],
            env={**os.environ, "LEAN_NUM_THREADS": "2"},
            stdin=subprocess.DEVNULL,
            stdout=self.log,
            stderr=self.log,
            start_new_session=True,
        )
        self.addCleanup(self.stop)
        info = self.root / ".leantools/daemon.json"
        deadline = time.monotonic() + 15
        while not info.exists() and self.process.poll() is None:
            self.assertLess(time.monotonic(), deadline, "daemon did not start")
            time.sleep(0.05)
        self.assertTrue(info.exists(), (self.root / "daemon.log").read_text())
        self.info = json.loads(info.read_text())

    def stop(self):
        for pid in sorted(descendants(self.process.pid), reverse=True):
            try:
                os.kill(pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        try:
            self.process.wait(timeout=3)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait()

    def call(self, tool, **args):
        request = {"token": self.info["token"], "tool": tool, "args": args}
        with socket.create_connection(("127.0.0.1", self.info["port"]), timeout=12) as client:
            client.sendall((json.dumps(request) + "\n").encode())
            chunks = []
            while chunk := client.recv(65536):
                chunks.append(chunk)
        return json.loads(b"".join(chunks))

    def batch(self, jobs):
        with ThreadPoolExecutor(max_workers=8) as pool:
            futures = [pool.submit(self.call, tool, **args) for tool, args in jobs]
            return [future.result() for future in futures]

    def test_parallel_initial_checks_and_tools(self):
        originals = self.batch(
            [("view_original_file", {"file": f"File{i}.lean"}) for i in range(8)]
        )
        for i, result in enumerate(originals):
            self.assertTrue(result["ok"], result["text"])
            self.assertIn(f"target{i}", result["text"])
            self.assertIn("⊢ True", result["text"])
        results = self.batch(
            [
                ("lean_run_scratch_code", {"file": f"File{i}.lean", "code": "#check Nat"})
                if i % 2 == 0
                else ("lean_file_outline", {"file": f"File{i}.lean"})
                for i in range(8)
            ]
        )
        for i, result in enumerate(results):
            self.assertTrue(result["ok"], result["text"])
            self.assertIn("Nat" if i % 2 == 0 else f"target{i}", result["text"])
        stopped = self.call("stop")
        self.assertTrue(stopped["ok"], stopped["text"])
        self.process.wait(timeout=3)
        self.assertFalse((self.root / ".leantools/daemon.json").exists())

    def test_parallel_timeouts(self):
        self.batch([("view_original_file", {"file": f"File{i}.lean"}) for i in range(8)])
        started = time.monotonic()
        results = self.batch(
            [
                ("lean_run_scratch_code", {"file": f"File{i}.lean", "code": "#eval IO.sleep 10000"})
                for i in range(8)
            ]
        )
        # Allow four seconds beyond the two-second check limit for transport and cleanup.
        self.assertLess(time.monotonic() - started, 6, "check timers waited for task pool slots")
        for result in results:
            self.assertFalse(result["ok"])
            self.assertIn("the check did not end in 2 s", result["text"])

    def test_timeout_and_failed_request_release_clients(self):
        results = self.batch(
            [
                ("lean_run_scratch_code", {"file": "File0.lean", "code": "#eval IO.sleep 10000"}),
                ("view_working_file", {"file": "Missing.lean"}),
            ]
            + [("view_original_file", {"file": f"File{i}.lean"}) for i in range(2, 8)]
        )
        self.assertFalse(results[0]["ok"])
        self.assertIn("the check did not end in 2 s", results[0]["text"])
        self.assertFalse(results[1]["ok"])
        self.assertIn("does not exist", results[1]["text"])
        for result in results[2:]:
            self.assertTrue(result["ok"], result["text"])
            self.assertIn("⊢ True", result["text"])
        recovered = self.call("lean_run_scratch_code", file="File0.lean", code="#check Nat")
        self.assertTrue(recovered["ok"], recovered["text"])
        self.assertIn("Nat", recovered["text"])


if __name__ == "__main__":
    unittest.main()
