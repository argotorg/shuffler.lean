#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the production coverage manifest against stale inputs and binaries."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("coverage_manifest", HERE / "coverage-manifest.py")
manifest = importlib.util.module_from_spec(spec)
spec.loader.exec_module(manifest)


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / "input.c"
        self.source.write_text("original source")
        self.binary = self.root / "coverage-program"
        self.binary.write_bytes(b"original binary")
        self.inputs = [self.source]
        self.record = manifest.capture(self.inputs, self.binary)

    def test_current_inputs(self):
        manifest.check(self.record, self.inputs, self.binary)

    def test_changed_source(self):
        self.source.write_text("changed source")
        with self.assertRaises(ValueError):
            manifest.check(self.record, self.inputs, self.binary)

    def test_changed_binary(self):
        self.binary.write_bytes(b"changed binary")
        with self.assertRaises(ValueError):
            manifest.check(self.record, self.inputs, self.binary)

    def test_changed_input_set(self):
        extra = self.root / "header.h"
        extra.write_text("new dependency")
        for inputs in ([], self.inputs + [extra]):
            with self.subTest(inputs=inputs), self.assertRaises(ValueError):
                manifest.check(self.record, inputs, self.binary)

    def test_missing_file(self):
        self.source.unlink()
        with self.assertRaises(OSError):
            manifest.check(self.record, self.inputs, self.binary)

    def test_wrong_binary_path(self):
        other = self.root / "other-program"
        other.write_bytes(self.binary.read_bytes())
        with self.assertRaises(ValueError):
            manifest.check(self.record, self.inputs, other)

    def test_invalid_records(self):
        for record in ({}, [], None, {**self.record, "extra": True},
                       {**self.record, "binary": {}}):
            with self.subTest(record=record), self.assertRaises(ValueError):
                manifest.check(record, self.inputs, self.binary)

    def test_source_change_during_build(self):
        before = manifest.hashes(self.inputs)
        self.source.write_text("changed during build")
        with self.assertRaises(ValueError):
            manifest.finish(before, self.inputs, self.binary)


class CoverageScriptTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name) / "repo/spikes/clight-permute"
        self.build = self.root / "build/guided"
        sources = manifest.inputs(self.root, self.build)
        for path in sources:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("build input\n")
        for name in ("coverage-manifest.py", "guided-coverage.sh"):
            shutil.copyfile(HERE / name, self.root / "tests" / name)
        self.binary = self.build / "coverage/permute-fuzz"
        self.binary.parent.mkdir()
        self.binary.write_text("#!/bin/sh\nexit 99\n")
        self.binary.chmod(0o755)
        self.record = self.build / "coverage-manifest.json"
        self.record.write_text(json.dumps(manifest.capture(sources, self.binary)))
        self.environment = {**os.environ,
                            "PATH": str(Path(sys.executable).parent) + os.pathsep + os.environ["PATH"]}

    def rejected_before_replay(self, message):
        run = subprocess.run(["sh", str(self.root / "tests/guided-coverage.sh"), str(self.build)],
                             capture_output=True, text=True, env=self.environment)
        self.assertNotEqual(run.returncode, 0)
        self.assertIn(message, run.stderr)
        self.assertEqual(list(self.build.glob("report.*")), [])

    def test_stale_source_stops_report(self):
        (self.root / "permute.c").write_text("changed source\n")
        self.rejected_before_replay("coverage source/binary manifest differs")

    def test_stale_binary_stops_report(self):
        self.binary.write_text("changed binary\n")
        self.rejected_before_replay("coverage source/binary manifest differs")

    def test_invalidated_build_stops_report(self):
        subprocess.run([sys.executable, str(self.root / "tests/coverage-manifest.py"),
                        "clear", str(self.build)], check=True)
        self.assertFalse(self.record.exists())
        self.rejected_before_replay("coverage-manifest.json")


if __name__ == "__main__":
    unittest.main()
