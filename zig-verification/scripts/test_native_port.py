"""Check source provenance in the production native harness without compiling Zig."""

import importlib.util
import hashlib
import json
import os
from pathlib import Path
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


def load():
    spec = importlib.util.spec_from_file_location("native_review", ROOT / "tools/shuffler-harness/native.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class NativePortTests(unittest.TestCase):
    def test_default_uses_path(self):
        with patch.dict(os.environ, {}, clear=True):
            self.assertEqual(load().ZIG, "zig")

    def test_compiler_override(self):
        with patch.dict(os.environ, {"ZIG": "/custom/zig"}):
            self.assertEqual(load().ZIG, "/custom/zig")

    def test_wrong_compiler_version_stops_before_compilation(self):
        module = load()
        with patch.object(module.subprocess, "check_output", return_value="0.18.0\n"), \
                patch.object(module.subprocess, "run") as compile_command:
            with self.assertRaisesRegex(RuntimeError, "Zig 0.17.1 is required"):
                module.build()
            compile_command.assert_not_called()

    def test_header_records_solidity_commit(self):
        module = load()
        manifest = json.loads((ROOT / "SOURCE-MANIFEST.json").read_text())
        header = module.header(types.SimpleNamespace(asm_sha="assembly"), "case.jsonl", 0, {})
        self.assertEqual(header["zig_commit"], manifest["soliditySource"]["commit"])
        self.assertEqual(header["zig_sha256"], manifest["soliditySource"]["sha256"])

    def test_missing_manifest_fails(self):
        module = load()
        with patch.object(module, "ROOT", str(ROOT / "absent")):
            with self.assertRaises(FileNotFoundError):
                module.header(types.SimpleNamespace(asm_sha="assembly"), "case.jsonl", 0, {})

    def test_fixture_cases_are_unchanged(self):
        expected = {
            "native-boundary.jsonl": "ae4274fdc830d860f7b7e1e0f6a7bd1b4bfd1f61f9ed47ef94998485e74d3b7b",
            "native-random.jsonl": "681c8bf3a4cac05c271de31442c026dbc90e7ed0fade6731d5f3b13b9aeb088f",
            "native-status2.jsonl": "93befde8c8091ba2278c7e1a969c714c6d68901b2469bef1aeffbe8ec1778403",
            "native-big.jsonl": "575c988806326a6e89e7cf5b86b5738502a29634cd19b11baeec91840b2b8457",
        }
        for name, digest in expected.items():
            data = (ROOT / "Lift/Shuffler/Test/data" / name).read_bytes().split(b"\n", 1)[1]
            self.assertEqual(hashlib.sha256(data).hexdigest(), digest)


if __name__ == "__main__":
    unittest.main()
