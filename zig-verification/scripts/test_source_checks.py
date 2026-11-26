"""Check missing and changed inputs at the package boundary."""

import argparse
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build
import check_source


class DependencyTests(unittest.TestCase):
    def test_lake_executable_prerequisites_are_built_first(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Main.lean").write_text("import Lean\n")
            (root / "Needed.lean").write_text("import Lean\n")
            (root / "lakefile.toml").write_text(
                'name = "Fixture"\n[[lean_lib]]\nname = "Needed"\n'
                '[[lean_exe]]\nname = "app"\nroot = "Main"\nneeds = ["Needed"]\n')
            with patch.object(build, "ROOT", root):
                self.assertEqual(build.ordered(["Main"]), ["Needed", "Main"])

    def test_unknown_lake_prerequisite_is_an_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Main.lean").write_text("import Lean\n")
            (root / "lakefile.toml").write_text(
                'name = "Fixture"\n[[lean_exe]]\nname = "app"\nroot = "Main"\nneeds = ["Missing"]\n')
            with patch.object(build, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "unknown prerequisite"):
                    build.ordered(["Main"])

    def test_build_timeout_has_a_positive_bound(self):
        self.assertEqual(build.positive_seconds("600"), 600)
        for value in ["0", "-1", "601"]:
            with self.assertRaises(argparse.ArgumentTypeError):
                build.positive_seconds(value)

    def test_shared_dependency_is_built_once_before_users(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "First.lean").write_text("import Shared\nimport Lean\n")
            (root / "Second.lean").write_text("import Shared\n")
            (root / "Shared.lean").write_text("import Std\nimport Init\nimport Lake.CLI.Error\nimport Std.Tactic.BVDecide\n")
            with patch.object(build, "ROOT", root):
                self.assertEqual(build.ordered(["First", "Second"]), ["Shared", "First", "Second"])

    def test_missing_module_is_an_error(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(build, "ROOT", Path(directory)):
                with self.assertRaisesRegex(ValueError, "missing source module"):
                    build.ordered(["Missing"])

    def test_import_cycle_is_an_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "First.lean").write_text("import Second\n")
            (root / "Second.lean").write_text("import First\n")
            with patch.object(build, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "import cycle"):
                    build.ordered(["First"])


class SourceChecks(unittest.TestCase):
    def setup_source(self, root):
        zig, asm = b"source\n", b"assembly\n"
        for name, data in [(check_source.ZIG_PATH, zig), (check_source.ASM_PATH, asm)]:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        (root / "Lift/Shuffler").mkdir(parents=True)
        (root / "Lift/Shuffler/Code.lean").write_text('def code := shufflerProgram("assembly\\n")\n')
        (root / "SOURCE-MANIFEST.json").write_text(json.dumps({"files": [
            {"path": check_source.ZIG_PATH, "sha256": check_source.digest(zig)},
            {"path": check_source.ASM_PATH, "sha256": check_source.digest(asm)}]}))

    def test_matching_source_is_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_source(root)
            check_source.check(root)

    def test_changed_zig_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_source(root)
            (root / check_source.ZIG_PATH).write_bytes(b"changed")
            with self.assertRaisesRegex(ValueError, "source hash differs"):
                check_source.check(root)

    def test_changed_embedded_assembly_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_source(root)
            (root / "Lift/Shuffler/Code.lean").write_text('def code := shufflerProgram("different")\n')
            with self.assertRaisesRegex(ValueError, "embedded Lean assembly differs"):
                check_source.check(root)

    def test_missing_required_submodule_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_source(root)
            with self.assertRaisesRegex(ValueError, "initialize the exact Zig source"):
                check_source.check(root, require_submodule=True)


if __name__ == "__main__":
    unittest.main()
