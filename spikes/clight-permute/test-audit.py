#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Exercise the actual dependency guard, including rejected source changes."""
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("audit", BASE / "audit-deps.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AuditTests(unittest.TestCase):
    def test_actual_vendor_tree(self):
        self.assertEqual(audit.audit(), 28)

    def test_nested_comments(self):
        text = "(* Require Compiler. (* nested *) *) Require Import Clight.\n"
        self.assertEqual(audit.imports(text, {"Clight"}), {"Clight"})

    def test_string_markers_cannot_hide_import(self):
        text = 'Definition a := "(*".\nRequire Import Compiler.\nDefinition b := "*)".\n'
        with self.assertRaisesRegex(ValueError, "unapproved CompCert dependency"):
            audit.imports(text, {"Clight"})
        self.assertEqual(audit.uncomment('"escaped ""(*"" quote"'),
                         '"escaped ""(*"" quote"')

    def test_standard_libraries(self):
        text = "From Coq Require Import Program.Wf.\nFrom Flocq Require Import Bits.\n"
        self.assertEqual(audit.imports(text, set()), set())

    def test_noncommercial_import(self):
        with self.assertRaisesRegex(ValueError, "unapproved CompCert dependency"):
            audit.imports("Require Import Compiler.\n", {"Clight"})

    def test_unknown_prefix(self):
        with self.assertRaisesRegex(ValueError, "unapproved import prefix"):
            audit.imports("From compiler Require Import Compiler.\n", {"Compiler"})

    def test_dynamic_code(self):
        for text in ('Load "compiler.v".\n', 'Declare ML Module "compiler".\n'):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "loads code"):
                audit.imports(text, set())

    def test_unrecognized_require(self):
        with self.assertRaisesRegex(ValueError, "unrecognized import"):
            audit.imports('Require "compiler".\n', set())

    def test_unclosed_comment(self):
        with self.assertRaisesRegex(ValueError, "unfinished Rocq comment"):
            audit.imports("(* unfinished", set())

    def test_source_tampering(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "compcert"
            shutil.copytree(BASE / "vendor/compcert", root)
            file = root / "cfrontend/Clight.v"
            file.write_text(file.read_text() + "\nRequire Import Compiler.\n")
            with self.assertRaisesRegex(ValueError, "source digest mismatch"):
                audit.audit(root)

    def test_added_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "compcert"
            shutil.copytree(BASE / "vendor/compcert", root)
            (root / "Compiler.v").write_text("")
            with self.assertRaisesRegex(ValueError, "source set differs"):
                audit.audit(root)

    def test_manifest_tampering(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "manifest"
            manifest.write_text((BASE / "vendor/compcert.sha256").read_text()
                                + "0" * 64 + "  Compiler.v\n")
            with self.assertRaisesRegex(ValueError, "license allowlist"):
                audit.audit(manifest=manifest)

    def test_actual_project(self):
        self.assertGreaterEqual(audit.audit_project(), 7)

    def test_project_imports(self):
        for text in ("Require Import Compiler.\n",
                     "From compcert Require Import Compiler.\n",
                     "From Legacy Require Import Compiler.\n",
                     "Load \"compiler.v\".\n",
                     "Declare ML Module \"compiler\".\n"):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "Permute.v").write_text(text)
                with self.assertRaises(ValueError):
                    audit.audit_project(root)

    def test_added_project_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Compiler.v").write_text("")
            with self.assertRaisesRegex(ValueError, "unapproved project modules"):
                audit.audit_project(root)

    def test_unexpected_compiled_dependency(self):
        for name in ("Compiler.vo", "cfrontend/Compiler.v", "bad/path/Clight.vo"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                file = root / name
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text("")
                with self.assertRaisesRegex(ValueError, "unexpected dependency build"):
                    audit.stage_dependencies(root)

    def test_dependency_build_symlink(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "common").symlink_to(BASE / "vendor/compcert/common", target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "unexpected dependency build path"):
                audit.stage_dependencies(root)

    def test_changed_source_invalidates_all_objects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertTrue(audit.stage_dependencies(root))
            objects = [root / "cfrontend/Clight.vo", root / "lib/Coqlib.vo"]
            for file in objects:
                file.write_text("cached object")
            self.assertFalse(audit.stage_dependencies(root))
            self.assertTrue(all(file.exists() for file in objects))
            (root / "cfrontend/Clight.v").write_text("changed source")
            self.assertTrue(audit.stage_dependencies(root))
            self.assertTrue(all(not file.exists() for file in objects))
            self.assertEqual((root / "cfrontend/Clight.v").read_bytes(),
                             (BASE / "vendor/compcert/cfrontend/Clight.v").read_bytes())


if __name__ == "__main__":
    unittest.main()
