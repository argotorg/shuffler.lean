"""Exercise the compiler and the axiom gate used by Review.Closed."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class ContractGateTests(unittest.TestCase):
    def compile(self, source):
        environment = dict(os.environ, LEAN_NUM_THREADS="2")
        environment.pop("LEAN_PATH", None)
        with tempfile.TemporaryDirectory(prefix="contract-gate-") as directory:
            path = Path(directory) / "Gate.lean"
            path.write_text(source)
            return subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                  env=environment, capture_output=True, text=True, timeout=120)

    def reject(self, source, reason):
        result = self.compile(source)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(reason, result.stdout + result.stderr)

    def test_hole_is_rejected(self):
        self.reject("import LeanTools.Axioms\ntheorem unfinished : True := by sorry\n"
                    "#gate_axioms unfinished\n", "sorryAx")

    def test_user_axiom_is_rejected(self):
        self.reject("import LeanTools.Axioms\naxiom assumption : False\n"
                    "theorem result : False := assumption\n#gate_axioms result\n", "depends on assumption")

    def test_forged_certificate_axiom_is_rejected(self):
        self.reject("import LeanTools.Axioms\naxiom forged._native.bv_decide.ax_0_0 : False\n"
                    "theorem result : False := forged._native.bv_decide.ax_0_0\n#gate_axioms result\n",
                    "not a claim")

    def test_open_hypothesis_cannot_fill_a_closed_contract(self):
        self.reject("import LeanTools.Axioms\ntheorem conditional (h : False) : False := h\n"
                    "theorem closed : False := conditional\n", "Type mismatch")

    def test_closed_proof_is_accepted(self):
        result = self.compile("import LeanTools.Axioms\ntheorem closed : True := True.intro\n"
                              "#gate_axioms closed\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
