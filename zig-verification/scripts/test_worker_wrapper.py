"""The review wrapper must select this package, even in another project shell."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class WorkerWrapper(unittest.TestCase):
    def test_foreign_root_and_search_paths_cannot_select_another_project(self):
        with tempfile.TemporaryDirectory() as directory:
            fake_lake = Path(directory) / "lake"
            fake_lake.write_text(f"#!{sys.executable}\n" +
                "import json,os,sys\n" +
                "print(json.dumps({'args':sys.argv[1:], 'cwd':os.getcwd(),\n" +
                "'root':os.environ.get('LEANTOOLS_ROOT'),\n" +
                "'loogle':os.environ.get('LEANTOOLS_LOOGLE'),\n" +
                "'path':os.environ.get('LEAN_PATH'),\n" +
                "'src':os.environ.get('LEAN_SRC_PATH')}))\n")
            fake_lake.chmod(0o755)
            env = dict(os.environ, LEANTOOLS_ROOT="/other/project",
                       LEANTOOLS_LOOGLE="/other/loogle", LEAN_PATH="/other/lib",
                       LEAN_SRC_PATH="/other/src")
            env["PATH"] = directory + os.pathsep + env["PATH"]
            result = subprocess.run([str(ROOT / "scripts/leantools"), "tools", "--json"],
                                    cwd=directory, env=env, text=True, capture_output=True,
                                    check=True, timeout=10)
            selected = json.loads(result.stdout)
            self.assertEqual(selected["root"], str(ROOT))
            self.assertEqual(selected["cwd"], str(ROOT))
            self.assertEqual(selected["loogle"], str(ROOT / "vendor/loogle/.lake/build/bin/loogle"))
            self.assertIsNone(selected["path"])
            self.assertIsNone(selected["src"])
            self.assertEqual(selected["args"], ["env", str(ROOT / "pkgs/leantools/.lake/build/bin/leantools"),
                                                "tools", "--json"])


if __name__ == "__main__":
    unittest.main()
