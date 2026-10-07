# SPDX-License-Identifier: GPL-3.0-or-later
import struct
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from completion import read_objects, completion_error, check_completions


def word(value):
    return struct.pack(">I", value)


def blob(value):
    return word(len(value)) + value


def ktest(objects):
    return (b"KTEST" + word(3) + word(0) + word(0) + word(0)
            + word(len(objects))
            + b"".join(blob(name.encode()) + blob(value) for name, value in objects))


class CompletionTests(unittest.TestCase):
    def test_accepts_input_followed_by_completion(self):
        objects = [("values", bytes(12)), ("checks_completed", bytes(1))]
        self.assertEqual(read_objects(ktest(objects)), objects)
        self.assertIsNone(completion_error(ktest(objects), "values", 12))

    def test_rejects_early_exit(self):
        self.assertIsNotNone(completion_error(ktest([("values", bytes(12))]), "values", 12))

    def test_rejects_wrong_input_domain(self):
        data = ktest([("symbols", bytes(8)), ("checks_completed", bytes(1))])
        self.assertIsNotNone(completion_error(data, "values", 12))

    def test_rejects_duplicate_or_early_marker(self):
        marker = ("checks_completed", bytes(1))
        for objects in [[marker, ("values", bytes(12))],
                        [("values", bytes(12)), marker, marker]]:
            self.assertIsNotNone(completion_error(ktest(objects), "values", 12))

    def test_rejects_bad_encoding(self):
        valid = ktest([("values", bytes(12)), ("checks_completed", bytes(1))])
        for data in [b"", valid[:-1], valid + b"x", valid.replace(word(3), word(9), 1)]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                read_objects(data)

    def test_requires_one_witness_per_completed_path(self):
        data = ktest([("values", bytes(12)), ("checks_completed", bytes(1))])
        with TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "test000001.ktest").write_bytes(data)
            self.assertTrue(check_completions(path, 1, "values", 12)["pass"])
            self.assertFalse(check_completions(path, 2, "values", 12)["pass"])
            self.assertFalse(check_completions(path, 0, "values", 12)["pass"])

    def test_reports_corrupt_witness(self):
        with TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "test000001.ktest").write_bytes(b"KTEST")
            result = check_completions(path, 1, "values", 12)
            self.assertFalse(result["pass"])
            self.assertIn("test000001.ktest", result["invalid_witnesses"])


if __name__ == "__main__":
    unittest.main()
