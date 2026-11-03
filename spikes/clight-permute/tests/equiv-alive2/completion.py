# SPDX-License-Identifier: GPL-3.0-or-later
"""Require a completion marker in each terminal KLEE input witness."""
import io
import struct


def read_objects(data):
    stream = io.BytesIO(data)

    def read(size):
        value = stream.read(size)
        if len(value) != size:
            raise ValueError("truncated KTest")
        return value

    def word():
        return struct.unpack(">I", read(4))[0]

    def blob():
        return read(word())

    if read(5) != b"KTEST" or word() != 3:
        raise ValueError("unsupported KTest format")
    for _ in range(word()):
        blob()  # program arguments
    word()  # symbolic argument count
    word()  # symbolic argument length
    objects = [(blob().decode("utf-8"), blob()) for _ in range(word())]
    if stream.read(1):
        raise ValueError("trailing KTest data")
    return objects


def completion_error(data, input_name, input_bytes):
    objects = read_objects(data)
    expected = [(input_name, input_bytes), ("checks_completed", 1)]
    if [(name, len(value)) for name, value in objects] != expected:
        return "input domain or final completion marker differs"
    return None


def check_completions(directory, complete_paths, input_name, input_bytes):
    witnesses = sorted(directory.glob("*.ktest"))
    invalid = {}
    for path in witnesses:
        try:
            error = completion_error(path.read_bytes(), input_name, input_bytes)
        except (ValueError, UnicodeError) as exception:
            error = str(exception)
        if error is not None:
            invalid[path.name] = error
    return {"witnesses": len(witnesses), "invalid_witnesses": invalid,
            "pass": complete_paths > 0 and len(witnesses) == complete_paths and not invalid}
