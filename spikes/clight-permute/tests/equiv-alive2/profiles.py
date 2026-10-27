# SPDX-License-Identifier: GPL-3.0-or-later
"""Parse explicit value-sharing domains and name concrete permutations."""
import hashlib


def parse_value_groups(text, sizes):
    groups = tuple(int(x) for x in text.split(","))
    if sizes != [len(groups)]:
        raise ValueError("value groups require one matching length")
    if set(groups) != set(range(max(groups) + 1)) or min(groups) < 0:
        raise ValueError("value group numbers must start at zero with no gaps")
    return groups


def case_name(permutation):
    numbers = "-".join(map(str, permutation))
    if len(numbers) > 180:
        numbers = hashlib.sha256(numbers.encode("ascii")).hexdigest()
    return f"n{len(permutation)}-{numbers}"
