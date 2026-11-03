# SPDX-License-Identifier: GPL-3.0-or-later
"""Reject KLEE runs which lose branches or terminate states without a return."""
from contextlib import closing
import sqlite3

COUNTERS = ("InhibitedForks", "TerminationEarly", "TerminationSolverError",
            "TerminationProgramError", "TerminationUserError", "TerminationExecutionError")


def check_exploration(directory, log):
    """Check statistics from the pinned KLEE version, without creating a file.

    This supplements the path counts, error files, source checks, and terminal
    completion markers. A completion marker alone covers only retained paths.
    """
    try:
        uri = (directory / "run.stats").resolve().as_uri() + "?mode=ro"
        with closing(sqlite3.connect(uri, uri=True)) as database:
            rows = database.execute("SELECT " + ",".join(COUNTERS) + " FROM stats").fetchall()
        if not rows:
            raise ValueError("empty KLEE statistics")
        if any(type(value) is not int or value < 0 for row in rows for value in row):
            raise ValueError("invalid KLEE statistics counter")
        counters = {name: max(row[index] for row in rows)
                    for index, name in enumerate(COUNTERS)}
    except (OSError, sqlite3.Error, ValueError) as error:
        return {"pass": False, "counters": {}, "error": str(error)}
    warnings = [line for line in log.splitlines() if "skipping fork" in line.lower()]
    return {"pass": not any(counters.values()) and not warnings,
            "counters": counters, "fork_warnings": warnings}
