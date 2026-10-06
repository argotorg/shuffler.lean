#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Report every exported true/false outcome in two selected source files.

LLVM 21's CoverageExporterJson.cpp specifies the nine branch fields used
below. File records include lambdas; expansion records contain nested macro
branches. Count both. Show LLVM's summary and all exported outcomes as
separate measures. Do not filter either by reachability. Inline library/helper functions in other files are
outside this report; macros invoked in a selected file remain inside it.
Reference: https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/llvm/tools/llvm-cov/CoverageExporterJson.cpp
"""
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys


@dataclass(frozen=True)
class Branch:
    location: str
    true_count: int
    false_count: int
    expansion: str = ""


@dataclass(frozen=True)
class Coverage:
    path: Path
    branches: tuple[Branch, ...]
    llvm_total: int

    @property
    def covered(self):
        return sum((branch.true_count > 0) + (branch.false_count > 0)
                   for branch in self.branches)

    @property
    def total(self):
        return 2 * len(self.branches)


def array(record, key):
    value = record.get(key) if isinstance(record, dict) else None
    if not isinstance(value, list):
        raise ValueError(f"missing or invalid {key} array")
    return value


def region(row, length, kinds):
    if (not isinstance(row, list) or len(row) != length
            or any(type(value) is not int or value < 0 for value in row)
            or any(value == 0 for value in row[:4])
            or tuple(row[2:4]) < tuple(row[:2]) or row[-1] not in kinds):
        raise ValueError(f"invalid coverage region: {row!r}")
    return row


def location(path, row):
    return f"{path}:{row[0]}:{row[1]}-{row[2]}:{row[3]}"


def filename(value):
    if not isinstance(value, str) or not value:
        raise ValueError("missing or invalid coverage filename")
    return Path(value).resolve()


def source_coverage(record, path):
    branches = []
    for raw in array(record, "branches"):
        row = region(raw, 9, (4, 6))  # BranchRegion or MCDCBranchRegion.
        branches.append(Branch(location(path, row), row[4], row[5]))
    # Require this field: --skip-expansions can otherwise hide macro branches.
    for expansion in array(record, "expansions"):
        files = tuple(filename(name) for name in array(expansion, "filenames"))
        call = region(expansion.get("source_region"), 8, (1,))
        if call[5] >= len(files) or files[call[5]] != path:
            raise ValueError("macro call does not belong to the selected source")
        for raw in array(expansion, "branches"):
            row = region(raw, 9, (4, 6))
            if row[6] >= len(files):
                raise ValueError("macro branch has an invalid file index")
            branches.append(Branch(location(path, call), row[4], row[5],
                                   location(files[row[6]], row)))
    if not branches:
        raise ValueError(f"no branch records for {path}")
    summary = record.get("summary")
    summary = summary.get("branches") if isinstance(summary, dict) else None
    if not isinstance(summary, dict):
        raise ValueError(f"missing LLVM branch summary for {path}")
    total, covered = summary.get("count"), summary.get("covered")
    counted = sum((branch.true_count > 0) + (branch.false_count > 0)
                  for branch in branches)
    if (type(total) is not int or type(covered) is not int
            or not 0 <= covered <= total or not 0 < total <= 2 * len(branches)
            or covered != counted):
        raise ValueError(f"LLVM branch summary disagrees with exported records for {path}")
    return Coverage(path, tuple(branches), total)


def read_coverage(document, paths):
    if (not isinstance(document, dict)
            or document.get("type") != "llvm.coverage.json.export"
            or not re.fullmatch(r"3\.\d+\.\d+", str(document.get("version")))):
        raise ValueError("expected LLVM coverage JSON export version 3")
    selected = tuple(Path(path).resolve() for path in paths)
    if len(selected) != 2 or len(set(selected)) != 2:
        raise ValueError("two different source files are required")
    for path in selected:
        if not path.is_file():
            raise ValueError(f"source file does not exist: {path}")
    records = tuple(record for data in array(document, "data")
                    for record in array(data, "files"))
    named = tuple((filename(record.get("filename")), record)
                  for record in records if isinstance(record, dict))
    if len(named) != len(records):
        raise ValueError("invalid file coverage record")
    result = []
    for path in selected:
        matches = tuple(record for name, record in named if name == path)
        if len(matches) != 1:
            raise ValueError(f"expected one coverage record for {path}; found {len(matches)}")
        result.append(source_coverage(matches[0], path))
    return tuple(result)


def count_text(covered, total):
    return f"{covered}/{total} outcomes ({100 * covered / total:.2f}%)"


def format_coverage(coverage):
    lines = ["LLVM: standard branch coverage; folded constant alternatives are omitted.",
             "Exported: both outcomes of each record, including folded constant alternatives.",
             "No error or assertion outcome is removed by a reachability review."]
    for item in coverage:
        sites = len(item.branches)
        true = sum(branch.true_count > 0 for branch in item.branches)
        false = sum(branch.false_count > 0 for branch in item.branches)
        lines.append(f"{item.path}")
        lines.append(f"  LLVM: {count_text(item.covered, item.llvm_total)}")
        lines.append(f"  exported: {count_text(item.covered, item.total)}; "
                     f"true {true}/{sites}, false {false}/{sites}")
        for branch in item.branches:
            for side, count in (("true", branch.true_count), ("false", branch.false_count)):
                if count == 0:
                    extra = f"; expanded at {branch.expansion}" if branch.expansion else ""
                    lines.append(f"  uncovered exported {branch.location} {side} "
                                 f"(true={branch.true_count}, false={branch.false_count}{extra})")
    covered = sum(item.covered for item in coverage)
    lines.append("TOTAL LLVM: " + count_text(covered, sum(item.llvm_total for item in coverage)))
    lines.append("TOTAL EXPORTED: " + count_text(covered, sum(item.total for item in coverage)))
    return "\n".join(lines)


def main(arguments):
    if len(arguments) != 3:
        raise ValueError("usage: coverage-report.py EXPORT.json CORE_PATH ORACLE_INC_PATH")
    document = json.loads(Path(arguments[0]).read_text())
    print(format_coverage(read_coverage(document, arguments[1:])))


if __name__ == "__main__":
    try:
        main(sys.argv[1:])
    except (OSError, ValueError) as error:
        sys.exit(f"coverage report: {error}")
