#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Import the pinned Vellvm frontend's Rocq term (an untrusted candidate)."""
import sys
import re
from pathlib import Path


def import_ast(text: str) -> str:
    marker = "Internal Coq representation of the ast:"
    if text.count(marker) != 1:
        raise ValueError("expected one Vellvm AST marker")
    term = text.split(marker)[1].strip()
    if not (term.startswith("[") and term.endswith("]")):
        raise ValueError("expected a Vellvm module list")
    # ReprAST uses OCaml quote escaping inside Rocq string literals.
    # These repairs produce input to the kernel; they are not trusted.
    term = term.replace('\\"', '""')
    term = term.replace("LOC_Armem", "LOC_Argmem")
    term = term.replace("ANN_tail tail", "ANN_tail Tail")
    # Accept only tokens of a constructor term. In particular, a standalone
    # period, comments, and tactic escapes cannot inject Rocq commands.
    token = re.compile(r'\s+|"(?:[^"]|"")*"|[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*|-?[0-9]+|[\[\]();,%]')
    offset = 0
    while offset < len(term):
        match = token.match(term, offset)
        if match is None:
            raise ValueError(f"unsupported Rocq term token at offset {offset}")
        offset = match.end()
    return (
        "From Stdlib Require Import List ZArith String.\n"
        "From Vellvm Require Import LLVMAst.\n"
        "Import ListNotations.\nOpen Scope string_scope.\n"
        "Definition candidate : list (toplevel_entity typ (block typ * list (block typ))) :=\n"
        + term + ".\n"
    )


if __name__ == "__main__":
    Path(sys.argv[2]).write_text(import_ast(Path(sys.argv[1]).read_text()))
