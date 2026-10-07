#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Reject new axioms or missing claims in Rocq's Print Assumptions report."""
from pathlib import Path
import re
import sys

ALLOWED = frozenset({
    "Classical_Prop.classic",
    "ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
    "Events.external_functions_sem",
    "Events.inline_assembly_sem",
})
# coqchk reports the whole imported environment, including unused upstream
# axioms. These twelve names occur in the checked baseline. The per-theorem
# policy above remains narrower. Kernel names include their library paths.
KERNEL_ALLOWED = frozenset({
    "Stdlib.Logic.Classical_Prop.classic",
    "Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq",
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep",
    "Stdlib.Logic.ProofIrrelevance.proof_irrelevance",
    "Stdlib.Reals.ClassicalDedekindReals.sig_not_dec",
    "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec",
    "compcert.common.Events.external_functions_sem",
    "compcert.common.Events.external_functions_properties",
    "compcert.common.Events.inline_assembly_sem",
    "compcert.common.Events.inline_assembly_properties",
    "compcert.lib.Axioms.proof_irr",
    "compcert.x86_64.Archi.win64",
})
REQUIRED = frozenset({
    "ClightCorrect.permute_call_correct",
    "ClightCorrect.permute_body_correct",
    "ClightCall.permute_empty_call",
    "ClightCall.permute_oversized_call",
})
NAME = r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+"


def check_kernel(report):
    """Check coqchk -silent -o output, including each unsafe-typing category."""
    lines = [line.strip() for line in report.splitlines() if line.strip()]
    header = ["CONTEXT SUMMARY", "===============", "* Theory: Set is predicative",
              "* Theory: Rewrite rules are not allowed"]
    tail = ["* Constants/Inductives relying on type-in-type: <none>",
            "* Constants/Inductives relying on unsafe (co)fixpoints: <none>",
            "* Inductives whose positivity is assumed: <none>"]
    if lines[:4] != header or lines[-3:] != tail:
        raise ValueError("kernel context has missing sections or unsafe typing settings")
    section = lines[4:-3]
    if section == ["* Axioms: <none>"]:
        return frozenset()
    if len(section) < 2 or section[0] != "* Axioms:":
        raise ValueError("invalid kernel axiom section")
    axioms = frozenset(section[1:])
    if len(axioms) != len(section) - 1 or not axioms <= KERNEL_ALLOWED:
        raise ValueError(f"duplicate or unapproved kernel axioms: {sorted(axioms - KERNEL_ALLOWED)}")
    return axioms


def check(report, expected=None):
    claims = {}
    current, state, axioms = None, None, set()

    def finish():
        if current is None:
            return
        if state not in ("closed", "axioms") or (state == "axioms" and not axioms):
            raise ValueError(f"incomplete assumption report: {current}")
        claims[current] = frozenset(axioms)

    for line in report.splitlines():
        if not line.strip():
            continue
        if re.fullmatch(NAME, line):
            finish()
            if line in claims:
                raise ValueError(f"duplicate claim: {line}")
            current, state, axioms = line, None, set()
        elif line == "Closed under the global context" and current and state is None:
            state = "closed"
        elif line == "Axioms:" and current and state is None:
            state = "axioms"
        elif state == "axioms" and (match := re.match(f"^({NAME})\\s*:", line)):
            name = match[1]
            if name not in ALLOWED:
                raise ValueError(f"unapproved assumption for {current}: {name}")
            axioms.add(name)
        elif state == "axioms" and axioms and line.startswith(" "):
            continue  # Rocq wraps the type of the preceding named assumption.
        else:
            raise ValueError(f"unrecognized assumption report line: {line}")
    finish()
    names = claims.keys()
    if expected is not None:
        if names != set(expected):
            raise ValueError(f"theorem list differs: {sorted(names ^ set(expected))}")
    elif not REQUIRED <= names:
        raise ValueError(f"missing required claims: {sorted(REQUIRED - names)}")
    return claims


if __name__ == "__main__":
    try:
        if len(sys.argv) == 3 and sys.argv[1] == "--kernel":
            axioms = check_kernel(Path(sys.argv[2]).read_text())
            print(f"Kernel context: {len(axioms)} allowed axioms; no unsafe typing settings")
            sys.exit(0)
        if len(sys.argv) not in (2, 3):
            raise ValueError("usage: check-assumptions.py REPORT [THEOREM_LIST] | --kernel REPORT")
        expected = Path(sys.argv[2]).read_text().splitlines() if len(sys.argv) == 3 else None
        claims = check(Path(sys.argv[1]).read_text(), expected)
        if not REQUIRED <= claims.keys():
            raise ValueError("the report omits a required public theorem")
        print(f"Assumption allowlist: {len(claims)} claims; no new assumptions")
    except (OSError, ValueError) as error:
        sys.exit(str(error))
