#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the actual public theorem against admissions and weaker statements."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def run(args, work, log, separate_errors=False):
    with log.open("w") as output:
        result = subprocess.run(args, cwd=work, stdout=output,
                                stderr=subprocess.PIPE if separate_errors else subprocess.STDOUT,
                                timeout=180)
    if separate_errors:
        log.with_suffix(".stderr.log").write_bytes(result.stderr)
    return result.returncode


def main():
    source = (ROOT / "ClightCorrect.v").read_text()
    start = source.index("Theorem permute_call_correct ")
    proof = source.index("\nProof.", start)
    end = source.index("\nQed.", proof) + len("\nQed.")
    statement = source[start:proof]
    variants = {
        "baseline": (source[start:end], False, False),
        "admitted": (statement + "\nAdmitted.", True, False),
        "false_assumption": ("Axiom proof_shortcut : False.\n" + statement +
                             "\nProof. exact (False_rect _ proof_shortcut). Qed.", True, False),
        "shadowed_assumption": ("Module Classical_Prop.\nAxiom classic : False.\n"
            "End Classical_Prop.\n" + statement +
            "\nProof. exact (False_rect _ Classical_Prop.classic). Qed.", True, False),
        "unchecked_recursion": ("Unset Guard Checking.\n"
            "Fixpoint proof_shortcut (n : nat) : False := proof_shortcut n.\n"
            "Set Guard Checking.\n" + statement +
            "\nProof. exact (False_rect _ (proof_shortcut 0%nat)). Qed.", True, False),
        "unchecked_positivity": ("Unset Positivity Checking.\n"
            "Inductive invalid : Prop := wrap_invalid : (invalid -> False) -> invalid.\n"
            "Set Positivity Checking.\n"
            "Definition unwrap_invalid (x : invalid) : invalid -> False :=\n"
            "  match x with wrap_invalid f => f end.\n"
            "Definition proof_shortcut (x : invalid) : False := unwrap_invalid x x.\n" + statement +
            "\nProof. exact (False_rect _ (proof_shortcut (wrap_invalid proof_shortcut))). Qed.",
            True, False),
        "impossible_precondition": (statement.replace(
            "  (d.+1 <= 1024)%coq_nat ->", "  False -> (d.+1 <= 1024)%coq_nat ->", 1) +
            "\nProof. intros Impossible. contradiction. Qed.", False, True),
        "true_postcondition": ("Theorem permute_call_correct (d : nat) (ge : Clight.genv) "
            "(memory : Mem.mem) (bd bp bt bu btrace bo : block)\n"
            "    (source : 'I_d.+1 -> nat) (p : 'S_d.+1) : True.\n"
            "Proof. exact I. Qed.", False, True),
    }
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cases", nargs="+", choices=tuple(variants), default=tuple(variants))
    args = parser.parse_args()
    destination = args.output.resolve()
    destination.mkdir(parents=True, exist_ok=False)
    flags = ["-w", "-notation-overridden,-deprecated-from-Coq", "-R",
             str(ROOT / "build/compcert"), "compcert", "-Q", str(ROOT / "build/legacy"), "Legacy"]
    reports = []
    for name, (replacement, reject_assumptions, reject_contract) in variants.items():
        if name not in args.cases:
            continue
        case = destination / name
        case.mkdir(exist_ok=True)
        work = case / "proofs"
        if work.exists():
            shutil.rmtree(work)
        shutil.copytree(ROOT / "build/proofs", work)
        (work / "ClightCorrect.v").write_text(source[:start] + replacement + source[end:])
        shutil.copyfile(work / "ClightCorrect.v", case / "ClightCorrect.v")
        compiled = run(["coqc", *flags, "ClightCorrect.v"], work, case / "compile.log")
        if compiled:
            raise RuntimeError(f"{name}: test theorem failed to compile")
        kernel = run(["coqchk", "-silent", "-o", *flags[2:], "ClightCorrect"],
                     work, case / "coqchk.log", separate_errors=True)
        if kernel:
            raise RuntimeError(f"{name}: unexpected kernel rejection")
        kernel_policy = run([sys.executable, str(ROOT / "check-assumptions.py"), "--kernel",
                             str(case / "coqchk.stderr.log")], work, case / "kernel-gate.log")
        claims = ("ClightCorrect.permute_call_correct", "ClightCorrect.permute_body_correct",
                  "ClightCall.permute_empty_call", "ClightCall.permute_oversized_call")
        commands = ["Require Import ClightCorrect ClightCall."]
        for claim in claims:
            commands += [f'Goal True. idtac "{claim}". Abort.', f"Print Assumptions {claim}."]
        (work / "GuardAssumptions.v").write_text("\n".join(commands) + "\n")
        status = run(["coqc", *flags, "GuardAssumptions.v"], work, case / "assumptions.txt",
                     separate_errors=True)
        if status:
            raise RuntimeError(f"{name}: cannot obtain assumptions")
        assumptions = run([sys.executable, str(ROOT / "check-assumptions.py"), str(case / "assumptions.txt")],
                          work, case / "assumption-gate.log")
        shutil.copyfile(HERE / "ProofContract.v", work / "ProofContract.v")
        contract = run(["coqc", *flags, "ProofContract.v"], work, case / "contract-gate.log")
        record = {"name": name, "coqc": compiled, "coqchk": kernel,
                  "assumption_gate": assumptions, "kernel_context_gate": kernel_policy,
                  "contract_gate": contract,
                  "expected_result": ((assumptions != 0) == reject_assumptions and
                                      (kernel_policy != 0) == reject_assumptions and
                                      (contract != 0) == reject_contract)}
        reports.append(record)
        (destination / "results.json").write_text(json.dumps(reports, indent=2) + "\n")
        print(json.dumps(record), flush=True)
    if not all(record["expected_result"] for record in reports):
        raise SystemExit("proof guard controls differ from expected results")


if __name__ == "__main__":
    main()
