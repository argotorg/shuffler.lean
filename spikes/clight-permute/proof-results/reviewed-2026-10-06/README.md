<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Checked public review interface

`check-proofs.sh` completed after the specification definitions were moved
into `ModelSpec.v` and `PermuteSpec.v`, and the public theorems were added in
`PermuteCorrect.v`. The Clight AST and generated C are unchanged.

The run compiled all project and legacy modules, checked the three
independent public type fixtures, checked every enumerated theorem's
assumptions, and completed `coqchk`. The kernel context contains the same
twelve upstream axioms as the recorded baseline, with no unsafe typing
settings. These are environment-wide axioms; the theorem assumption policy
remains the narrower six-name policy.

The source manifest identifies this check. The log, theorem list, assumption
report, kernel context, and module list are retained without compiled files.
The three type fixtures are additional to `checked-modules.txt`.

`guard-results.json` records all eight expected guard-control results.
`mutation-results.json` records two behavior changes rejected by dependent
proofs and two equivalent controls accepted with all three public types.
Their source variants and logs are retained under `guards/` and `mutations/`.
`control-sources.sha256` identifies the runners and mutation manifest.

This establishes the stated Clight-to-model theorem. It does not establish
the Lean relation, a Clight-to-ISO-C translation theorem, or full C/C++
equivalence. See the [review entry point](../../../../docs/verified-permute/README.md)
and [trust boundary](../../../../docs/verified-permute/trust-boundary.md).
