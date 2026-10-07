<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# C ↔ Lean proof-of-concept review

For completed work and open gaps, read the [short summary](SUMMARY.md).

The main subject is the proposed C ↔ Lean verification workflow. Permute
is the test case. Start with the core Rocq definitions and theorem statements,
then assess the independent evidence that tests this workflow before it is
used for larger programs.

The checked central link is **Clight → the duplicate-aware Rocq model**
(stated as complete-call refinement). The Lean ↔ Rocq relation is unproved.
The original [Lean definition](../../Shuffler/Permute/Defs.lean) omits the
duplicate normalization and equal-value swap rules now present in Rocq.
The Clight-to-printed-C translation also remains trusted, with a confirmed
initialization gap in the accepted printer subset. These are workflow gaps.

Solc comparisons, symbolic tools, sanitizers, and mutation tests are
supporting evidence. They test the workflow and its assumptions. Full solc
C++ equivalence is not the central theorem and is not claimed.

See [lean-rocq-link.md](lean-rocq-link.md) for the proposed model-correspondence
route and its distinction from importing proof terms between systems.

## Core definitions

| File | What to review |
| --- | --- |
| [`SolcModel.v`](../../spikes/clight-permute/SolcModel.v) | `target_of`, duplicate normalization, `solc_run`, and `solc_permute`. This is the mathematical algorithm used by the theorem. |
| [`Permute.v`](../../spikes/clight-permute/Permute.v) | `check_input`, `normalize`, `choose_position`, `exchange`, and `permute`. This is the actual Clight implementation that is extracted and printed. |
| [`Legacy.Permute`](../../spikes/rocq-permute/Permute.v) | Shared definitions `exchange`, `choose`, `rank`, `depth`, and `swap_stack`. Its earlier top-level algorithm is not the duplicate-aware model used by the public theorem. |
| [`Legacy.Proofs`](../../spikes/rocq-permute/Proofs.v) | `SwapTrace`, the inductive relation for legal physical swaps. |

The model assigns each source index a destination. Normalization reserves
positions whose values are already correct, then pairs the remaining
sources and equal target values in ascending index order. The loop updates
destinations even when selected values are equal. Equal values emit no swap
and skip the depth check. Check these rules in both core files.

## Public statement

[`PermuteCorrect.v`](../../spikes/clight-permute/PermuteCorrect.v) exposes:

```coq
Theorem clight_refines_model d (source : 'I_d.+1 -> nat) (destinations : 'S_d.+1)
    (arrays : buffers) ge initial :
  valid_call source destinations arrays initial ->
  exists final code result,
    clight_returns d arrays ge initial final code /\
    matches_model source destinations arrays final code result.
```

For a valid call, the actual Clight function returns. Its result agrees
with the exact model result. This includes the return code, final or
partial data, written trace, trace count, blocked position, and excess
depth. A successful execution is a conclusion, not a premise.

Read the named predicates in
[`PermuteSpec.v`](../../spikes/clight-permute/PermuteSpec.v):

| Definition | Review question |
| --- | --- |
| `buffers` | Are the six array roles distinct and correctly mapped? |
| `valid_call` | Does the input domain include every required valid call? |
| `clight_returns` | Is this the complete call to the actual `Permute.permute` AST? |
| `matches_model` | Does it use the exact result of `SolcModel.solc_permute`? |
| `result_arrays` | Are status, data, trace prefix, and all output fields represented correctly? |
| `separate_arrays` | Are memory separation requirements explicit? |

`d+1` is the stack length; the index type excludes empty stacks. The type
`'S_d.+1` contains valid permutations. The remaining premises require
length at most 1024, unsigned 32-bit values, six distinct writable blocks,
initialized data and permutation, and sufficient scratch/output capacity.
All pointers start at offset zero. Empty and oversized calls have separate
theorems in [`ClightCall.v`](../../spikes/clight-permute/ClightCall.v).
Malformed-permutation rejection has tests, but no universal call theorem.

[`ModelSpec.v`](../../spikes/clight-permute/ModelSpec.v) contains the model
postcondition and the success condition:

```text
target[j] = initial_data[inverse_permutation(j)]
success iff every position deeper than 16 already has its target value
```

This is a condition on values. Duplicate values can make a position correct
even when its original permutation entry is not fixed. Depth 16 is allowed.
`PermuteCorrect.clight_decides_reachability` states this condition for
the actual Clight call, together with the same exact result relation.

## Trust boundary

Read [trust-boundary.md](trust-boundary.md) for the exact separation between
definitions that need human review, proof scripts checked by Rocq, and tools
that remain trusted. Tests and symbolic runs have their own limited domains.

The expanded public type is retained independently in
[`PublicContract.v`](../../spikes/clight-permute/tests/proof-challenge/PublicContract.v).
It checks that the readable theorem retains the original premises and
conclusions. The [original call type fixture](../../spikes/clight-permute/tests/proof-challenge/ProofContract.v)
and [reachability type fixture](../../spikes/clight-permute/tests/proof-challenge/ReachabilityContract.v)
remain separate checks. These fixtures require human review too; agreement
between two wrong specifications would not establish the required behavior.

## Independent supporting evidence

Read this evidence after the definitions, public statements, and trust
boundary. Each tool challenges a different part of the workflow.

The [checked proof archive](../../spikes/clight-permute/proof-results/reviewed-2026-10-06/README.md)
records the refactored proof, public type checks, and policy controls.
The [supporting evidence index](../../spikes/clight-permute/tests/results/resumed-2026-10-06/README.md)
records the completed resumed tool runs and their limits.
The [extended evidence](../../spikes/clight-permute/tests/results/extended-2026-10-06/README.md)
adds symbolic rejection checks, a selected length-six comparison, and
controls for lost forks and assumptions inserted into tested code.

| Evidence | What it tests | Limit |
| --- | --- | --- |
| [Proof mutations and guards](../../spikes/clight-permute/tests/proof-challenge/) | Changed AST/model behavior, admissions, false axioms, unsafe settings, and weakened statements. | Selected mutations do not prove that every incorrect change is rejected. |
| [Printer reproduction](../../spikes/clight-permute/tests/equiv-saw/undef-copy/README.md) | A proved Clight self-copy prints an uninitialized C read. | Confirms a translation-contract gap; unchanged production C has no such witness. |
| [Clight execution comparison](../../spikes/clight-permute/tests/rocq-eval/README.md) | The extracted Clight interpreter and actual generated C agree on 1,110 selected cases across six compiler builds. | Finite tests; extraction, adapters, and compilers remain trusted. |
| [Generated printer programs](../../spikes/clight-permute/tests/printer-eval/README.md) | 128 generated ASTs, 50 inputs each, six compiler builds, and printer mutation controls. | A selected grammar and finite inputs; initialization and bounds are supplied by the generator. |
| [Candidate assignment check](../../spikes/clight-permute/tests/initialization/README.md) | Prior-assignment proofs for control paths and terminating Clight executions; actual AST check and negative controls. | Memory byte initialization, concrete divergent prefixes, and C translation remain separate. The checker is outside the production pipeline. |
| [Source mutation matrix](../../spikes/clight-permute/tests/challenge/README.md) | Native tests detect changed data, status, trace, depth, and size behavior. | Finite executions and selected changes. |
| [KLEE comparisons](../../spikes/clight-permute/tests/equiv-alive2/README.md) and [SAW comparisons](../../spikes/clight-permute/tests/equiv-saw/README.md) | Actual C and pinned solc bodies on explicit symbolic domains; completion and result handling. | Limited sizes or value families and explicit LLVM/runtime assumptions. |
| [Frama-C status](status/frama-c.md) | Source-C memory, initialization, termination, trace, and reachability obligations. | All six components pass individually (2,749 goals); the combined run and two source control suites remain incomplete. |
| [Fuzzing](../../spikes/clight-permute/tests/FUZZ_RESULTS.md), [MSan](../../spikes/clight-permute/tests/MSAN_RESULTS.md), [Fil-C](../../spikes/clight-permute/tests/FILC_RESULTS.md) | Execution errors, output disagreements, and runtime memory checks. | Coverage and sanitizer passes are not universal proofs. |

Use [WORKING_STATUS.md](WORKING_STATUS.md) for current run status and
[FINDINGS.md](FINDINGS.md) for confirmed defects and open proof links.
The [older review guide](review-guide.md) lists the original commit series.
