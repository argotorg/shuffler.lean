# Planner proof status

The assembly proof for the full public planner is complete.

## Final theorems

- `Bbu.plan_correct` proves the public `plan` assembly contract in a linked host.
- `Bbu.plan_harness_correct` specializes that proof to `binLinked`.
- `Bbu.plan_rejects_bad_args` proves rejection without input or output buffers.
- `Bbu.plan_rejects_invalid_ids` proves rejection with only the source and target
  prefixes that the checks can read.
- `Bbu.plan_harness_rejects_bad_args` and
  `Bbu.plan_harness_rejects_invalid_ids` specialize these rejection proofs to
  `binLinked`.
- `Bbu.planner_run_correct` proves the full `Planner::run` assembly contract.
- `Bbu.planner_run_spec` supplies its call specification.
- `Bbu.planner_run_harness_correct` specializes the internal function proof to
  `binLinked`.
- `Bbu.planner_classify_correct`, `Bbu.planner_resolve_correct`, and
  `Bbu.emission_run_correct` discharge the remaining internal calls.

The public theorems are in `BbuKraken/PlanFinal.lean` and
`BbuKraken/PlanReject.lean`. The internal run theorem is
assembled in `BbuKraken/Unit/Plan/PlannerRunAssemble.lean` and linked in
`PlannerRunLinked.lean`. `BbuKraken.lean` imports the final results.

## Coverage

| Assembly function | Checked result |
| --- | --- |
| `Planner::classify` | All 15 CFG blocks, function proof, and linked theorem |
| `Planner::resolve` | All 21 CFG blocks, function proof, and linked theorem |
| `Emission::run` | All 13 CFG blocks, function proof, and linked theorem |
| `Planner::run` | All 35 CFG blocks, model and termination joins, function proof, and linked theorem |
| `plan` | All 17 CFG blocks, model and termination joins, function proof, and linked and binary-host theorems |

The counts include the synthetic entry block and the function label. There are
no remaining block proofs or function joins on the public `plan` call path.

The public contract checks sizes, enum bytes, and source and target variable IDs
through the actual assembly branches. Rejected arguments and planner assertion
failures return the model's error word. Done and blocked results also connect the
output flag to the model through its nonzero value. Assertion failure preserves
the old output flag.

`EntryValidU.Pre` specifies buffer ownership, buffer lengths, register arguments,
and the stack frame. It does not assume that input IDs pass the public checks.
Local mapping bounds and emission safety are derived inside the proof.
`EntryValidU.Post` gives an exact `Flat.planEntry` result witness and restores the
memory frame. The linked public theorem has no helper-call specification
parameters.

The public and internal run contracts own `m` dropped bytes, `max(m,n)` data
words, and `n` source-result words. The operation buffer has `4m + 6n` records.
The pure model keeps its `MAX_N` vectors. Values above each physical buffer
prefix remain ghost values; the emission proof restores their original values
in the exact model result.

The separate bad-argument contract owns only 11 free stack words, the return
slot, and the two enum arguments. Invalid-ID rejection also owns the
read source and target prefixes. A source rejection needs no target cells. A
target rejection needs all source cells and a target prefix that contains an
invalid ID. Neither rejection contract needs output buffers or spill bytes.
Both return `-2` and restore their memory frame.

The separation assertions require the owned memory blocks to be disjoint.
The proof does not permit arbitrary overlap between nonempty source, target,
output, spill, and stack regions.

The ancillary `build_mapping`, `emit`, and public `resolve` wrappers still lack
assembly proofs. They are outside the public `plan` call path.

## Specification connection

`PlanBridge.planEntry_corr` connects the same `Flat.planEntry` source to PR31
`Planner.run`. Its `SlotsOk` premise requires canonical slot encodings, kinds
below four, and consistent variable encodings for equal payloads.

The assembly result witness supplies the flat-model side of this connection.
The assembly theorem covers arbitrary slot bits under its memory contract; the
PR31 correspondence retains `SlotsOk`. The two proof stages use separate Lake
packages and toolchains. There is no combined theorem that imports both compiled
packages into one Lean environment.

## Build diagnosis

The repository root uses Lean `v4.35.0`. This package uses
`nightly-2026-10-20`. Run assembly commands from `kraken/`.

The nightly toolchain was absent. A download with a 20-second limit stopped before
installation finished. Installation without that limit succeeded. No toolchain
or package configuration was changed.

The final package build also found missing explicit binders that direct Lean
checks had accepted with automatic implicit arguments enabled. The binders are
now explicit. A missing `r13` preservation proof was supplied. The targeted
checks now use the package's strict implicit-argument settings.

The CFG definitions generate their equations at their definition sites. This
prevents duplicate equation declarations when the separate block proof modules
are imported together.

## Verification

- `LEAN_NUM_THREADS=6 nice lake build BbuKraken ProofKitTest`: passed, 950 jobs.
- Root `nice lake build PlanBridge`: passed, 1420 jobs.
- The final theorem axiom audits pass. Allowed dependencies are the Lean core
  axioms and the checked `bv_decide` reflection axioms for small word lemmas.
- `test/axioms.sh` audits 14 final theorems, including the four rejection
  theorems. `test/axioms_test.sh` passed all acceptance and rejection cases.
- The buffer tests cover empty inputs, unequal input lengths, `MAX_N`, and
  stores at the first index outside an owned prefix. The rejection tests cover
  source and target prefixes, an empty source, valid prefixes, and prefixes
  that exceed the public size.
- The data frame tests cover zero capacity, one slot, `MAX_N`, arbitrary ghost
  tails, swaps, and invalid permutation indices. The frame theorems for
  `buildBottomUp` and `emissionRun` use only Lean's core axioms.

The proof sources contain no `sorry`, `admit`, user axiom declarations, or
`native_decide`. The user assigned this task 24 threads and 96 GB RAM and
authorized parallel proof work, which overrides the shared-machine process
limit in `AGENTS.md` for this task.
