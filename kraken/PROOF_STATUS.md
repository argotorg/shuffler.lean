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

`PlanBridge.plan_correct` composes the assembly and model contracts.
`PlanBridge.plan_harness_correct` specializes the result to the binary host.
Both are in `PlanBridge/Final.lean`. `Interface.lean` defines the shared input and
exact flat result. `Assembly.lean` keeps the Kraken proof imports private and
lifts a property of that flat result into the assembly postcondition.
`Model.lean` keeps the Shuffler proof imports private and proves that property
from `planEntry_corr`.

The old theorem statements directly named both implementation libraries. Their
types would export those dependencies even with private imports. The new public
predicates have types over the shared flat data.

The contract definitions retain the canonical-slot premise, assembly witness,
output and frame facts, and the assertion-failure flag rule. Rejected arguments
return `-2`. Accepted arguments give the PR31 result relation, including the
output stack, trace, and source mapping on success. The definitions have private
bodies so that the public interfaces do not load either implementation library.
They are definitions of the original predicates; they add no axioms.

## Build diagnosis

Both packages use the root `nightly-2026-10-20` toolchain. The root package depends
on this package by path. Each model module belongs to this package; the root
package defines only the Shuffler and correspondence libraries. `Verification.lean`
imports the assembly proofs, proof tool tests, and combined theorem. All these
targets are part of the default root build.

The pinned Kraken source is unmodified. There is no patch or update hook.
The local proof files use Lean's module system. Files that import the combined
contract must start with `module`; a legacy importer loads private dependencies
transitively. `kraken/test/modules_test.sh` checks that public composition works
and that importing both implementations directly still reports the original
`List.allSome` conflict.

Both local packages compile with `-E warning`, so warnings in their source files
are errors. Kraken's own warnings remain visible. A workspace-wide `--wfail`
would also reject those dependency warnings, so the CI uses the package settings.

The assembly file readers resolve paths from the source file that uses them.
The root build and direct file checks therefore read the same assembly files.

The new Lean core uses `Classical.choice` in `WellFounded.fixF`. The exact axiom
reports now include that core axiom. The audit still rejects proof holes,
`native_decide`, and user axioms.

The final package build also found missing explicit binders that direct Lean
checks had accepted with automatic implicit arguments enabled. The binders are
now explicit. A missing `r13` preservation proof was supplied. The targeted
checks now use the package's strict implicit-argument settings.

The CFG definitions generate their equations at their definition sites. This
prevents duplicate equation declarations when the separate block proof modules
are imported together.

## Verification

All Lean checks use `LEAN_NUM_THREADS=1` and `nice`.

- Root `lake build`: passed (3,792 jobs). It includes the assembly proofs,
  proof tool tests, correspondence proofs, and `PlanBridge.Final`.
- Root `lake test`: all seven property-test modules passed.
- `kraken/test/axioms_test.sh`: all 19 final theorems passed. The negative
  tests reject proof holes, `native_decide`, user axioms, forged reflection
  axioms, and unknown theorem names. The tests check that the rejected theorems
  reached the audit and that proof holes and `native_decide` report their own axioms.
- `kraken/test/modules_test.sh`: passed. The public composition hides both
  implementations. Direct mixed imports and a legacy import are rejected.
- The native unit tests, binary instruction tests, binary and struct layout
  checks, field generator tests, and label tests passed.
- All six runtime comparison scripts passed. They cover 3,787 permutations,
  558,467 build-bottom-up states, 22,091 pop cases, 21,171 surplus cases,
  35,200 lowest-height cases, and 409,376 planner cases. The surplus,
  lowest-height, and planner checks also passed with their changed-input cases.
- Before the module refactor, direct checks of both assembly readers from
  `kraken/`, with the root Lake environment and strict implicit arguments, passed.
- Before the module refactor, `Fuzz/build.sh build/fuzz 1` passed with the shared
  compiler. The port unit tests, 3,011,850 generated cases, and CI wrapper tests passed.
- The earlier 30-second fuzz run with one worker exited with status 0 and reported
  no crashes or differences.

The buffer tests cover empty inputs, unequal lengths, `MAX_N`, and stores at
one index beyond an owned prefix. The rejection tests cover source and target
prefixes, an empty source, valid prefixes, and sizes above the public limit.
The data frame tests cover zero capacity, one slot, `MAX_N`, arbitrary ghost
tails, swaps, and invalid permutation indices.

The unmodified Kraken dependency reports compiler warnings. Local source files
compile with warnings treated as errors. The final theorem audit permits only
Lean's core axioms and the checked `bv_decide` reflection axioms.
