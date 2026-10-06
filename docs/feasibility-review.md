# Review the feasibility results

Start with [Shuffler/Feasibility/Spec.lean](../Shuffler/Feasibility/Spec.lean).
It contains the actual predicate definitions and the four complete public
statements together. These are the definitions used by the proof modules.

The four statement names are definitions of propositions. The existing
theorems prove those propositions; the specification does not assume them
as axioms. [Shuffler/Feasibility/Theorems.lean](../Shuffler/Feasibility/Theorems.lean)
is the public import for the proofs.

| Statement in the specification | What it decides |
|---|---|
| `AppendOnlyGeneration` | Whether DUP, PUSH, and LOAD can add the requested multiset, with a free generation order. |
| `GenerationWithSwaps` | Whether generation and SWAP can add the requested multiset, with no required final order. |
| `ExactPlacement` | Whether a trace can reach a specified concrete target with exactly the specified additions. |
| `WildcardPlacement` | Whether a trace can reach some result that matches a target pattern. Both that concrete result and its additions are chosen. |

All four results exclude POP. The first three fix the exact additions. The
pattern result chooses an addition multiset together with a matching result.

## What to review

1. **The operations and their limits.** The proof uses the production
   [Trace constructors](../Shuffler/Trace.lean). The stack is written bottom
   first. The [limits](../Shuffler/Basic.lean) are zero-based: DUP reads depths
   0 through 15; SWAP can move values at depths 0 through 16. Check that these
   are the intended machine rules.
2. **The allowed traces.** `onlyGenerates` excludes SWAP and POP. `noPop`
   permits SWAP but excludes POP. `additions` counts the values actually
   produced by DUP, PUSH, and LOAD. Exact additions exclude extra temporary
   values.
3. **The source requirement.** `Free` means a value can be pushed or loaded.
   `seeds` keeps one copy of each distinct nonfree kind still requested. It
   does not keep one copy per request. Check the
   [Value and free-generation definitions](../Shuffler/Stack.lean), too.
4. **The placement condition.** `frozen` counts the initial bottom positions
   outside SWAP reach. `window` contains the remaining initial top 17 slots,
   or the whole source if shorter. `boundary` reserves the next target
   output only when growth is required and the source has at least 17 slots.
   `Reserve` checks value counts, the frozen prefix, and enough separate
   occurrences for that output and the needed seeds.
5. **What a target means.** `ExactPlacement` uses exact value equality.
   `SlotMatches actual pattern` lets a wildcard in the pattern accept any
   actual value. `StackMatches` also requires equal lengths.
   `WildcardPlacement` chooses both a matching concrete result and its exact
   additions. Failure for one chosen result does not reject all possible
   matches.

A known machine-model TODO remains: `Trace.Dup` permits a
`FunctionReturnLabel`. The theorems use that rule; one existing label can
supply a second label through DUP1. A model that forbids this operation needs
a matching restriction that excludes such additions, plus an update to the
sufficiency proofs. This work does not change the rule.

The core results do not fix a mapping of individual source copies to target
positions. They decide whether some legal plan exists. They do not prove
that BBU's supplied mapping and choices find that plan. The separate
[`expectedStack` compatibility bridge](../Shuffler/BuildBottomUp/Compatibility.lean)
requires the bound source values to match their target slots, including
wildcards. There is no mapping-builder correctness claim here.

## Where the proofs and checks are

The existing theorem names remain available:

| Public theorem | Proof module |
|---|---|
| `Shuffler.Generate.canGenerate_iff_ready` | [Append-only generation](../Shuffler/Generate/Theorems.lean) |
| `Shuffler.Generate.WithSwaps.canGenerate_iff_ready` | [Generation with swaps](../Shuffler/Generate/WithSwaps.lean) |
| `Shuffler.Placement.canPlace_iff_reserve` | [Exact placement](../Shuffler/Placement/Theorems.lean) |
| `Shuffler.Placement.exists_matching_trace_iff_reserve` | [Wildcard patterns](../Shuffler/Placement/Compatibility.lean) |

Lean checks the proof bodies against the statements. The focused tests cover
[generation](../Tests/GenerateFeasibility.lean),
[generation with swaps](../Tests/GenerationWithSwaps.lean), and
[placement and patterns](../Tests/PlacementFeasibility.lean). They use the
production definitions and include successful cases and rejected cases.

For the intuition, read the [illustrated explainer](generation-feasibility.html).
The separate arguments about a protected prefix with swaps, general machine
limits, and the stronger impossibility result allowing POP remain outside
these four proved statements.
