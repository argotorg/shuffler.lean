# When can we generate the missing slots?

[Open the illustrated HTML explainer](generation-feasibility.html).

For code review, start with
[Feasibility/Spec.lean](../Shuffler/Feasibility/Spec.lean). It contains the
actual predicate definitions and all four public statements together.
The [review guide](feasibility-review.md) explains what to check.

There is a simple exact condition if we separate **generation** from **placement**:

> If we can choose the generation order, every missing value that cannot be
> pushed or loaded must have a copy in the initial DUP region.

This condition is necessary and sufficient for a plan that only appends values.
It does not require a bound on the stack length or on the number of missing
slots. It does not state that the new values end in their target positions.

**Proof status:** the append-only equivalence, its BBU `Reachable` corollary,
and the equivalence that allows swaps are proved in Lean. The existing
`StaticSuccess` theorem concerns the full BBU algorithm; it is a different
result.

## The question and the operations

Let `S` be the initial stack, written bottom first. Let `H` be the finite list
of missing values, including repeated values. Treat `H` as a multiset: its order
does not constrain the generation order.

Let `Free(v)` mean that `v` can be pushed or loaded from the spill set. A literal
or wildcard can be pushed. A spilled variable can be loaded. All other missing
values need an existing copy.

Write `D` for the number of slots that DUP can read. In this workspace, `D=16`:

- DUP can read depths 0 through 15.
- SWAP can exchange the top with depths 1 through 16.
- PUSH and LOAD append one value.
- POP removes the top, but is excluded from the results below.

These are the operations in [Trace.lean](../Shuffler/Trace.lean), with limits
from [Basic.lean](../Shuffler/Basic.lean). The generation branch of
[BBU's `produce`](../Shuffler/BuildBottomUp/Defs.lean) uses the same DUP, PUSH,
and LOAD operations.

All equality here is exact `Value` equality. A wildcard is a freely generated
value. We do not use a wildcard-matching relation to replace other demands.

## 1. Append-only generation

Allowed operations: DUP, PUSH, and LOAD. Each step appends one demanded value
and removes one occurrence of that value from the remaining demand. There are
exactly `|H|` steps. There are no swaps, pops, or extra temporary slots.

Success means that the result is `S ++ A`, where `A` is a permutation of `H`.
Thus the entire original stack stays unchanged.

Define:

```text
CopyReady(S,H) :=
  for every value v in H,
    Free(v) or v occurs in the initial top D slots of S.
```

Then:

```text
an append-only generation plan exists  iff  CopyReady(S,H).
```

The Lean theorem is
[`Shuffler.Generate.canGenerate_iff_ready`](../Shuffler/Generate/Theorems.lean).
Its [definitions](../Shuffler/Feasibility/Spec.lean) use an actual `Trace`, restrict
it to DUP, PUSH, and LOAD, and require the appended list to be a permutation of
the missing list. There is no input-size bound, validity assumption, or fixed
generation order.

For the initially unassigned target slots of a BBU state, `CopyReady` is exactly
the existing [Reachable predicate](../Shuffler/BuildBottomUp/Lemmas/Reachability.lean).
This is proved by
[`canGenerate_missing_iff_reachable`](../Shuffler/Generate/BuildBottomUp.lean),
which also needs no `State.Valid` assumption. The general generation result
does not require a BBU mapping at all.

### Why the condition is necessary

Consider a demanded value `v` that cannot be pushed or loaded. Its first new
copy must come from DUP. Before that step, no earlier generation step has added
`v`. Since all earlier steps only append, each original copy has stayed at its
original position and has become no closer to the top.

If no copy was initially within DUP reach, this first duplication is impossible.

### Why the condition is sufficient

Keep this invariant: every remaining nonfree demand has a copy within DUP reach.

If any nonfree demand remains, select the value whose **shallowest copy is
deepest**. Duplicate it and remove one occurrence from the demand. For each
other still-needed nonfree value, its shallowest copy was strictly above the
selected copy. It therefore stays within the top `D` slots after the append.
If the selected value is still needed, its new copy is at the top.

Once only free values remain, push or load them in any order. Each step reduces
the remaining demand by one, so the process finishes after exactly `|H|` steps.

The depth argument is precise. If the current length is `n`, the selected copy
has position `p` with `n ≤ p+D`. Every other selected representative has position
`q>p`, so `n+1 ≤ q+D`. That is exactly its DUP-reach condition after the append.

This proof also gives a simpler rule for each step:

> If the next append would bury the last reachable copy of a still-needed
> nonfree value, duplicate that value first. Otherwise, generate any remaining
> value.

At most one value can be endangered by a single append: the value at the bottom
of the DUP region. This rule does not require extra duplicates. Each duplicate
fulfils one existing demand.

### Example: order matters, but a feasible order exists

Let `x` be a variable that is not spilled:

```text
initial stack: [x, 0, 0, ..., 0]   (16 slots)
missing values: [0, x]
```

Appending `0` first puts `x` at depth 16. DUP can no longer read it. Appending
`x` first, then `0`, satisfies both demands. The initial copy condition holds
and correctly says that some order succeeds.

The number of copies requested is unrestricted. One reachable copy can supply
many missing copies. The schedule keeps a copy available for as long as it is
needed.

## 2. Generation with swaps

Now also allow SWAP, with maximum depth `D`. Thus the movable region has `D+1`
slots. Still exclude POP and require exactly the demanded additions. Existing
slots can move, but none is removed. Final placement is still unrestricted.

Let `K` be the set of distinct nonfree values in `H`. Then a generation plan
exists exactly when:

```text
every v in K occurs in the initial top (D+1) slots
and
|K| ≤ D.
```

For this machine, each needed nonfree kind must occur in the initial top 17
slots, and there can be at most 16 distinct needed nonfree kinds.

The Lean theorem is
[`Shuffler.Generate.WithSwaps.canGenerate_iff_ready`](../Shuffler/Generate/WithSwaps.lean).
Its `CanGenerate` means that some final stack is reachable by an actual
production trace, with no POP and exactly the additions `H`. Its `Ready`
requires the distinct nonfree seeds in the initial SWAP region and limits
their count to `MAX_DUP_DEPTH + 1`, which is 16.

The proof is a corollary of the exact placement reserve theorem. When growth
is required from at least 17 slots, the count bound leaves one occurrence
beside the required seeds. Choose that occurrence as the next fixed output.
The reserve theorem then supplies a trace to a suitable final stack. The
reverse direction follows from the necessary reservations for any final
stack. This Lean result uses the repository's fixed machine limits; the
explanation using general `D` below is a mathematical argument.

The [focused Lean tests](../Tests/GenerationWithSwaps.lean) check depth 16
versus 17, sixteen versus seventeen needed kinds, empty sources, spills,
repeated demand, and an explicit `SWAP16; DUP1` production trace.

This extra slot can help. From `[x, 0, ..., 0]` with 17 slots and demand `[x]`,
SWAP16 moves `x` to the top; DUP1 then makes the missing copy. Append-only
generation could not start.

### Why these conditions are necessary

A value outside the initial SWAP region cannot enter it through swaps and
appends. Swaps touch only the current region; appends move its lower boundary
upward. A nonfree value with no copy in the initial region therefore cannot
supply a new copy.

This leaves at most `D+1` distinct needed nonfree kinds. Suppose there are
exactly `D+1`. Every slot in that region then holds a different needed kind,
with one reachable copy of each. Swaps can only permute them before the first
append.

That first append moves the bottom slot outside SWAP reach. If it is a DUP,
its source was in the top `D`, so it did not duplicate the distinct value in
the bottom slot. If it is a PUSH or LOAD, it did not create that nonfree value
either. A still-needed kind has therefore lost its only reachable copy before
any demand for it was fulfilled. The plan cannot finish.

### Why the conditions are sufficient

Choose one representative of each kind in `K`. There are at most `D` such
representatives, all in the top `D+1` slots. Swaps with the top can permute that
region, so put all representatives within the top `D` slots.

The append-only condition now holds. Apply the plan from the first result.
No further swaps are needed.

If the initial stack has at most `D` slots, all its slots are already in DUP
reach, and the count bound is automatic. With the mathematical limit `D=0`,
the condition reduces to having no nonfree demands; PUSH and LOAD suffice.

### Example: 17 needed kinds prevent growth

```text
initial stack: [x0, x1, ..., x16]
missing values: [x0, x1, ..., x16]
```

All variables are distinct and none is spilled. Every needed kind is in SWAP
reach, but there are 17 of them. After any sequence of swaps, the first append
loses one still-needed kind below the reachable region. No generation plan
under these rules can finish.

If only 16 of these kinds are needed, put the unneeded kind at depth 16. All
needed representatives then fit in DUP reach, and generation can finish.

## A prefix that must stay fixed

The append-only result preserves every original slot. It therefore preserves
any fixed prefix without an extra condition.

The swap construction may move any initial slot in the top 17. If a prefix of
length `c` must stay fixed and `n≥17`, that construction is permitted when
`c≤n−17`. If `c>n−17`, the depth-16 slot is protected. It cannot be swapped or
duplicated, and appends only make it deeper. It cannot supply a missing value
unless another copy is already in DUP reach. In this case the exact condition
reduces to `CopyReady`.

This prefix extension is an informal consequence of the preceding arguments.
It concerns a prefix that is fixed throughout the plan, not one that may move
temporarily and be restored later.

## What these results do not decide

These results decide whether all missing values can be generated. They do not
decide whether those values and the original slots can then be put in their
required final positions.

For a small example, set `D=1` and let `a` and `b` be distinct nonfree values:

```text
initial stack: [a,b]
missing values: [a]
generation plan: [a,b] --SWAP1--> [b,a] --DUP1--> [b,a,a]
prescribed final stack: [a,b,a]
```

Generation succeeds. Reaching the prescribed final stack under the same rules
is impossible. To duplicate `a`, it must first be at the top. After that
duplication, the bottom `b` is outside SWAP reach. This example allows exactly
the one demanded addition and no pops.

In particular:

- A fixed generation order is a different problem. The first example shows
  why initial reachability alone does not decide it.
- Generating all values before placement can bury slots that still need to
  move. A later permutation need not be reachable.
- A fixed assignment of source occurrences to target positions adds placement
  constraints. Treating equal values as interchangeable can change those
  constraints.
- Allowing POP changes the available plans. The necessity proofs above use
  the fact that stack length never decreases.
- BBU chooses when to generate and when to place a value. Its exact success
  condition remains `StaticSuccess`; it is not replaced by either generation
  condition here.

The reusable generation fact is smaller: **one reachable copy per still-needed
nonfree kind is enough, when the generation order is free.** The schedule must
preserve that resource until its demand is complete.

## Finite checks

A separate finite-state search checked the two conditions at limits `D=1,2,3`.
It covered 40,878 append-only cases and 156,996 cases with swaps, across 56
configurations. The cases varied source values, free values, and requested
multiplicities from zero through two. The search found no disagreement.

These checks use a mathematical model with smaller depth limits. They support
the arguments and check examples. The Lean theorems prove the append-only and
swap-generation equivalences for the repository's machine limits. Their axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`.
