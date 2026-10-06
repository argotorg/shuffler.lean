# A reserve condition for generation and placement

For code review, start with
[Feasibility/Spec.lean](../Shuffler/Feasibility/Spec.lean). It contains the
actual predicate definitions and all four public statements together.
The [review guide](feasibility-review.md) explains what to check.

When growth is required and the source has at least 17 slots, the core
condition is a multiset containment:

> **The current top 17 slots must contain one copy of the next value to be
> fixed, plus one copy of each distinct nonfree kind that still needs to be
> generated.**

If the next fixed value is also one of those needed kinds, this requires two
copies of that value. One copy is for its final position; the other is a source
for DUP.

This is a condition for the existence of a plan. It does not characterize the
choices made by the current BBU implementation.

**Status: proved in Lean.** The public theorem
[`canPlace_iff_reserve`](../Shuffler/Placement/Theorems.lean) proves both
directions. Its witnesses are actual production `Trace` values. The proof
constructs a plan directly; it does not assume that the current BBU choices
succeed. A separate proved theorem covers wildcard target patterns.

## The exact problem

We are given:

- An initial stack `S`, written bottom first.
- A required final stack `T`.
- A multiset `H` of exactly the values that may be added.
- A fixed spill set.

A plan can use the current machine's SWAP, DUP, PUSH, and LOAD operations. It
must add exactly `H`, in any order. It cannot use POP or extra temporary
additions. Its final stack must equal `T`. In
[`CanPlace`](../Shuffler/Feasibility/Spec.lean), `trace.noPop` excludes POP and
`trace.additions = H` counts the actual DUP, PUSH, and LOAD results.

Equal values are interchangeable. The plan does not have to preserve a given
assignment of individual source occurrences to target positions, or a given
set of hole positions. Equality is exact `Value` equality, including for
wildcards.

Here `T` is an exact result stack, not a wildcard pattern. For a valid BBU
state, use `S = state.stack`, `H = multiset(state.missingValues)`, and
`T = state.expectedStack`. Thus `S` is the current stack, not the type-level
original source of the state's trace. A bound wildcard target retains its
assigned source value in `expectedStack`. The raw BBU target need not have the
same value multiset. It can be used as the exact `T` when the assigned source
and target values are equal. See
[`State.expectedStack`](../Shuffler/BuildBottomUp/Defs.lean).

For a wildcard pattern `P`, the exact proved condition is instead:

```text
Some no-POP trace from S has a result matching P
↔
There exist a concrete result E and an addition multiset H such that
  StackMatches E P and Reserve spills S E H.
```

See
[`exists_matching_trace_iff_reserve`](../Shuffler/Placement/Compatibility.lean).
`StackMatches` requires equal lengths. Each pattern slot either is a wildcard
or equals the actual value at that position. Both `E` and `H` are chosen by
this condition. It does not fix the values at wildcard positions in advance.

With a compatible BBU mapping, `expectedStack` is one such matching result.
Compatibility means each bound source value matches its target slot; a
wildcard target slot can match any value. Reserve for that chosen result is
sufficient for a matching plan. Failure for that chosen `E` and `H` does not
rule out a plan for another matching result. See
[`expectedStack_matches`](../Shuffler/BuildBottomUp/Compatibility.lean).

The limits are those in [Basic.lean](../Shuffler/Basic.lean): DUP reads the top
16 slots, while SWAP can move any of the top 17 slots. The operations are
defined in [Trace.lean](../Shuffler/Trace.lean).

## A single predicate on the initial data

Let:

```text
n = length(S)
f = max(0, n − 17)
W = S.drop(f)
```

Thus `W` is the initial top 17 slots, or the entire source if it is shorter.
The first `f` source positions are already outside SWAP reach.

A value is `Free` if it can be pushed or loaded. Form a multiset `N` containing
**one copy of each distinct nonfree value in H**. Repeated requests for the
same value contribute only one member to `N`.

Define the boundary reservation `B`:

```text
B = [T[f]]   if H is nonempty and n ≥ 17
B = []       otherwise
```

The index `T[f]` exists in the first case under the size balance below.

The proved exact condition is:

```text
multiset(T) = multiset(S) + H
and
T.take(f) = S.take(f)
and
B + N ≤ multiset(W).
```

Here `+` adds multiplicities. The relation `≤` compares the count of every
value. It therefore reserves separate copies when the two requirements name
the same value.

These are finite checks on the initial source, target, missing values, and
spill set. They do not execute BBU, choose a generation order, or update a
shadow stack.

### Read the three clauses

1. **The counts match.** The final values are exactly the original values plus
   the allowed additions.
2. **The part that cannot move is correct.** Those initial bottom positions
   stay fixed throughout a plan with no POP.
3. **The working region can supply both jobs.** It can fix the next bottom
   position and retain the sources needed for later generation.

The small and empty cases are part of the definition:

| Case | Meaning of the reserve clause |
|---|---|
| No missing values | `B` and `N` are empty. This leaves the usual permutation condition. |
| At most 16 initial slots | `B` is empty. Each needed nonfree kind only needs one initial copy. |
| At least 17 initial slots, with growth required | Reserve the next fixed target value and all required DUP sources together. |

## Why the condition is necessary

Each addition contributes its specified value, swaps preserve all counts, and
there are no pops. The multiset balance follows.

The initial first `f` positions are beyond SWAP reach. Stack length never
decreases, so those positions never become reachable. They must already equal
the target prefix.

A required nonfree value must have an initial source. A value whose last copy
is lost cannot be created by DUP, PUSH, or LOAD. In particular, a copy below
the initial working region cannot supply a new value: swaps cannot reach it,
and growth only makes it deeper.

If the source has at least 17 slots and some growth is required, consider the
**first append**. Before that append, only swaps have occurred. They can only
permute `W`. The append moves position `f` to depth 17, beyond all later SWAP
reach. It must therefore already hold `T[f]`.

That reserved slot is at depth 16 immediately before the append. DUP cannot
read it. If it were the only working copy of a nonfree kind still to be
generated, the first append could not duplicate it, and no later append could
recover it. Every needed nonfree kind must therefore have a separate copy in
the other 16 working slots.

This is exactly `B + N ≤ multiset(W)`.

## Why the condition is sufficient

First suppose some growth is needed and the source has at least 17 slots.

Use swaps to put the reserved `T[f]` at position `f`. Keep one copy of every
kind in `N` in the other 16 working slots. The multiset containment ensures
that these choices use separate occurrences where required. Swaps with the
top can perform any permutation of this 17-slot region.

The first `f+1` positions now have their final values. Exactly 16 current slots
remain above that prefix. Each missing value is free or has a DUP source in
those slots. The proved
[`Reserve.prepare`](../Shuffler/Placement/Prepare.lean) constructs this
preparation trace.

The direct completion proof,
[`canPlace_complete`](../Shuffler/Placement/Completion.lean), now fills the
target from bottom to top. At every stage it keeps a correct fixed prefix,
at most 16 working slots, and one source for each remaining nonfree kind.
Let `y` be the next target value.

1. **If `y` is still in the missing multiset, generate it now.** A free value
   can be pushed or loaded. Otherwise the retained seed permits DUP. The
   working region has at most 17 slots after this append. Swaps put the new
   `y` next to the fixed prefix. The previous working values remain above it,
   so all needed seeds remain available. Remove one `y` from the demand.
2. **If `y` is not missing, use an existing working occurrence.** The count
   balance guarantees one is present. Swaps put it next to the fixed prefix.
   Remove that occurrence from the working region. No needed seed is lost:
   `y` is not among the values still to be generated.
3. **Extend the fixed prefix by that one value and repeat.** The target tail
   gets shorter at each step. When it is empty, the count balance says the
   working region and missing multiset are both empty.

The construction uses actual `Trace` operations with no POP. It generates
exactly the requested multiset. The initial predicate is still non-recursive;
only the proof that a plan exists uses this recursive construction.

If the source has at most 16 slots, the same completion proof starts with an
empty fixed prefix. All required seeds are already within DUP reach. No
preliminary boundary reservation is needed.

If `H` is empty, no growth is needed. The initial frozen prefix is correct,
and the remaining top 17 slots have the right multiset. Swaps can put that
region in the required order.

The no-growth construction is
[`canPlace_perm_of_take_eq`](../Shuffler/Placement/Permute.lean). All three
cases are joined in
[`Reserve.canPlace`](../Shuffler/Placement/Sufficiency.lean). The reverse
direction is
[`CanPlace.reserve`](../Shuffler/Placement/Necessity.lean).

## An impossible case that passes both initial reach checks

Let `a, b1, …, b16` be 17 distinct variables. None is spilled.

```text
S = [b1, …, b16, a]
H = [a]
T = [a, b1, …, b16, a]
```

The missing `a` is at the top, so the generation-only `Ready` check passes.
Every initial slot is also within SWAP reach.

But `B=[a]` and `N=[a]`. Their sum requires two copies of `a` in `W`, which
contains only one. The reserve condition fails.

Putting that one `a` at the bottom before growth makes it unavailable to DUP.
Duplicating it first freezes the wrong bottom value. No plan with exactly the
specified addition and no POP can reach the target. This follows from the
proved equivalence and is checked in
[`Tests/PlacementFeasibility.lean`](../Tests/PlacementFeasibility.lean).

This obstruction is not just a BBU choice. In fact, a separate mathematical
argument rules out even plans with POP and extra temporary additions here:

1. All 17 nonfree kinds must remain present throughout. Once the last copy of
   one is lost, no operation can recreate it. Stack length therefore stays at
   least 17.
2. Take the last transition from length 17 to length 18 before the final
   stack. Immediately before it, there is exactly one copy of each kind.
3. After that transition, length never returns to 17. Position 0 stays frozen
   and must already contain `a`.
4. The transition cannot duplicate this depth-16 `a`. The sole `a` becomes
   frozen outside both reachable regions, so a second `a` can never be made.

This stronger impossibility argument is informal, not a Lean theorem.

## A possible case that the current BBU choices reject

```text
S = [0, …, 0, 1]       (sixteen zeros, then 1)
H = [1]
T = [1, 0, …, 0, 1]   (sixteen zeros between the two ones)
```

The missing literal can be pushed. Thus `N` is empty, `B=[1]`, and the source
contains the required reservation. The condition passes.

A legal plan is:

```text
SWAP16; PUSH 1
```

It puts the existing `1` at the bottom, then adds the other `1` at the top.

With the particular initial mapping `i ↦ i+1`, target position 0 is the only
hole. The current BBU implementation tries to generate its value first and
returns `.blocked 1`. That BBU result, the mapping's validity and exact value
bindings, and the successful explicit `Trace` are all checked in
[`Tests/PlacementFeasibility.lean`](../Tests/PlacementFeasibility.lean).

This example explains the scope distinction: the reserve condition concerns
the existence of a value-correct plan. `StaticSuccess` concerns the result of
the current BBU function on its supplied state and mapping.

## Evidence and limits

The public placement and wildcard-pattern equivalences compile in Lean. An
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; it
reports no `sorryAx`.

The focused Lean tests cover empty sources, absent variables, spills,
repeated demand, exact counts, wildcard matching, the 16/17-slot boundary,
a wrong frozen prefix, suffix permutations, and the BBU gap above. They use
the production definitions and actual traces.

A finite search compared the reserve condition with exhaustive full-stack
reachability for 9,588,891 target cases across 62,495 configurations. It used
DUP limits 1 through 3, SWAP limits of the same number, up to four value kinds,
source lengths up to five, and at most four missing occurrences. It found
zero disagreements. An earlier formulation using all target-prefix deadlines
gave the same answers.

These finite checks are supporting evidence from a mathematical operation
model. The Lean theorem proves the equivalence for the machine limits in the
repository. No further cases are hidden in an execution predicate: the
condition is the initial multiset reservation stated above.

The operation restrictions matter. POP can expose a previously frozen prefix,
and extra temporary additions change the multiset problem. A fixed assignment
of individual copies to positions is also a different problem. The exact
condition here is for the stated values, exact additions, arbitrary legal
swaps, and no pops.

For the separately proved generation-only result, see
[generation-feasibility.md](generation-feasibility.md) or its
[visual explanation](generation-feasibility.html).
