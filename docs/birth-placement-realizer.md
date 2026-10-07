# Build a trace from a birth plan

This construction starts with an empty source. It uses the production
reach of sixteen. The plan-to-trace result and a factor-two comparison
for a fixed ordered birth word are proved in Lean. The comparison does
not yet permit different birth orders or a nonempty source.

## The plan

Number the target positions from zero. A plan assigns each birth slot
`b` to one final position `f(b)`. The assignment is a permutation, so each
final position receives exactly one copy. The value born at slot `b` is
`target[f(b)]`. Equal values can use any assignment of their copies.

There are two conditions.

1. Each copy is born before its final position becomes unreachable:
   `b <= f(b) + 16`.
2. Each specified birth instruction is available. A direct instruction
   needs `Placement.Free`. A DUP at birth slot `b`, for value `v`, needs

   ```text
   count(v, births.take b) > count(v, target.take (b - 16)).
   ```

Subtraction on natural numbers stops at zero. The second count removes
the copies that must already lie below DUP reach. Thus the difference
counts the readable copies. This condition depends on the birth word
and the target, without a shadow stack.

`Plan` in `Shuffler/Optimality/BirthPlacement/Plan.lean` contains these
conditions and the chosen direct/DUP instruction for each birth.

## Start from a raw birth word

An input trace is not required to find a plan. `RawWord.Feasible` uses
only the spill set, target, and proposed ordered birth values. Its three
clauses are:

1. The birth word and target have equal multisets.
2. For every height `b` from zero through the word length,
   `target.take (b - 16)` is a submultiset of `births.take b`.
3. Before birth `b` of value `v`, either `Placement.Free spills v` holds,
   or `count(v, births.take b) > count(v, target.take (b - 16))`.

The first clause supplies exactly the required copies. The second clause
supplies each copy before its final position leaves SWAP reach. The third
clause permits either direct generation or a readable copy for DUP.
These are finite tests on the two input lists. There is no shadow stack.

`RawWord.feasible_iff_trace` proves that these clauses hold exactly when
there is a no-POP trace from `[]` to the exact target with that ordered
birth word. `RawWord.parse` returns a `Plan` and its word-equality proof
when the clauses hold; it returns `none` otherwise. It computes an
endpoint assignment with Hall matching. It does not search stack states.
The returned plan can use `Plan.cheapest` or `Plan.optimizeFixedWord`
before `realize` builds its production trace.

The raw-word tests replay the actual constructor. They include a birth
at its SWAP16 deadline, a birth one step too late, wrong counts, wrong
lengths, an unavailable variable, a spilled variable, and a wildcard.
They also check every pair of length-four words over two literal values.

## Place one new copy

After each birth, inspect the top copy's assigned final position.

- If that position is below the top, SWAP the copy into that position.
  Then inspect the copy brought to the top.
- If its assigned position is the top or is still above it, finish this
  stage and proceed to the next birth.

Every completed position contains its assigned copy. Every unfinished
copy at position `p` has an assigned destination greater than `p`.

The first SWAP after birth `b` is in range because of the birth deadline.
After that SWAP, the displaced copy has a destination greater than the
position just filled. It is therefore also in range. Each SWAP fixes one
position, so the stage terminates.

Before the next birth, every position below the readable suffix already
agrees with the target. Together with the number of copies born so far,
this proves the DUP availability formula above. The constructor selects
a readable physical copy only after this count proof establishes one.

After the final birth, an unfinished copy would need a destination above
its current position. A permutation cannot move every remaining copy
upwards. Thus all final positions are correct.

## The proved result

`realize plan` returns a production `Trace` from `[]` to the exact target.
It has no POP. It preserves the plan's ordered birth values and requested
direct/DUP instruction kinds, and introduces exactly its birth-word
multiset. `RealizedPlan.events` and `realize_births` prove these ordered
properties.

Its SWAP count is exactly

```text
number of moved assignment positions - number of nontrivial assignment cycles.
```

This is `Permute.Permutation.arbitrarySwapCount`. In particular, its SWAP
count is at most the number `E` of moved assignment positions.

`realize_score` proves the exact weighted cost: the sum of the specified
birth instruction prices, plus the SWAP price times this SWAP count.
`Plan.cheapest` replaces each specified birth instruction with the
cheapest available direct or DUP instruction. It preserves the assignment
and birth word, and cannot increase the chosen weighted cost. The result
also covers direct generation that is cheaper than DUP. A tie can select
direct generation even if it increases a cost component with zero weight.

The core interface is in
`Shuffler/Optimality/BirthPlacement/Realize/State.lean`. The tests run the
actual constructor and replay its operations. They cover an empty target,
equal copies, several SWAPs after one birth, DUP16, SWAP16, unavailable
direct generation, missing DUP parents, spilled variables, and wildcards.

## The fixed-word factor-two result

`traceAssignment` now computes the birth-token assignment induced by any
no-POP trace. It satisfies the endpoint deadlines and the value mapping,
and its moved-token count satisfies `E <= 2 * SWAPs`. For an empty source,
`tracePlan` also proves all birth availability conditions and preserves
the ordered birth events. These proofs are in the `TracePlan` modules.

`Plan.optimizeEndpoints` computes a compatible deadline assignment with
the least number `E` of moved positions. `Plan.optimizeFixedWord` combines
that assignment with the cheapest available instruction at each birth.
`optimizeTraceWord` extracts the word from an input trace, applies these
two choices, and builds a production trace.

For any no-POP comparison trace from `[]` to the same target, with the
same ordered birth values, the optimized trace satisfies

```text
optimized score <= 2 * comparison score
optimized score - B <= 2 * (comparison score - B).
```

Here `B` is the generation baseline for the target multiset. Scores use
the supplied gas and byte weights. Both inequalities are proved in
`FixedWord/Theorems.lean`, by `optimizeTraceWord_score_le_twice` and
`optimizeTraceWord_surplus_le_twice`.

The comparison trace can use any stack states, any SWAP sequence, any
direct/DUP choices, and any assignment of equal copies. It must have the
same ordered birth values. Thus the theorem does not fix the instruction
kind used to introduce each value.

The proof has three bounds. The other trace supplies an assignment with
at most twice its SWAP count in moved positions. The endpoint optimizer
uses no more moved positions than that assignment. The chosen birth
instructions cost no more than the other trace's birth instructions.
The realizer uses at most `E` SWAPs. These bounds give the total-score
inequality. The generation baseline is at most the other trace's birth
cost; subtraction gives the second inequality.

`Tests/OptimalityFixedWord.lean` replays the actual constructor. It checks
equal copies, direct generation cheaper than DUP, different birth
instruction kinds for the same values, spilled loads, wildcards, DUP16,
and SWAP16. It also checks every valid four-operation word over a
six-operation alphabet in gas-only and bytes-only modes.

## Scope still to prove

Choosing the ordered birth word remains a separate task. The proved
factor-two bound does not compare traces with different birth words.

An initial source needs more conditions. For example, changing
`[a,b,c]` to `[b,a,c]` has two moved positions but needs three top SWAPs.
The empty-source construction does not cover that entry cost.
