# Build a trace from a birth plan

This construction starts with an empty source. It uses the production
reach of sixteen. The plan-to-trace result is proved in Lean. It does not
yet prove that a planner finds a global optimum or a factor-two result
against every input trace.

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

## Scope still to prove

Any physical trace assigns birth tokens to final positions. Each moved
token must take part in a SWAP, which suggests `E <= 2 * SWAPs`. Combined
with an assignment that minimizes `E`, this gives the proposed factor-two
movement bound for a fixed birth word. The trace-to-assignment link and
assignment optimizer are separate proof tasks. The weighted comparison
is proved conditionally by `realize_score_le_twice`: the planned birth
cost must be no greater than the other trace's birth cost, and the planned
`E` must be at most twice the other trace's SWAP count. A separate theorem
proves the same bound after subtraction of a supplied generation baseline.

An initial source needs more conditions. For example, changing
`[a,b,c]` to `[b,a,c]` has two moved positions but needs three top SWAPs.
The empty-source construction does not cover that entry cost.
