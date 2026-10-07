# Old-copy and retained-gap movement

The Lean module `Collective.GapTransport.Theorems` proves a joint movement
lower bound. It uses production traces with no POP, a fixed spill set, and
at most 17 source entries. It makes no assumption about birth order.

For a consecutive equal-value interval from target position `i` to `j`, set

```text
gap demand = floor((j - i - 1) / 16).
Q(P)       = sum of gap demands in selected set P.
M          = sum over target values of sparseRequiredSwaps(value, source, target).
```

`M` measures movement of the original source copies. It uses the existing
sparse prefix-surplus bound. `Q` measures later retained copies. A selected
interval is paid when the target prefix through `i` has already consumed at
least the source count of its value. It is resident when its value remains
above that prefix at the height cut `i + 17`.

The joint theorem states:

```text
M + Q(P) <= actual SWAP count
```

It holds for any selected set whose intervals are paid and resident. Both
`retained trace` and `retainedWithoutDirect trace` satisfy these conditions.

## Why a retained gap requires movement

At the start cut, the stack contains an extra copy of the interval's value.
Its height is at most `i + 17`. The target contains no further copy before
position `j`. Thus each cut at `i + 16`, `i + 32`, and so on, below `j`, has
at least one surplus copy in the initial prefix. The final target prefix
has no such surplus.

A birth cannot decrease this surplus. This includes a DUP made for a later
output. A SWAP moves at most 16 positions, so it can decrease surplus at
only one of these cuts. This proves the per-gap bound against upward SWAPs
between the gap's two height cuts. The proof does not need to assume that
the gap contains no direct introductions.

Intervals for the same value have disjoint time ranges. Their charges use
disjoint levels of that value's upward-SWAP counter. A SWAP has only one
lower value, so summing across values does not count one SWAP twice.

## Why the old-copy and gap terms add

Once a target prefix has consumed all source copies of a value, the initial
source surplus is zero beyond that prefix. The entire sparse old-copy
demand is therefore charged by this output cut. Every paid interval of the
same value starts at or after that cut. Its movement charges occur later.
This separates old-copy work from retained-gap work.

The production test has source `[a]` and target `b^17, a, c^16, a`. Its trace
has two old-copy SWAPs and one later retained-gap SWAP. Lean computes `M=2`,
`Q=1`, and three SWAPs. Another test creates two future `a` copies before
their outputs and still satisfies the movement theorem.

## Joint weighted cost

The introduction premium is direct weighted price minus the baseline unit
price. Define the plan cost as

```text
J(P) = sum of premiums for omitted paid intervals + SWAP price * (M + Q(P)).
```

Lean proves, for every permitted primitive-cost model and weight pair,

```text
baseline + J(retainedWithoutDirect trace) <= trace weighted score.
```

The selected set is also proved feasible: mandatory source inventory plus
crossing selected intervals uses at most 16 slots at each positive cut.
`exists_feasible_jointPlan` combines the feasibility and cost results.

This is a trace-to-plan lower bound. It does not construct a trace from an
arbitrary feasible plan. It does not prove a factor-two approximation.
Displaced values and placement cycles can require work that the sparse
movement count does not measure. A plan-to-trace upper bound needs a
separate proof and may need a stronger objective.
