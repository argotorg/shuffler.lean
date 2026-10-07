# Target-order optimality and surplus bounds

The existing `Schedule.appendCandidate` and `Schedule.build` have a proved
cost guarantee for an empty source. Every target value must have a legal
direct introduction. There is no limit on target length or multiplicity.
No production algorithm changes are required.

Let

```
u = DUP score
s = SWAP score
d_v = direct introduction score for value v
p_v = d_v - min(u,d_v)
B = generation baseline
Q = GapCost.bound from the empty source to the target.
```

For consecutive equal-value target positions `before,next`, `Q` contains

```
min(p_v, s * floor((next-before-1)/16)).
```

A gap at most 16 contributes zero. A longer gap contributes at least
`min(p_v,s)`. The first occurrence has no gap charge: its introduction
cost is already in `B`.

The existing lower-bound theorem gives `B+Q <= score(other)` for every
eligible trace. Eligibility here fixes the empty source, exact target,
and exact additions, and excludes POP.

For any natural number `rho>=1`, assume every target value satisfies

```
p_v <= rho*s.
```

The new trace theorem constructs a trace with no SWAP and proves

```
score(target-order trace) <= B+rho*Q.
```

At each target position, use the cheaper of direct introduction and DUP
if a copy is readable. Otherwise use direct introduction. For a repeated
value outside DUP16, the extra direct cost is at most `rho` times the new
capped-gap charge. The proof follows append steps and sums the existing
per-value gap measure.

The executable append candidate selects the cheapest legal generation
operation at each step, so its score is no greater than this trace. The
scheduler retains a candidate whose score is no greater than the append
candidate. Thus both satisfy

```
score(result)-B <= rho*(score(other)-B)
```

for every eligible `other` trace. This also holds for `buildWith` with any
strategy list, including the empty list.

When `rho=1`, the result is exactly weighted optimal. When `rho=2`, its
cost above the baseline is at most twice the least possible cost above
the baseline. The factor applies to this difference, not only to total
cost.

## Gas-only EVM and C++ models

For both supplied models, DUP and SWAP cost 3 gas. PUSH costs 2 or 3 gas.
In `PrimitiveCosts.evm`, LOAD costs 5 gas for a PUSH0 address or 6 gas for
another address encoding. In `PrimitiveCosts.cppEstimate`, LOAD always
costs 6 gas. Every direct-over-DUP premium is therefore at most 3 gas.

The ratio-one condition holds for every target in both gas-only models.
Consequently the existing scheduler returns a gas-optimal trace from an
empty source whenever every target value can be introduced directly.
This is a theorem for the repository's static cost model, which does not
include memory expansion or spill-store costs.

## Boundary and negative checks

`Tests/OptimalityTargetOrder.lean` checks the actual append candidate,
including DUP16 versus a gap of 17, repeated long gaps, and PUSH0 rather
than DUP. The tests also instantiate the scheduler optimality theorems for
arbitrary EVM encodings, the C++ model, and the empty target.

The byte-cost boundary uses a spilled variable around sixteen PUSH0
values. A PUSH1 address makes the LOAD premium 2 bytes and SWAP cost
1 byte. The append score is 22, baseline is 20, and `Q=1`, attaining the
ratio-two upper bound. With a PUSH2 address, the premium rises to 3. The
append score is 24, baseline is 21, and a checked one-SWAP trace costs 22.
Thus the append surplus 3 exceeds twice that competitor's surplus 1.
The premium condition cannot be removed.

The tests reject a hard value absent from an empty source and cover a
zero-SWAP-price case with zero premiums.

## Lean APIs

- `GapCost.targetOrder_trace_bound`
- `Schedule.appendCandidate_gapCost_bound`
- `Schedule.buildWith_gapCost_bound`
- `Schedule.appendCandidate_surplus_le`
- `Schedule.buildWith_surplus_le`
- `Schedule.appendCandidate_weightedOptimal_of_premium_le_swap`
- `Schedule.buildWith_weightedOptimal_of_premium_le_swap`
- `Schedule.build_weightedOptimal_of_premium_le_swap`
- `Schedule.build_evm_gas_weightedOptimal`
- `Schedule.build_cpp_gas_weightedOptimal`

The focused test build checks all proofs. Axiom reports for the trace,
surplus, and two gas-optimality theorems list only `propext`,
`Classical.choice`, and `Quot.sound`.
