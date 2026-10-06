# Cost and optimality

Feasibility and optimality ask different questions. `Reserve` says when a
trace exists. A cost model must also state what each operation costs before
we can ask which trace is optimal.

The proposed model records both static gas and encoded bytes. It compares
production `Trace` values with the same source, concrete target, fixed spill
set, and exact addition multiset `H`. POP and extra temporary additions are
excluded. Generation uses the same restrictions but leaves the final order
free. Wildcard target choices and new spill allocation are separate problems.
No POP is a restriction on the comparison set, not an optimality claim.
These results do not show that an optimum over traces that allow POP always
has a no-POP representative.

The definitions are in [Optimality/Cost.lean](../Shuffler/Optimality/Cost.lean).
The tests are in [Tests/OptimalityCosts.lean](../Tests/OptimalityCosts.lean).
The [cost explorer](optimality-costs.html) compares example traces.

**Proof status:** the cost definitions and tests use the production trace
type. Lean proves addition of costs under trace concatenation, the gas-only
and byte-only specializations, and the implication from a weighted optimum
with two positive weights to a Pareto optimum. The generation formula and
the placement formulas below have paper
arguments and search checks. They are not yet Lean optimality theorems.
The existing [permutation theorems](../Shuffler/Permute/Optimality.lean) are
proved in Lean, but they fix an occurrence permutation.

## Gas and bytes

For the current DUP1–DUP16 and SWAP1–SWAP16 instruction set:

| Operation | Static gas | Encoded bytes |
| --- | ---: | ---: |
| SWAP or DUP | 3 | 1 |
| PUSH0 | 2 | 1 |
| PUSH with `w` data bytes, `1 ≤ w ≤ 32` | 3 | `1 + w` |
| LOAD through an address with `w` data bytes | 6 in the C++ estimate | `2 + w` |

LOAD expands to `PUSH address; MLOAD`. If the address uses PUSH0, its actual
static gas is 5. The C++ estimator still charges 6. The model gives these two
choices different names: `PrimitiveCosts.evm` and `PrimitiveCosts.cppEstimate`.
Both omit memory expansion.

MLOAD can increase the memory cost by
`C(newWords) − C(oldWords)`, where `C(w) = 3w + floor(w² / 512)`.
This depends on prior memory use and the allocated address. It is outside the
current stack state and outside this cost model.

References:

- [EIP-3855](https://eips.ethereum.org/EIPS/eip-3855#specification) specifies
  PUSH0, its 2-gas cost, and its lack of immediate data. It starts at Shanghai.
- [EVM Codes: MLOAD](https://www.evm.codes/#51) and
  [memory expansion](https://www.evm.codes/about#memoryexpansion) describe
  the base cost and the additional memory cost.
- [Geth gas constants](https://github.com/ethereum/go-ethereum/blob/master/core/vm/gas.go)
  and its [instruction table](https://github.com/ethereum/go-ethereum/blob/master/core/vm/jump_table.go)
  give the 3-gas PUSH, DUP, SWAP, and MLOAD base costs.
- [AssemblyItem::bytesRequired](../solidity/libevmasm/AssemblyItem.cpp)
  counts one byte for an ordinary opcode and `1 + width` for PUSH.
  [assemblePush](../solidity/libevmasm/Assembly.cpp) emits those bytes.
- [spill::Emitter::emitLoad](../solidity/libyul/backends/evm/ssa/spill/Emitter.h)
  emits the address PUSH and MLOAD.
- [stackOpsGas](../solidity/libyul/backends/evm/ssa/StackUtils.cpp) contains
  the C++ static gas estimate.

The C++ code has two different comparisons. The shuffler chooses between
its `Leave` and `Take` wildcard policies by `(spill-set size, operation count)`.
A tie keeps `Leave`. The operation count is the length of the abstract trace;
it counts LOAD as one operation. The join-layout chooser uses
`(spill-set size, summed static gas, stack size)` instead. Neither comparison
is a global search over traces, and neither directly minimizes encoded bytes.
See [Shuffler.cpp](../solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp),
[SpillSet.h](../solidity/libyul/backends/evm/ssa/spill/SpillSet.h), and
[StackLayoutGenerator.cpp](../solidity/libyul/backends/evm/ssa/StackLayoutGenerator.cpp).

Spill-set size counts distinct SSA values assigned spill storage. It is not
the number of LOAD operations. The results here keep that set fixed. They do
not trade a new spill allocation against a short local trace.

## Compare both costs

Let a trace cost be `(gas, bytes)`. A trace dominates another trace when it
uses no more gas and no more bytes, and at least one inequality is strict.
A Pareto-optimal trace has no eligible trace that dominates it.
`ParetoOptimal` and `WeightedOptimal` fix the concrete target.
`GenerationParetoOptimal` and `GenerationWeightedOptimal` compare traces
with any result stack, while retaining the same source, spill set, and `H`.
For example, generation with `H = 0` can use the empty trace. Placement with
`H = 0` can still require SWAPs to reach a different order.

For weights `g, b ≥ 0`, with at least one nonzero, the weighted score is

```text
g * gas + b * bytes.
```

This includes gas only, bytes only, and combined preferences. Natural-number
weights cover rational ratios by scaling. With both weights positive, a
weighted minimum is Pareto-optimal. With one weight zero, equal-score traces
can still differ in the ignored cost.

The full Pareto set contains more information than weighted minima. A
weighted sum can miss a Pareto point. For example, the abstract pairs
`(2, 10)`, `(7, 7)`, and `(10, 2)` do not dominate each other, but no positive
weighted sum selects `(7, 7)`. These pairs illustrate the distinction; they
are not claims about a particular shuffle.

With no POP and exact additions, every trace has exactly `|H|` generation
operations. Thus:

```text
abstract operation count = |H| + SWAP count.
```

A temporary Lean check proves this identity and the corresponding comparison
theorem. It does not make unit operation count equal to gas or bytes.
For the C++ static gas model, after replacing zero and junk DUPs with their
cheaper PUSH operations, the fixed part is `3|H| − cheapCount(H)`. The part
that remains to minimize is `3 * (SWAP count + LOAD count)`.

For bytes, the exact decomposition is:

```text
|H| + SWAP count
  + sum of PUSH data widths
  + sum over LOADs of (address width + 1).
```

The widths must be supplied by the cost model. The Lean spill set contains
identifiers, not allocated memory addresses.

## A finite formula for generation

This result leaves the final stack order free. It permits SWAP, DUP, PUSH,
and LOAD, with no POP and exactly the additions `H`.

Fix a scalar cost, for example a weighted gas-and-byte score. Let `d` be the
cost of DUP and `s` the cost of SWAP. Let `p(v)` be the cost to create value
`v` with PUSH or LOAD, without an existing stack copy. Set `p(v) = ∞` when
that operation is not available.

Define:

```text
base(v) = min(d, p(v))
r(v)    = max(p(v) − d, 0), with r(v) = ∞ if p(v) = ∞
B(H)    = sum over the copies in H of base(v)
A       = distinct demanded values v with r(v) > 0
W       = initial top 17 slots
D       = initial top 16 slots
Q       = sum of r(v) over v in A that do not occur in W.
```

`r(v)` is the extra cost to create a first copy instead of using DUP.
Values with `r(v) = 0` can always use their direct generation operation at
the baseline cost. Each value with `r(v) = ∞` must retain a source copy.
These infinite-price values are exactly the nonfree seeds used by the
existing feasibility predicate. Positive finite prices describe sources
that can be discarded, but only at a cost.

Each kind counted in `Q` needs one direct generation operation. After that,
DUP can supply its remaining copies. If `Q = ∞`, generation is impossible.

If every value in `A ∩ W` also occurs in `D`, the proposed exact minimum is

```text
B(H) + Q.
```

Otherwise there is one required value `x` that occurs in `W` but not in `D`.
It is the value at depth 16. This case requires a full 17-slot window.
For a position `j` in its top 16 slots, define:

```text
loss(j) = 0       if W[j] is not in A, or W has another copy of W[j]
          r(W[j]) otherwise.
```

The cost to handle this boundary is:

```text
R = min(
      r(x),
      s + loss(top),
      2s + min loss(j) over the other 15 positions
    ).

minimum generation cost = B(H) + Q + R.
```

The three choices have concrete meanings:

1. Create `x` later. Its initial copy can become unreachable.
2. Use SWAP16 now. This brings `x` to the top and leaves the old top at the
   bottom. Pay for that lost source if it is still needed.
3. Move another chosen slot to the top, then use SWAP16. This leaves that
   chosen value at the bottom. Pay for it if its source is lost.

All quantities refer to the initial stack and `H`. The minimum has at most
17 choices. It does not run a planner or use a recursively updated stack.
An infinite result agrees with the existing generation feasibility condition.

For combined C++ gas and byte weights, `d = s = 3g + b`.
A nonzero literal with width `w` has `r(v) = wb`.
A spilled variable with address width `w` has
`r(v) = 3g + (w + 1)b`.
Zero and junk use their cheaper direct-generation baseline `2g + b`.
An unspilled variable has infinite regeneration price.

**Paper lower-bound argument.** A value absent from `W` cannot enter DUP
reach through SWAP. Its first added copy must pay its regeneration price.
These are the independent charges in `Q`.
For the boundary value `x`, either some generation operation pays `r(x)`,
or its initial copy must move before any stack growth. If growth happens
first, that copy moves beyond both DUP and SWAP reach. To rescue it, another
initial top-16 occurrence must be left at the bottom. If that occurrence
was the top, at least one SWAP is needed. Otherwise at least two are needed.
After growth, a sole needed source left there requires regeneration. This
gives the three lower bounds in `R`.

**Paper construction.** Each finite choice in `R` is achieved with zero,
one, or two initial SWAPs. Then generate all remaining copies of the costly
kinds that still have reachable sources. This can use only DUP: before a
generation would remove the last reachable copy of a still-needed kind,
duplicate that copy. Otherwise duplicate any still-needed reachable kind.
This maintains a source for every remaining kind and consumes one demand
per step. Then handle each kind charged in `Q` or `loss`: generate it once
and DUP its remaining copies. Generate cheap kinds directly. The output
order is free, so all of these phases are permitted.

Thus an optimum has a representative with all SWAPs first, at most two
SWAPs, and at most one expensive direct generation per kind. Cheap values,
such as PUSH0 under a gas objective, can be pushed for every requested copy.
This phase statement is specific to generation. It is false for placement.

Search checks used shortest-path search over stacks and remaining demand:

- 10,500 unit-cost cases with DUP widths 1–3.
- 101,381 further unit-cost cases, including seed-count limits.
- 125,160 cases over all tested spill-set subsets, with cost SWAP + LOAD.
- 12,000 weighted cases with regeneration prices 0, 1, 2, 3, 7, 31, or
  infinity, and SWAP prices 1, 3, or 5.

These checks found no counterexample. They do not replace a Lean proof.

## Placement without a reach limit becoming active

There is also a graph formula when the final concrete stack has at most
17 slots. Assume the exact placement problem is feasible.

For every old position `i` where `S[i] ≠ T[i]`, add a directed edge
`S[i] → T[i]`. Parallel edges are retained. Let:

```text
m = number of these edges
E = values in T.drop(length(S)), together with the old top value if it exists
q = number of nonempty weak graph components that do not meet E
r = 1 if the old top is wrong and its edge lies on a directed cycle; 0 otherwise.
```

The proposed exact minimum SWAP count is:

```text
m + q − r.
```

An old wrong position requires a correction. Each component without an
available top value requires one entry operation. A cycle through the old
top saves one correction because one SWAP can correct both endpoints.
The construction follows directed trails through the components. This
allows equal-valued occurrences to exchange their assignments and allows
generation to occur between SWAPs.

The cost of required direct generation is independent of that construction
in this size range. Before any birth, the current stack has at most 16 slots,
so every existing value is within DUP reach. Each costly demanded kind absent
from the initial source needs one direct generation. Let their total
regeneration surcharge be `Qsource`. The weighted formula is then:

```text
B(H) + Qsource + s * (m + q − r).
```

This is a paper result with 71,381 checked small cases for the SWAP formula.
It is not yet a Lean theorem. The bound on final stack length is essential
to this proposed equality.

For the current EVM primitives, the same construction minimizes gas and
bytes together in this size range. For an existing value, DUP costs no more
than a positive-width PUSH or LOAD in either component. PUSH0 costs no more
than DUP in either component. A kind absent from the source is introduced
once. These choices can use the minimum-SWAP construction. Thus the proposed
short-stack result has one minimum cost pair, rather than a gas/byte tradeoff.

If `H` is empty, the same reasoning applies to the movable suffix even when
the whole stack is longer than 17. The frozen prefix must already match.
In the suffix graph, let `k` count the nonempty weak components. Its minimum
is `m + k − discount`, where the discount is 2 for a wrong top, 1 for a
correct top whose value occurs in the mismatch graph, and 0 otherwise.
For example, `[a, b, a] → [b, a, a]` needs two SWAPs. An occurrence assignment
that fixes the equal-valued top would instead need three.

## What remains for general placement

The graph expression remains a lower bound when stacks are longer. It does
not charge every movement needed to keep a value within reach during growth.

A second lower bound labels the original source occurrences. Choose any
injective, equal-value assignment of them to final target positions. Charge
an occurrence assigned from `i` to `j`:

```text
ceil(max(j − i, 0) / 16).
```

Sum these charges, then minimize over the assignments. Each SWAP moves at
most one original occurrence upward, by at most 16 positions. Thus every
trace needs at least that many SWAPs. Equal-value assignments must be free
to vary; fixing a supplied mapping can give a false lower bound.
The maximum of the movement bound and the value-graph bound is also a lower
bound. Their sum is not justified: one SWAP can contribute to both.

For example, a feasible problem `[a] → [b × k, a]`, with exactly `k` added
copies of `b`, needs `ceil(k / 16)` SWAPs when `a ≠ b`. Generate at most
16 copies of `b`, move `a` back to the top, and repeat. This attains the movement bound. The value
graph alone only gives one SWAP when `k > 0`.

Placement can trade SWAPs against LOADs. A checked example is:

```text
S = [a, b, 0 × 14]
T = [a, a, 0 × 14, c, b, a]
H = {a, a, c}; a and c are spilled; c is absent from S.
```

`DUP16; DUP1; SWAP16; LOAD c; SWAP2` uses two SWAPs and one LOAD: 18 gas.
A one-SWAP plan needs three LOADs: 21 gas. The sole `b` must move from
position 1 to position 17. With only one SWAP, that forces SWAP16 at length
18. The resulting birth order forces both copies of `a` to use LOAD.
At least one LOAD of `c` and one SWAP are necessary, and a one-SWAP,
one-LOAD plan is impossible. Thus the first plan attains the static-gas
minimum for this example.

Gas and bytes can also disagree. Let `a` be a 32-byte literal:

```text
S = [a, 0 × 15]
T = [a, 0 × 32, a]
H = {0 × 17, a}.
```

`PUSH0 × 17; PUSH32 a` has cost `(37 gas, 50 bytes)`.
`DUP16; PUSH0 × 16; SWAP16; PUSH0; SWAP1` has cost `(43 gas, 20 bytes)`.
The latter wins between these two traces when `g < 5b`; they tie when
`g = 5b`.

There is also a paper argument that these are the two Pareto cost pairs
for this example in the stated model. If the single added `a` uses PUSH32,
the 18 births already cost at least `(37, 50)` and the first plan attains it.
If it uses DUP, at least two SWAPs are necessary. With at most one SWAP, the
original `a` cannot move from position 0 to final position 33, so it must stay
at position 0. Its added copy must then be the first birth, at position 16:
one earlier birth would put the original beyond DUP reach. A single SWAP
cannot move that copy by the remaining 17 positions. The second plan attains
the resulting lower bound `(43, 20)`. Replacing a zero PUSH0 with DUP adds
gas without saving bytes. This frontier argument is not yet proved in Lean.

The current complete planner proves feasibility. It does not minimize any
of these costs: even `[1, 2] → [1, 2]` can emit two cancelling SWAPs through
`placeExisting`, while the empty trace has cost zero.

Allowing POP and replacement additions can also change the optimum for the
same endpoints. For `[1, 2, 0] → [2, 1, 0]`, `Reserve` holds with `H = 0`.
A no-POP trace needs three SWAPs, costing `(9 gas, 3 bytes)`.
`POP; SWAP1; PUSH0` costs `(7 gas, 3 bytes)`. Its additions are `{0}`, so it
is outside the fixed-`H = 0` comparison set. This example shows a gas benefit
from POP when replacement additions are allowed. It does not refute any
fixed-additions optimality statement.

A single finite formula for the full Pareto set, or for every weighted
optimum at arbitrary stack height, remains open here. The generation
formula, the short-stack placement formula, the lower bounds, and the
counterexamples give parts of that problem without assuming that a BBU
choice is optimal.
