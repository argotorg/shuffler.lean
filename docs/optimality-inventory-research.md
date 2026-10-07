# Inventory and flow research

This note records a proposed abstraction and the proved lemmas below.
The global introduction-cost lower bound is now proved for normalized
no-POP production traces. Constructive plan realization and its SWAP bound
remain open. The results do not establish a general approximation ratio.

At a stack height of at least17, the next birth freezes one old position.
Let `bag` contain the current top17 values. Let `b` be the target value at
the position about to freeze, and let `v` be the next birth. A necessary
transition is:

```
b belongs to bag
rest = bag - {b}
v is free to introduce, or v belongs to rest
bag' = rest + {v}
```

The residual condition matters. The removed boundary position is at depth17
before the birth, so it cannot serve DUP. A sole hard copy at that position
cannot both become the fixed output and supply the new copy.

Each transition can be implemented by placing `b` with at most two swaps,
then generating `v` from the16-value residual suffix or directly. The last
bag can be arranged by the proved no-growth solver. Conversely, each legal
no-POP production trace gives such bag transitions when split at births.
For heights below17, a birth does not freeze a position yet. These statements
describe a possible feasibility proof; that proof has not been added.

The abstraction loses physical swap cost. For example, the existing carry
test starts with `[a,0×15]` and ends with `[a,0×32,a]`. Its generation baseline
is18 one-byte births. A legal trace reaches that baseline plus two swaps.
The bag retains an `a` copy through the gap without charging those swaps.
Longer gaps require further upward movement while abstract residency stays
continuous. Thus a minimum generation-cost bag path is not a lower-bound
model that can by itself support a factor-two excess proof.

A cache with one slot per value kind also loses copy conservation. Suppose
the source contains16 old tokens, `v` is absent, and the target is
`[v,v]` followed by those16 old tokens. The exact additions are `{v,v}`.
After the first `v` is fixed, all16 old tokens still occupy the readable
window. No active copy of `v` remains. The second `v` needs another direct
introduction. A cache model that keeps `v` after its output would have kept
a copy that the physical stack does not contain.

A faithful flow model would need all of these constraints:

- Each target output consumes one active copy.
- Each birth round inserts exactly one copy from the fixed additions.
- Old copies cannot be discarded before their target outputs.
- DUP needs an overlapping active copy after the boundary output.
- A retained copy needs upward transport as its old position leaves reach.
- The birth order is chosen, rather than being a fixed request sequence.

These conditions go beyond the usual fixed-request interval cache problem.
A possible next step is an interval model that prices upward transport and
tracks copy counts. It would then need a construction whose swap cost is at
most twice a proved joint lower bound. Separate charges for old mismatches
and transport can count the same swap, so adding them is insufficient.

## A restricted interval bound

The following is a proof plan for one input family. Window lemmas and a
conditional finite-interval cost theorem are proved in Lean. The full
production-trace transfer is not proved yet. The proposed result bounds
generation cost. It does not prove a scheduler approximation factor.

Let both reach limits be R. Let the source contain q old copies, with
`q ≤ R`. Let the target be `P ++ U`, where U is a permutation of the whole
source and no value in P occurs in the source. The additions must be exactly
the multiset of P. Thus no old copy is added or removed, and all q old
copies are still needed after the whole fresh prefix P. In the production
system, R is 16.

For each value v in P, join each occurrence of v to the next occurrence of
v. A pair of positions i < j gives the half-open interval `[i,j)`. The
interval crosses the cuts just after outputs i through j−1. A selected
interval means that a v seed is retained after output i until output j.
The capacity at each cut is `C = R−q`.

Here is the proposed reduction from a production trace.

1. Before each birth that freezes a position, emit that position's target
   output and remove it from the current 17-value bag. The residual bag has
   16 values. This is the exact DUP-readable suffix: the emitted boundary
   copy itself is outside DUP reach.
2. At the end of the trace, emit the remaining fresh outputs in target
   order by virtual deletion from the final window. These are proof events,
   with no production operations. After the first such output, at most R
   values remain. This includes the final two fresh outputs in the q=R−1
   family; they must not be omitted from the interval model.
3. Select a consecutive-v interval if a v copy remains in the residual bag
   immediately after its first output. Intervening outputs have other
   values. No POP occurs. Thus this v copy cannot leave the active bag before
   the next v output. The trace may move it or add more copies.
4. All q old copies remain in every such bag until the fresh prefix ends.
   At most R−q different selected intervals can cross a cut. Intervals of
   the same value do not overlap, so each crossing interval needs a distinct
   active copy.
5. An unselected interval has no v copy after its first output. A later DUP
   cannot create the first new v copy. Thus the interval requires a direct
   introduction before its next v output. For each v these time periods
   are disjoint. Since v was absent initially, its first output also requires
   a direct introduction.

The intended Lean proof must make the emission events precise and show
that these bags are the trace suffixes just described. The key count is

```
directCount(v) ≥ occurrences(P,v) − selectedIntervals(v).
```

Prefetching does not invalidate this count. A prefetched copy helps only
when it is still in the bag after the earlier output is consumed. Virtual
terminal deletions cannot introduce a new value, so an unselected terminal
gap cannot occur in a valid final stack.

Let `premium(v) = directPrice(v) − unitPrice(v)`, the same nonnegative
premium used by `GenerationSurcharge`. Give each v interval this weight.
Let E be all the intervals, and let M be the maximum total weight of a
subset with at most C crossings at each cut. The proposed premium floor is

```
sum(interval ∈ E, premium(interval.value)) − M.
```

Baseline already pays the first direct introduction of each fresh kind.
Every deleted interval pays for a later direct introduction. If the trace
reduction is proved, the existing surcharge theorem lets this premium floor
be added to an unconditional SWAP-cost floor. It must not be added to a
bound that already charges these same introduction premiums.

For C=1, M is the usual maximum-weight set of disjoint intervals. For fixed
larger C, a minimum-cost flow formulation could compute M. This note does
not establish a runtime bound or implement that solver.

For `P = (a,b)^k` and q=R−1, all 2k−2 intervals have length two. Capacity
one permits at most k−1 of them; taking all consecutive-a intervals attains
that number. Therefore the proposed count floor is k+1 introductions.
With equal premium p, the later-introduction floor is `(k−1)*p`.
At k=8, LOAD width32 gives p=33 bytes. The floor is231. The proved SWAP
floor is15, and baseline is82, so the sum is328, equal to the exact oracle
and the current production scheduler. The interval part is not yet a Lean
certificate of this equality.

A bounded search checked1134 inputs: equal reach limits1,2,3; every q from
zero through R; every nonempty binary fresh prefix of length at most6; and
q copies of an old zero value in the source and target suffix. In each
case, exhaustive reachability with fewer introductions than the proposed
interval floor was impossible. The searches visited23988 states in total.
Evidence and the checking script are `/tmp/collective-interval-check.json`
and `/tmp/check-collective-intervals.mjs`. Separate production-cap exact
searches for k=2,3,8 are saved in
`Bench/evidence-collective-introductions.json`. These finite checks do not
replace the missing trace-reduction proof.

## Current Lean proof boundary

`Collective.TraceCuts.split_at_birth` splits an actual no-POP production
trace at any intermediate birth height and retains its exact operation
order. `Collective.HeightCut.takeHeight` constructs the last trace prefix
at a height limit. Its theorems prove exact re-concatenation, no POP on both
parts, the prefix height, and equality of target positions below the output
cut. It includes the virtual final-output case.

`real_cut_oldCount` and `virtual_cut_oldCount` prove the residual-window
statements for the disjoint fresh-prefix family. `freshKinds_card_le` proves
that a residual with at most16 slots and q old copies has at most16−q fresh
kinds. `exists_output_residual` obtains such a window for every nonempty
fresh-output cut. Tests use the production complete constructor and cover
the two real cuts and two virtual cuts of a four-birth fixture.

`Collective.Intervals` defines consecutive-value intervals and their cut
capacity. Its `interval_floor_le_later_direct` theorem assumes a feasible
selected set, a checked upper bound on saved interval weight, and the
per-value inequality `occurrences−directCount ≤ selectedCount`. It then
proves the weighted later-introduction floor. `capacityMaximum` is a finite
specification over subsets; production planning does not evaluate it.

`Collective.Inventory` defines the global mandatory multiset
`source − target.take(c)`. Its theorems prove that this multiset is contained
in the residual of every no-POP production trace. A paid reuse interval
starts after the source-count-th output of its value. Its retained seed
therefore needs a slot beyond the mandatory inventory. The proved capacity
inequality is `mandatory.card + crossingPaidIntervals.card ≤ 16` at every
positive output cut, for source length at most17. It includes repeated
source values and the virtual final cuts.

`Collective.HeightRelations` proves that height cuts are nested, and that a
residual value remains present until its next output. `Collective.TraceDirect`
proves that a value absent from a residual needs a new PUSH or LOAD before it
can appear again. It also localizes this strict direct-count increase between
two output cuts.

`Collective.Retention` now constructs one set of retained paid intervals
from each production trace. Its `retained_capacity` theorem proves the global
capacity inequality without a residency assumption. Its
`unretained_direct_increase` theorem proves a strict direct-count increase
between the start and stop output cuts of each omitted paid interval.
`Collective.Counts.omitted_count_le` sums these disjoint intervals by an
injection into direct-count levels. For each value v, the omitted count is
at most `directCount(v) − (if v belongs to source then 0 else 1)`. Thus the
first introduction of an initially absent value stays within baseline.
The omitted interval weight is at most the proved generation surcharge.

`Collective.InventoryBound` defines feasible paid sets, an upper bound on
saved weight, and a finite maximum over feasible subsets. The maximum is a
specification; no production planner evaluates it. The checked score theorem
for every no-POP trace with source length at most 17 is:

```
baseline + swapPrice * trace.swapCount +
  (paidIntervalWeight − maximumFeasibleSavedWeight) ≤ traceScore.
```

The abstract upper-weight certificate variant avoids subset enumeration in
proof clients. Tests establish a 33-byte floor for two overlapping fresh
intervals, a 66-byte floor for three alternating pairs, the extra seed slot
after one old output, and a paid interval of a source-present value.

`Collective.DeadlineCounts` proves the exact finite identity
`dueJobs + source.length = cut + mandatory.card + crossingPaid.card`.
Its signed deadline condition is equivalent to the inventory sum constraint.
Tests cover duplicate source values, advanced deadlines, the height-17
boundary, unpaid intervals, and empty stacks. Constructive plan realization,
its SWAP bound, and global factor two remain open.

The initial Reserve boundary condition still matters. At source height17,
a fresh first output would leave17 mandatory copies. Truncating
`16−mandatory.card` to zero loses that failed constraint. Tests cover this
case, repeated source values, paid and unpaid intervals, real and virtual
cuts, and a production constructor that reloads both omitted fresh intervals.
Transport cost must enter the plan objective because a retained seed can
cost more SWAPs than another introduction.

## Retention and transport refinements

`retainedWithoutDirect` removes paid intervals that contain a direct
introduction between their output cuts. The subset still satisfies capacity.
Its omitted count and weight have the same introduction-cost bounds as the
original retained set. A production replay test has a resident a seed plus
an extra LOAD in its first a interval. The refined set removes that interval
and keeps the following interval. This supplies a trace-to-plan interface
for future joint transport work; it is not a transport theorem for the gaps.

`UnitSchedule` constructs a deadline-feasible order by merge sort. It proves
that the unit-job capacity condition is equivalent to existence of such an
order. `InventoryOrder` applies the result to a feasible paid-interval set.
It does not prove that the order has a stack realization or the required
SWAP cost. Fixed deadline orders can have different least SWAP costs.

`Transport.Sparse` sums prefix surplus at cuts with one residue modulo 16.
One legal SWAP can cross at most one such cut. The sum is bounded by the
actual upward SWAP count for that value. The maximum over all 16 residues
has the same bound. For source `value^q`, target `fresh ++ value^q`,
`value` absent from `fresh`, and `q ≤ 16`, Lean proves:

```
q * (fresh.length / 16) + min(q, fresh.length % 16)
  ≤ upwardCount(value).
```

The selected residue is `q−1`. For four old copies and eight fresh outputs,
this bound is four SWAPs; rounding total distance divided by 16 gives two.
Tests check the formula for every q from 0 through 16 and fresh length from
0 through 33. The per-value gap transport bound and its disjoint combination
with old-copy transport remain open.
