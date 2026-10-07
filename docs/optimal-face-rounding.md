# Prefix rounding on a priced assignment face

This note concerns the empty-source endpoint cost `E`, with one positive
identity reward `s`. It does not extend the result to the source cost
`W=E+interiorEdges`. It gives Lean proofs of local price facts, a paper
proof for assignments with the same fixed positions, and named finite
checks of two open rounding claims.

Let `A(i,v)` be the sum of the nonnegative canonical gap prices for value
`v` whose cuts are at least birth row `i`. A feasible assignment has
`i <= f(i)+R`. The fixed-price oracle maximizes

```
s * numberOfFixedRows(f) + sum_i A(i,target[f(i)]).
```

Its dual prices satisfy

```
alpha_i + beta_j >= A(i,target[j]) + s*[i=j]
```

on every legal edge. An edge is tight when equality holds. Every edge
of a primal assignment that attains the dual bound is tight.

The required rounding goal concerns only the canonical gap cuts. For
each such cut and value, each output count must be the floor or ceiling
of the mean input count. The outputs must preserve each row's multiset
of values and remain on the common optimum face. Balance at every
prefix is a stronger, optional property. The finite checks below test
that stronger property; the general proof does not need it.

Canonical prices have a further restriction: at cut `c`, only value
`target[c-R]` can have a price drop. A target position defines at most
one canonical gap. Arbitrary nonnegative prefix prices do not satisfy
this restriction.

## Lean price facts

`Shuffler/Optimality/BirthPlacement/Dual/Face.lean` states these facts
directly for the existing integer-scaled `Dual.Certificate`. The
identity reward in the Lean equations is `cert.scale*swap`.

1. A tight nonidentity edge `i -> j` reaches a minimum-price eligible
   column of its value. For every same-value column `k` with `i<=k+R`,
   `beta_j<=beta_k`.
2. The level of generic tight edges for one value is nondecreasing in
   birth row. Later rows have fewer eligible columns.
3. If the identity `i -> i` and a same-value nonidentity edge `i -> j`
   are both tight, `beta_i=beta_j+s`.
4. If `j<k` are same-value target columns and `beta_j>beta_k`, then
   every tight assignment fixes `j`. Any nonidentity edge into `j`
   could also reach `k`, contrary to the first fact.
5. Two crossing same-value generic edges have equal column levels.
   Their uncrossing stays tight. At positive `s`, neither new edge can
   become an identity: that would improve the oracle objective.
6. If a tight assignment moves a row `i` but preserves its value, then
   `f(i)<i<f^-1(i)`. Its outgoing generic level is lower than the price
   of its own column. The first four facts force both directions.

The module does not assume or prove a global rounding theorem. Its test
uses `a a b b b b a a` at reach 2, with price 3 at the a-gap cut 3.
Both the identity and the three-cycle `3 -> 6 -> 4 -> 3` attain the same
oracle reward 14. Row 4 gives a nontrivial instance of the mixed-pin
level equation. Negative checks reject a nontight edge and an invalid
column-price order. All six audited results use only the standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`.

These local facts alone cannot prove balance at every prefix in the
mixed-pin case. At reach 2, take target `a a b c`, identity `P`, and
`Q=[3,2,0,1]`. Under arbitrary row-value rewards
`A(i,v)=[v != target[i]]` and `s=1`, both assignments maximize the reward
4 and have a common tight dual. Their total moved count is 4, but every
row-token recoloring balanced at every prefix has total moved count at
least 5. Adding the row constant `3-i` makes each value's rewards
nonincreasing without changing the optimum face: the reward columns are
`a:[3,2,2,1]`, `b:[4,3,1,1]`, and `c:[4,3,2,0]`. The dual is
`alpha=[4,3,2,1]`, `beta=[0,0,0,0]`. These prices are not canonical gap
prices. Also, the two input words already differ by only one at their
sole canonical a-gap cut 2. Their excess discrepancy is at cut 1, which
is not a generation constraint. This example does not refute rounding
at canonical cuts, but it rules out an all-prefix proof from the local
price facts alone.

## Paper result when all fixed-position sets agree

Take `k>0` tight assignments with exactly the same fixed-position set
`F`. There is a constructive balanced recoloring that preserves every
row's multiset of birth values, retains `F`, and uses only tight edges.
Thus it preserves the total endpoint cost `E`.

Reserve the `k` identity tokens at each row in `F`, one for each output
color. Remove those rows and their target columns from the matching
problem. Keep all original indices and the original reach bound.
Every remaining input token uses a generic tight edge.

For each value, sort its remaining tokens by birth row. Their column
levels are nondecreasing by the second Lean fact. Each level contains
exactly `k` times the number of its remaining target columns, because
each input assignment uses every remaining column once. Consecutive
blocks of `k` tokens therefore stay within one level.

The remaining same-value target columns have nondecreasing levels in
target order. A downward step would force the earlier column to be
fixed in all inputs, and that column would already have been removed.
Match each token block to the corresponding remaining target column.
The match has the right level. It also meets lag: in the sorted union
of the input legal matchings, the kth token assigned through a column
cannot occur after that column's deadline. Removing the common pins
does not change this counting argument or any physical index.

Make a bipartite multigraph with one vertex for each remaining birth
row and one vertex for each token block. Each token joins its row to
its block. Every vertex has degree `k`. Repeated perfect matchings
give `k` edge colors. Every color uses one token at each row and one
token from each block.

Each output's count of a value through a prefix is the floor or ceiling
of the mean input count: the prefix contains whole token blocks and at
most one partial block. The reserved identity count is the same integer
in every output, so adding it preserves this property.

Every new edge has the value and column level of a generic tight edge
at the same row, so it remains tight. It cannot become an identity,
because a tight identity at that level would require the extra positive
reward `s`. The output fixed set is exactly `F`. This proves the stated
paper result for any denominator `k`; it is not yet a Lean edge-coloring
construction or a production runtime bound.

## The open mixed-pin case

An identity token can appear before generic tokens at a lower level.
The level equation in item 3 describes the edge that could replace it,
but does not supply a simultaneous recoloring for all rows and values.
The common-fixed-set proof therefore does not apply when pin status
varies among input assignments.

Two precise local statements remain open:

* In a relative cycle whose value-prefix discrepancy has magnitude at
  least 2 at a canonical gap cut, there is a same-value pair of nonfixed
  rows in one input whose destinations can be exchanged legally.
* After repeated such safe splits until no legal nonpin same-value split
  remains, some choice of whole relative cycles balances the counts at
  all canonical gap cuts at once.

A safe split stays on the oracle face, preserves `E`, and increases the
number of relative cycles. These facts would give finite progress if the
two missing statements held. A separate proof is required for the second
statement; discrepancy at most one in each cycle alone does not prove it.
These two-input statements would also need an extension or a composition
argument for arbitrary denominators. The required theorem is still open.

## Named exact checks

`scripts/optimality-priced-face-rounding.mjs` checks six named targets,
all at reach 2. Each canonical gap price ranges over `{0,1,2,3,4}` and
`s` ranges over `{1,2}`. The cases are the four-row unpriced obstruction,
the pin-interval overlap case, the safe-split case, the eight-row
value-job obstruction, and two three-value repeat patterns.

The completed check contains 76,260 price vectors, 174 distinct optimum
faces, 287 co-optimal birth-word pairs, and 36 pairs that need balancing.
Each pair admits a balanced recoloring with unchanged total minimum
endpoint cost `E`. Endpoint minima are computed by enumerating all
lag-valid permutations, independently of the flow oracle.

The local split check includes all 1,201 co-optimal endpoint pairs with
different words. It encounters 74 large-discrepancy relative cycles and
finds a legal nonpin split in every case. One deterministic sequence of
safe splits makes 1,106 splits across 828 pairs. Every resulting terminal
pair has a balanced whole-cycle orientation. This checks one sequence
per pair; it does not check every possible split sequence.

A separate reach-16 case has a at positions 0,17,18,19 and distinct
filler values. Its three inputs are identity, identity, and the cycle
`14 -> 17 -> 15 -> 18 -> 16 -> 19 -> 14`. With price `2s` at the first
a gap, a checked assignment dual gives reward 22 to all three inputs.
There are six balanced colorings. Their best total moved cost is 6,
equal to the input total; three transpositions attain it.

The evidence is in `Bench/evidence-priced-face-rounding.json`. No general
rounding, LP integrality, source extension, or efficient joint optimizer
is established by these checks.
