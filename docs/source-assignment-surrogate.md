# A source assignment bound and an edge-cost obstruction

The source realizer is already proved. Choosing a source assignment is still
open. This note gives a weaker objective than its exact SWAP count and proves
that one proposed linear approach cannot work with that realizer.

The bound for the weaker objective is a paper deduction from existing Lean
lemmas. The finite edge-cost obstruction below is a separate Lean theorem.
Neither changes the production builder or its public guarantees.

## Count only the full cycles affected by source entry

For an assignment `f`, let:

- `E` be the number of moved token positions;
- `z` be the number of nontrivial full cycles of `f`, so `K=E-z`;
- `P` be the virtual source-prefix permutation;
- `c` be the number of nontrivial cycles of `P` that omit the initial top;
- `r` be the number of full cycles of `f` that contain at least one of those
  `c` prefix cycles.

For an empty source, take `c=r=0`. Every prefix cycle lies in one full cycle,
so `0≤r≤c` and `r≤z`. Define

```
F = K + 2c              exact canonical realizer SWAP count
H = E + 2c - r          proposed assignment objective
```

Then `H-F=z-r≥0`. The objective `H` uses the exact contribution to `F` on
each source-affected full cycle. On every other full cycle it uses the moved
count `E`. It does not need to maximize the number of all full cycles.

Let `q` count the full two-cycles wholly below the initial source top.
The existing component proof gives the following bounds:

```
F ≤ H ≤ 2K + q ≤ 2S,
```

where `S` is the SWAP count of any no-POP trace with assignment `f`.
To see the middle inequality, consider a full cycle of size `m≥2`.
If it contains no counted prefix cycle, its contribution to `H` is `m`,
which is at most `2(m-1)`. Otherwise its contribution is
`m-1+2c_local`. The proved prefix bound gives
`2c_local≤m-1+q_local`. Add these bounds over the disjoint full cycles.
Finally, the proved first-touch bound is `K+2q≤S`; it implies
`2K+q≤2S`. In fact, this argument gives `H+3q≤2S`.

The Lean facts used here are `SourcePrefix.prefix_sameCycle`,
`SourcePrefix.component_bound`, and
`SourceCycles.trace_cyclesBelow_lower_bound`. The combined `H` statement
has not been added as a Lean theorem.

At production reach 16, a valid plan has at most 17 movable source slots.
Only 16 of them omit the top. Thus `c≤8`; when `c>0`, the correction
`2c-r` is at most 15. The topology to be tracked concerns at most eight
prefix cycles. Their membership in common full cycles can still depend on
arbitrarily long paths through future token assignments.

Minimizing `H` over feasible assignments of a fixed birth word would suffice
for a factor-two SWAP bound. The cheapest introduction score depends only
on that word and the source, so it also gives the weighted surplus bound.
For a joint word-and-assignment objective, `2G+sH` is sufficient, where `G`
is the introduction score and `s` the SWAP price. This is a weaker target
than minimizing `F`. No efficient minimizer for `H` is claimed here.

## A bounded interface to future assignments

Keep only assignment edges whose endpoints are both in the source. This
partial permutation consists of disjoint paths and closed cycles. The
virtual prefix uses only this data: a target outside the source acts as an
exit, and its exact future index does not affect any prefix SWAP. Each
prefix cycle stays inside one component of the source partial permutation.

Call a source component marked when it contains a prefix cycle counted by
`c`. Let `q_closed` count marked closed source cycles, and let `m` count
marked open source paths. Then `m≤c≤8` at reach 16. Follow the full assignment
from each marked path, through future positions and any unmarked source
paths, to the next marked path. These returns define a permutation `tau`
of the `m` marked paths. Fixed points of `tau` count as return cycles. Thus

```
r = q_closed + number_of_cycles(tau).
```

This confines the needed global topology to at most eight terminals. It
does not make the connection problem local: a return path can pass through
many future positions. Once the full assignment is supplied, a cycle scan
with indexed arrays computes this information in linear time. Optimizing it
remains a separate problem.

If `m=0`, then `r=q_closed`. If `m=1`, then `r=q_closed+1`. In these cases
`H-E` is fixed by the source partial map. For a supplied birth word and a
fixed source partial map, minimum-cost bipartite matching can minimize `E`
over the remaining value-compatible deadline edges. Source rows that exit
the partial map are restricted to future columns. Introduction availability
depends on the supplied word, not on which equal copies are paired.

In particular, source length at most four gives `c≤1` and hence `m≤1`.
There are only finitely many partial maps on those source positions.
Trying them and solving their matching problems gives a polynomial
fixed-word route for that special case. This is a paper construction; no
implementation, complexity refinement, or Lean optimization theorem is
claimed.

For `m>0`, discarding the return connections only gives

```
q_closed + 1 ≤ r ≤ q_closed + m.
```

The resulting local upper estimate can exceed `H` by as much as `m-1`,
with the bound `m-1≤7`. This additive allowance is not a factor-two surplus
guarantee. A finite set of terminal-connection patterns does not by itself
give an efficient method to realize each pattern through the permitted
future matching edges.

## H is not an exact sum of edge costs

Use three equal source values and no births. Every token permutation is
value-compatible. The top is position 2. The values of `H` are:

| Assignment | H |
|---|---:|
| identity | 0 |
| either three-cycle | 3 |
| `(0 1)` | 3 |
| `(0 2)` or `(1 2)` | 2 |

The three even permutations use every row/column edge once in total.
So do the three odd permutations. Any sum of fixed edge costs therefore
has the same total on the two groups. Their `H` totals are 6 and 7.
Thus a plain assignment cost matrix cannot represent `H` exactly.
This argument does not rule out a polynomial algorithm with more structure.

## A stronger obstruction for the current realizer

Suppose a fixed signed rational matrix supplied

```
W(f) = sum_i w[i,f(i)]
```

with both of these properties for one source/target instance:

1. `F(f)≤W(f)` for every valid source plan.
2. `W(f_trace)≤2*trace.swapCount` for every no-POP comparison trace.

These properties would permit minimum-cost matching to select a plan whose
canonical realization has at most twice the comparison trace's SWAP count.
They are incompatible, even with source length 5 and total length 7.

Use an empty spill set, source `[a,a,a,a,a]`, ordered births `[a,a]`, and target
`[a,a,a,a,a,a,a]`, where `a` is an unspilled variable. Every permutation below
is a valid `SourcePlan`: the birth values agree, all deadlines fit reach 16,
the source has no frozen slot, and both births can use DUP.

An assignment array lists the target index of each token.

| Name | Assignment | Fact used |
|---|---|---|
| A | `[6,5,1,0,4,3,2]` | `F=9` |
| D | `[0,6,2,1,4,5,3]` | `F=4` |
| I | `[0,1,2,3,4,5,6]` | `F=0` |
| B | `[0,5,2,1,4,3,6]` | a trace uses 2 SWAPs |
| C | `[6,1,2,0,4,5,3]` | a trace uses 2 SWAPs |
| E | `[0,6,1,3,4,5,2]` | a trace uses 2 SWAPs |

`A` has one full six-cycle and two prefix two-cycles, both away from the
initial top. Thus `K=5`, `c=2`, and `F=9`. `D` has `K=2` and `c=1`.

These production instruction lists give the three upper bounds:

```
B: DUP1; SWAP2; SWAP4; DUP1
C: DUP1; DUP1; SWAP3; SWAP6
E: DUP1; DUP1; SWAP4; SWAP5
```

For every row, the multiset of its destinations in `A,D,I` equals the
multiset in `B,C,E`. Therefore every edge matrix, including an asymmetric
matrix with negative entries, satisfies

```
W(A) + W(D) + W(I) = W(B) + W(C) + W(E).
```

The lower requirements make the left side at least `9+4+0=13`.
The three traces make the right side at most `4+4+4=12`. This is a
contradiction.

`Tests.OptimalitySourceEdgeObstruction.no_edge_additive_sandwich` proves
this statement in Lean. It constructs valid source plans, replays the actual
production traces, proves their extracted assignments and SWAP counts,
checks the three potential values in the kernel, and proves the edge-sum
identity for arbitrary rational weights. It uses only the standard proof
axioms. No solver result is an assumption of the theorem.

The six assignments were found in one focused check of the 5040 labelled
assignments at source height 5 and total length 7. The final proof needs only
the six displayed assignments and the three explicit traces.

## Old rows and moved count do not determine a sufficient bound

Keep `A` above, and compare it with

```
T = [6,5,1,0,4,2,3].
```

Both have six moved positions and exactly the same five old assignment rows,
including the same future destinations for the old tokens. They have the
same source partial map and the same two prefix cycles. `A` reconnects those
paths into one full cycle, so `r=1` and `F=H=9`. `T` leaves two full cycles,
so `r=2` and `F=H=8`.

The production trace

```
DUP1; SWAP3; SWAP4; DUP1; SWAP3; SWAP6
```

has assignment `T` and four SWAPs. Any score that depends only on `E` and
the old rows must give the same result for `A` and `T`. A pointwise bound
`F≤score≤2S` would require that result to be both at least 9 and at most 8.
This rules out such a local score even when it is nonlinear.

`Tests.OptimalitySourceEdgeObstruction.no_old_rows_surrogate` proves this
second obstruction in Lean. It checks the production trace, equal old rows,
the moved counts, and the required potential values. Future connectivity is
therefore necessary for this pointwise bound, even though its interface has
at most eight marked paths at production reach.

## What remains possible

The obstruction concerns a universal pointwise edge-cost bound for this
canonical realizer. It does not rule out a global factor-two algorithm, a
different realizer, or an optimizer that only needs a bound for its selected
assignment. This equal-value instance itself has an immediate zero-SWAP
solution.

The source correction in `H` is small at fixed reach, but it includes cycle
connectivity. A candidate-specific primal-dual certificate can avoid a
universal assignment bound: the already proved test `C+B≤L` is sufficient.
Thus exact minimum `F` is one route, but is not required by the cost theorem.
