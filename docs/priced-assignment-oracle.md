# A sparse oracle for one priced assignment problem

This is a paper-level construction with small exact checks. It does not
change production code. It solves one assignment problem after the gap
prices have been fixed. It does not solve the outer price problem or
give the rounding theorem needed to construct a trace with the required
surplus bound.

[The restricted full-price theorem](pairwise-premium-certificate.md)
proves that one oracle optimum suffices when every positive-premium
value occurs at most twice. Its Lean proof takes the optimal assignment
or tight finite certificate as input; it does not implement this oracle.

## Fixed prices

Let target positions be `0,...,n-1`, with common reach `R>=1`. Give each
gap `g=(p,t,v)` a nonnegative price `lambda_g`, and define

```
h_v(b) = sum_{g: value(g)=v and b<=p_g+R} lambda_g.
```

For fixed prices the assignment subproblem is

```
maximize  sum_b (s*[b=f(b)] + h_target[f(b)](b))
subject to f being a permutation and b<=f(b)+R.
```

The price function is nonincreasing. It changes just after target
deadlines `p+R`. If `d` is the first deadline of value `v` at or after
`b`, then `h_v(d)=h_v(b)`. Include every target deadline, including a
value's last occurrence even when it has no priced gap.

## The flow graph

Send `n` units from a source to a sink. Each birth and target has capacity
one. Use rewards, or negate them for a minimum-cost flow implementation.

- A birth node `b` has a direct arc to target node `b`, with reward
  `s+h_target[b](b)`. This arc preserves endpoint identity.
- Birth `b` can instead enter a global time chain at time `b` for reward
  zero. The global chain permits waiting forward.
- At every target deadline `d=j+R`, the global chain can enter a value
  chain for `target[j]`, with reward `h_target[j](d)`.
- Each value chain visits its target deadlines in order. Travel forward
  has reward zero. At deadline `j+R`, the chain can exit to target `j`.
- Each target sends its unit to the sink.

Compress the global chain to the union of birth times and target
deadlines. There are `O(n)` nodes and arcs. No edge for every possible
birth/target pair is needed.

For a source of length `m<=n`, an old row `b<m` can only enter its fixed
source value's chain, at that value's first deadline at or after `b`.
That arc has reward `h_source[b](b)`. Its identity arc exists only when
`source[b]=target[b]`. If `b+R+1<m`, give the old row only its legal
identity arc. These are the source value and frozen-row restrictions
used by the proved `SourcePlan` API. New rows use the global chain.

## Equality of optimal values

An allowed assignment gives a flow with exactly its reward. Route an
identity on its direct arc. For any other edge `b->j`, enter the value
chain at its first deadline `d>=b`, then continue to `j+R`. Such a
deadline exists because `j+R>=b`. The entry reward is `h_v(b)`, as above.
Each target has one assigned birth, so all target capacities are met.

Conversely, decompose an integral complete flow into birth-to-target
paths. Each path gives an allowed edge. A path entering a value chain
at `d>=b` receives at most `h_v(b)`. A path decoded as an identity can
only gain the nonnegative identity bonus compared with a generic path.
Thus the decoded assignment has at least the flow reward. An optimal
integral flow exists because this is a network flow problem with integer
capacities. Together, the two directions prove equality of optima.

The same argument applies to the restricted old rows. Hard-value quotas
change the outer dual's constant term; they do not change this fixed-price
assignment oracle.

## Capacity and runtime bounds

Place each birth at time `b` and each target at time `j+R`. After all
events at a time have been processed, the flow that still crosses the
time cut is

```
number of births so far - number of target deadlines so far <= R.
```

Consequently each positive-time internal arc needs capacity at most `R`.
A zero-time entry arc can need `R+1`: the first `R+1` births of one value
can enter its chain at its first deadline `R`; one unit exits and `R`
remain. A uniform internal capacity `R+1` therefore preserves the
construction. Capacity `R` on every internal arc does not preserve its
representation of every assignment. Unit-arc expansion has `O(R*n)`
size, hence `O(n)` size at fixed reach 16.

For direct extraction of a row/column certificate, use capacity `R+2`
on every internal arc instead. This includes birth-entry, identity, and
target-exit arcs; their smaller natural capacities follow from the unit
birth supplies and target demands. Every internal upper bound is then
strictly inactive in a complete flow. Optimal residual potentials `p`
satisfy `cost(u,v)+p(u)-p(v)>=0` on each internal arc, with equality on
every used arc. Set

```
alpha_b = p(birth_b),    beta_j = -p(target_j).
```

Summing the inequalities along the exact path for an allowed edge gives
`alpha_b+beta_j>=s*[b=j]+h_target[j](b)`. Used paths give equality, so the
sum of row and column potentials equals the optimal assignment reward.
This supplies the row/column part of the existing finite certificate
without an extra dense assignment solve. Gap cap multipliers are still
`max(w_g-lambda_g,0)`.

A standard successive-shortest-path algorithm with potentials and
Dijkstra uses at most `n` augmentations. The graph is initially acyclic,
so initial potentials can be computed in linear time. This gives
`O(n^2 log n)` arithmetic operations on the sparse graph. This exceeds
the strict production ceiling of `O(n^2)`.

For a theoretical bound, Theorem 1.1 of
[van den Brand et al., A Deterministic Almost-Linear Time Algorithm for
Minimum-Cost Flow](https://arxiv.org/html/2309.16629#S1.SS2) gives exact
flow in `m_edges^(1+o(1))*log U*log C`, for integral demands/capacities
bounded by `U` and integral costs bounded by `C`. After clearing rational
prices, the oracle has `O(n)` edges and can use `U=O(n)`. The resulting
bound retains a `log C` factor. No bound on the bit length or magnitude
of all prices produced by an outer algorithm has been established here.
This theorem requires no unit-capacity expansion. It is a theoretical
reference, not a proposed production implementation.

## The remaining price and rounding problem

Write `A(lambda)` for the oracle's maximum reward. For optional gaps
with quota base `a_g` and reward `w_g`, eliminating the cap multipliers
gives the convex dual objective

```
U(lambda) = A(lambda) - sum_g a_g*lambda_g
             + sum_g max(w_g-lambda_g,0),       lambda>=0.
```

A required hard gap has quota base `a_g+1` and reward zero. Its term is
included using that base. The lower bound is the constant cost minus
`min U`. An oracle assignment supplies the prefix counts for a
subgradient. At an optimal price, a convex combination of optimal
assignments can meet the quotas even if no one oracle assignment does.
The sparse oracle therefore does not establish LP integrality.

For an empty-source integer plan, let `G` be generation cost, `E` the
moved endpoint count, and `c` its number of nontrivial permutation cycles.
The proved realizer uses `E-c` SWAPs. If `B` is the generation baseline,

```
J = 2*G+s*E
S = G+s*(E-c)
J-(S+B) = (G-B)+s*c.
```

Thus exact attainment `J=L` is stronger than required. A rounding loss
of at most `(G-B)+s*c` still permits the finite certificate `S+B<=L`.
This is a possible accounting rule for a rounding proof, not a proved
rounding guarantee. It does not apply unchanged to the source realizer,
whose initial permutation can require extra SWAPs.

[The direct certificate note](direct-certificate-invariant.md) gives
an exact defect identity for capped optional prices. It includes the
assignment slack of a plan that does not maximize the oracle reward,
and checks the price boundary cases at an optimal fractional pair.

One possible first step is to round the value birth-count matrix using
its laminar prefix constraints. Constrain each rounded prefix count
between the floor and ceiling of its fractional count. The resulting
flow polytope is integral; a convex decomposition can also preserve each
prefix count's expectation. A reuse reward is the threshold at the
integer count `a_g+1`. This rounding preserves its expected reward, and
preserves required integer quotas. The missing step is to couple the
rounded value word to endpoint identities and charge any lost identity
reward to the cycle and generation allowance above. Rounding only the
current assignment support is insufficient; new endpoint edges can be
needed.

[Celis, Straszak, and Vishnoi, Ranking with Fairness
Constraints](https://arxiv.org/html/1704.06840) is relevant to disjoint
value groups and prefix quotas. Its flow and objective-specific
integrality results assume monotone Monge weights. A diagonal bonus
fails that condition. The sparse construction above instead uses the
specific sum of a nonincreasing value price and a direct identity arc.
The ranking result supplies no outer rounding theorem for this model.
No hardness result for another buffer cost model is used here.

## Independent small checks

`scripts/optimality-priced-assignment.mjs` compares exact BigInt flow
with independent enumeration of every endpoint permutation in seven
named cases. It also routes each feasible assignment through the sparse
graph and checks capacities and reward equality. It extracts residual
potentials, checks every allowed row/column inequality, and checks dual
attainment. The cases cover empty
input, last-occurrence entries, several value prices, zero SWAP price,
source values, frozen source rows, and a frozen value conflict.

The test implementation uses Bellman-Ford for its small flow instances;
it does not claim the Dijkstra runtime above. Five tests include negative
price and invalid deadline data, and the `R+1` entry example. Results are
in `Bench/evidence-priced-assignment.json`. The report also reevaluates
the two saved price vectors. The periodic vector gives row/column sum
619 on 206 nodes and 375 arcs; the source vector gives sum 153 on 218
nodes and 409 arcs. Replacing the saved row/column data by the extracted
potentials passes the existing exact certificate checker and keeps lower
bounds 1166 and 147. This does not search for new prices.

These checks support the
construction but are not a Lean proof, a broad search, or a production
solver. Outer multiplier updates and trace-producing rounding remain
open.
