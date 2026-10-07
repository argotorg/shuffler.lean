# Minimum endpoint weight for a fixed source and birth word

`SourceLazy.WeightSolver.minimize` is an executable Lean solver. A returned
result contains a source plan with the same ordered birth word and a proof of
`MinimalWeightForWord`. It can be passed to the proved fixed-word factor-two
score and surplus theorems.

The result is an `Option`. A `none` result does **not** prove infeasibility.
The theorem that every feasible input returns `some` is still open. The
certificate proof below does not replace that theorem.

## Assignment problem

Let the full word be the initial source followed by the ordered births. Let
its length, which is also the target length, be `n`. Set

```text
A = {i | i + 1 < initial source height}.
```

An endpoint edge `i -> j` is allowed exactly when

```text
word[i] = target[j]
i <= j + reach
i + reach + 1 < initial source height implies j = i.
```

The last condition fixes source tokens below the first SWAP window. At
production reach 16 it is the existing `SourcePlan.source_frozen` condition.
The edge weight is zero for an identity edge, two for a moved edge with both
endpoints in `A`, and one for each other moved edge. The total is

```text
W(f) = moved endpoints + moved A-to-A edges.
```

The existing min-moved-endpoints procedure does not minimize this weight.
For example, at reach 2 and source height 3, use

```text
word   = [b,a,a,b,b,b]
target = [a,b,b,b,b,a].
```

`Word.cachedOptimal` returns `[1,0,5,3,2,4]`, with weight 7. It fixes position
3. Every allowed assignment that fixes position 3 has weight at least 6.
The assignment `[2,5,0,1,4,3]` has weight 5 and is a minimum. Both lower bounds
have checked integer certificates. Replacing each active index `i` by `8*i`
and giving each inserted position a distinct value gives the same failure at
reach 16 and source height 17. The production min-moved-endpoints function
and the new solver are both exercised by the Lean regression.

## Finite minimum certificate

`WeightDual` contains an integer price for each row and each column. Validity
requires

```text
row[i] + column[j] <= edgeWeight(i,j)
```

on every allowed edge. Summing over any legal permutation gives

```text
sum rows + sum columns <= W(permutation).
```

If the candidate attains this lower bound, it is a minimum. The Lean proof
uses the permutation to reorder the column sum. It does not enumerate
permutations. `WeightDual.minimalWeightForWord` transfers the result to
`SourcePlan`: equality of the birth suffixes and the common source gives
equality of the full words. The comparison includes all legal assignments
with this word, regardless of their birth methods.

The executable checker also checks both directions of the supplied inverse
and every allowed endpoint. Thus an error in shortest paths, potentials, or
flow decoding cannot produce an unproved minimum in the result type.

## Sparse network

The graph has `4*n+2` vertices: a source, a sink, one vertex for each row and
column, and two chain vertices per target position. Its arc count is linear
in `n`. Each forward arc also has a residual reverse arc.

* Source-to-row and column-to-sink arcs have capacity one and cost zero.
* Each legal identity row-to-column arc has cost zero.
* For each value there are two chains of target positions in increasing
  order. One chain serves rows in `A`; the other serves rows outside `A`.
* A nonfrozen row enters its chain at the first target position `j` with
  `i <= j+reach`. Entry costs one. Chain travel costs zero.
* An interior-row chain exits to an interior target at cost one. Every other
  exit costs zero.

Every internal arc has capacity `n+1`. A flow of value at most `n` cannot
saturate such an arc, since the original graph has no directed cycle.

Any legal assignment has a flow of the same cost: use direct identity arcs
and use the relevant chain for moved edges. Conversely, decompose an
integral full flow into one row-to-column path per row. Each endpoint is
allowed. Each path costs its edge weight, except that a generic path could
decode to an identity and then cost more. At an optimum this excess cannot
occur: replacing it by its direct zero-cost identity path reduces cost.
Thus the network and assignment minimum values are equal.

The final potentials give the certificate

```text
row[i]    = -potential(row vertex i)
column[j] =  potential(column vertex j).
```

All internal forward arcs remain residual. Their nonnegative reduced costs
prove the certificate inequalities along every legal route. Every used
internal arc also has a residual reverse arc. Both reduced costs can be
nonnegative only if they are zero. The decoded used routes therefore attain
the certificate. This also excludes a positive-cost generic identity route.

## Shortest paths and runtime

The Lean implementation performs `n` unit augmentations. It uses Dijkstra's
algorithm with an array scan to select the least unsettled label. Its simple
implementation has cubic operation count under constant-time indexed
array access and value comparison. There is no Lean runtime theorem.

The following is a paper proof for an implementation that uses integer
buckets in place of the array scan. It is not a claim that the current Lean
code uses buckets.

Initially all potentials are zero and all available arc costs are zero or
one. Stop each shortest-path search when the sink is settled at reduced
distance `D`. Increase **every** vertex potential by

```text
min(distance(vertex), D),
```

where an unset distance is treated as `D`. This truncated update preserves
nonnegative reduced costs, including edges from unreachable vertices. The
source potential stays zero. The new sink potential is the original cost
of that augmentation, called `m_k`. Consequently

```text
D_k = m_k - m_(k-1) >= 0
sum D_k = m_n <= total flow cost <= 2*n.
```

The last bound holds because a full flow decomposes into `n` paths, each
with cost at most two. Each vertex potential lies between zero and `2*n`.
Each residual reduced cost is at most `2*n+1`. A provisional queue key made
before sink settlement is at most `4*n+1`.

Use a bucket array of length `4*n+2` for each augmentation. Resetting it costs
`O(n)`. Scanning arcs and inserting improved labels costs `O(n)`, because
the graph has `O(n)` arcs. Duplicate queue entries can be discarded when
their vertex is already settled or their key is stale. There is at most one
insertion per successful relaxation. The total bucket cursor advance over
all augmentations is at most `sum D_k <= 2*n`. The result is `O(n²)` time and
`O(n)` space in the unit-cost RAM model. Path decoding and the independent
dual check each take at most `O(n²)` operations.

## Remaining Lean proof work

The checked output theorem is complete. Total success needs the following
links to the executable arrays and recursive functions.

| Module boundary | Required result |
| --- | --- |
| Network representation | Arc endpoints and reverse indices are in range; reverse pairs agree; outgoing lists contain exactly their arcs. |
| Assignment routes | A legal full assignment gives a feasible flow of value `n`; each route has at most two positive-cost arcs. |
| Flow augmentation | An executable path has positive residual capacity; augmentation preserves capacities, reverse pairs, and conservation, and raises flow value by one. |
| Residual path existence | A feasible flow of value below a known feasible full flow has a residual source-to-sink path. This lemma is independent of costs. |
| Dijkstra labels | Settled labels are minimum reduced distances; predecessor paths use residual arcs; the minimum scan settles a reachable sink within the vertex count. |
| Potential update | Truncated labels satisfy the edge triangle inequality; updated residual costs are nonnegative; each augmented path arc is tight. |
| Decode | A full flow on the original acyclic graph decodes to mutually inverse endpoint maps; the decoder fuel is sufficient. |
| Certificate completion | The final internal arc slack and tight used routes make all three checks in `check` pass. |
| Solver totality | Induction over the `n` augmentations, followed by decoding and certificate completion, proves `solve ... = some result` for some result. |

The shortest-path invariant must include array sizes, nonnegative reduced
costs, sound tentative distances, predecessor edges, and the settled-set
minimum property. It must establish the truncated edge triangle inequality
at the early sink stop, not only at a full search termination.

Tests cover the two greedy obstructions, initial-height boundaries, empty
input, identity, frozen mismatch, deadline failure, count mismatch, invalid
inverse maps, invalid prices, a nonminimum assignment, and residual reverse
arcs. They also compare the actual solver with an independent permutation
enumerator for all 768 combinations of binary length-three words, source
heights zero to three, and reaches zero to two. These finite tests do not
prove total success on arbitrary inputs.
