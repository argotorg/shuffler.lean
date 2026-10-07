# The endpoint and quota polytope is not half-integral

This is one paper counterexample at production reach 16, with an exact
finite check. It concerns the general endpoint-assignment polytope with
a required generation quota. It does not prove a fractional gap for
the specific moved-position objective or the joint reuse objective.

Use a target of length 20. Value a occurs at positions 0, 17, 18, and 19.
Positions 1 through 13 contain distinct fresh values. Put distinct values
b, c, and d at positions 14, 15, and 16. Require the first a-gap, from
position 0 to position 17, to be retained. This gives the quota

```
C_a(16) >= 2.
```

Let `P` be the identity assignment. Let `Q` fix every position except for
the cycle

```
(14 17 15 18 16 19).
```

Both permutations meet `birth<=target+16`. The largest backward step in
`Q` is five. At cut 16, `P` has one a birth and `Q` has four. Therefore

```
X = (2*P+Q)/3
```

meets the required quota with equality. It also meets all row, column,
nonnegativity, lag, and other generation-quota constraints.

The point is a vertex. Restrict to the face where every edge outside
the union of P and Q has zero weight. Fourteen rows are fixed. On the
remaining six rows, the support is one alternating cycle, so every
doubly stochastic matrix on that support has the form

```
(1-t)*P+t*Q,  0<=t<=1.
```

The required quota has value `1+3*t`. Its tight equality forces `t=1/3`.
In any convex decomposition of X into feasible points, nonnegativity
keeps both points on the same support face. Tightness of the quota keeps
both on its equality. Both points therefore equal X, which proves that
X is a vertex. Its cycle entries are `1/3` and `2/3`, so the polytope is
not half-integral.

This rules out a universal argument that uses only two equally weighted
assignments because every LP vertex is half-integral. A special objective
could still have a different optimal point. In this example, exchanging
positions 16 and 17 gives a legal integral assignment with two moved
positions and meets the quota. No objective gap is claimed.

`scripts/optimality-third-vertex.mjs` checks the two permutations and the
integer numerator of X. It checks every generation quota produced by the
existing deadline construction. On the 26 support variables, the row
and column equations have rank 25; adding the tight quota gives rank 26.
The rank check uses exact BigInt row operations. The saved result is
`Bench/evidence-third-vertex.json`. No optimizer or broad search is used.
