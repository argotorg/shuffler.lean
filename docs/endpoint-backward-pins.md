# A moved value-correct row must lie on a backward chain

This result is proved in Lean in
`Shuffler/Optimality/BirthPlacement/Word/Backward.lean`. It concerns a fixed
birth word, an endpoint permutation, and the common lag bound. It does not
prove the global rounding bound.

Let `f` minimize the number of moved positions among all permutations
that preserve the birth values and satisfy

```
b <= f(b)+R.
```

Suppose row `p` already has the value required at target position `p`, but
`f(p)!=p`. Write `q=f^-1(p)`. Then

```
f(p)+R < q,
f(p) < p < q.
```

The first inequality is stronger than the second line. The theorem also
applies to the actual `Word.cachedOptimal` endpoint routine, through its
proved minimum-moved-count property.

## Proof

Exchange target endpoints `p` and `f(p)` throughout `f`. Only the edges
from rows `p` and `q` change:

```
before: q -> p -> f(p)
after:  q ------> f(p),    p -> p.
```

All three positions carry the same relevant value. The exchange preserves
value compatibility. It fixes `p` and does not move any previously fixed
position. The number of moved positions therefore decreases.

The new identity edge at `p` meets lag. Every other unchanged edge also
meets lag. Thus the only possible failure is `q -> f(p)`. Minimum moved
count requires that edge to fail, giving `f(p)+R<q`.

The original two edges give `p<=f(p)+R` and `q<=p+R`. Together these three
inequalities imply `f(p)<p<q`.

The proof does not require positive reach. It also does not require an
endpoint implementation, a particular tie choice, or minimum SWAP count.
If further edge restrictions are imposed, the argument needs those
restrictions to permit the two new edges.

## The chain interpretation

A moved row whose birth value equals its target value is an internal
point of a strictly decreasing chain of edges for one value. Its incoming
and outgoing edges meet lag separately. Joining them would miss lag.
Every such chain ends at rows whose birth and target values differ: a
finite, strictly decreasing sequence cannot close into a cycle.

For example, take

```
target = [a,a,b,c]
births = [c,a,b,a]
R = 2.
```

The production endpoint permutation is `[3,0,2,1]`. Row 1 has the correct
value `a`, but lies on the chain `3 -> 1 -> 0`. The shortcut `3 -> 0`
misses reach 2. At reach 3 the shortcut is legal, and the production
routine fixes row 1. `Tests/OptimalityBackwardPins.lean` checks both sides
of this boundary and applies the general theorem to the reach-2 case.

## The exact remaining rounding charge

For each input or output permutation, separate its moved rows into:

- `M`: rows whose birth and target values differ;
- `A` for an input, or `L` for an output: moved rows whose values agree.

Then `E_input=M_input+A` and `E_output=M_output+L`. Rounding that preserves
the multiset of birth values at every row also preserves the total `M`.
If `c` counts nontrivial output cycles and `K=E-c`, then exactly

```
sum K_output - sum E_input = sum L - sum A - sum c_output.
```

Thus the desired original-budget bound is equivalent to

```
sum L <= sum A + sum c_output.
```

The backward-chain theorem describes the vertices counted by `L` for
minimum-moved output endpoints. It does not prove this inequality.

A possible stronger component statement uses the following finite graph.
Choose row-wise provenance for each rounded birth token. Use that choice
to relabel the input-layer vertices as output-layer vertices. Overlay the
relabeled input permutation edges with the output permutation edges on
vertices `(layer,row)`. Each connected component is closed under both
permutations. It has the same mismatch vertices before and after rounding.

For each component `C`, the proposed bound is

```
L_C <= A_C + c_output,C.
```

This would charge every original moved value-correct vertex once. It
would also separate disjoint copies of a local rounding obstruction.
This component bound is a proof question, not a theorem in this file.

For a fixed weighted instance, even the displayed unweighted bound is
stronger than necessary. Let `X` be an optimal fractional assignment, `G_X`
its generation score, `B` the generation baseline, and `s>0` the SWAP
score. Prefix rounding that preserves mean generation needs only

```
expected K_output <= E_X + (G_X-B)/s.
```

It then gives `expected S_output+B <= 2*G_X+s*E_X=L_dual`. At least one
output passes the existing surplus certificate. This implication is
algebra; constructing outputs with that bound remains open here. When
`s=0`, no endpoint-rank bound is needed.
