# One local rounding step for an empty source

This note proves a local statement on paper and gives finite checks of its
permutation calculation. It is not a Lean theorem or a global rounding
algorithm. Production code is unchanged.

The result allows a local step to lose endpoint identities. The number of
cycles in the resulting permutations pays for that loss in the actual
empty-source realizer cost. It does not justify repeating the step: the
same cycle credit cannot be used twice.

## The permutation calculation

For a permutation `f` on `n` positions, write

```
E(f) = number of non-fixed positions
c(f) = number of nontrivial cycles
W(f) = E(f)-c(f) = n-(number of all cycles).
```

The proved empty-source realizer uses `W(f)` SWAPs.

Let `P` and `Q` be two permutations. Choose distinct rows `u,v` in one
cycle of the relative permutation `Q⁻¹ ∘ P`. Exchange the two destinations
`Q(u),Q(v)` to obtain `Q*`. This splits that relative cycle into two.
Choose any subset of the cycles of `(Q*)⁻¹ ∘ P`. On each chosen cycle,
exchange the `P` and `Q*` edges between two output permutations `P',Q'`.
Both outputs are permutations, and their combined edge multiplicities are
those of `P,Q*`.

Then

```
W(P') + W(Q') <= E(P) + E(Q).
```

To prove this, put `d=E(Q*)-E(Q)`. Only two rows change, so `d<=2`.
The edge multiplicity identity gives

```
E(P') + E(Q') = E(P) + E(Q) + d.
```

There are three cases.

- If `d<=0`, use `W<=E` on each output.
- If `d=1`, the output pair has at least one nontrivial cycle. Subtracting
  that cycle from its moved-position count pays for the extra position.
- If `d=2`, both changed rows were fixed by `Q`. Neither was fixed by `P`:
  an edge shared by `P` and `Q` is a fixed point of `Q⁻¹ ∘ P`, whereas
  `u,v` lie in one nontrivial relative cycle. The exchanged `Q*` edges are
  also non-diagonal at both rows. Thus both output permutations are
  nonidentity, whichever whole relative cycles are exchanged. Each has a
  nontrivial cycle. These two cycles pay for the two extra moved positions.

This calculation does not require values, quotas, or a reach bound. Those
conditions are needed for the next step, which interprets the outputs as
birth plans.

## When the step gives a trace bound

Assume an empty source and legal direct introduction of every target
value. Suppose `P,Q` meet the endpoint lag bound. For the exchange above,
also require

```
target[Q(u)] = target[Q(v)]
u <= Q(v)+R
v <= Q(u)+R.
```

The exchanged assignment `Q*` has the same birth word as `Q` and still
meets lag. Every recombined output uses only legal edges from `P,Q*`.
The mean value-prefix counts of `P',Q'` equal those of `X=(P+Q)/2`.

For a gap after the `j`th target copy of a value, let `k=p+R` be its cut
and let `C` be the number of births of that value through `k`. Lag gives
`C>=j`. Its relaxed reuse amount is

```
y(C) = min(1,C-j).
```

A sufficient condition for the recombination to preserve the mean reuse
reward at this gap is

```
min(C_P',C_Q') >= j+1  or  abs(C_P'-C_Q') <= 1.
```

In the first case both outputs retain the gap. In the second case the two
integer counts lie within one linear piece of `y`, or at its adjacent
endpoints. Hence

```
(y(C_P')+y(C_Q'))/2 = y((C_P'+C_Q')/2).
```

The same condition preserves a mandatory gap satisfied by the midpoint:
both integer output counts then meet its quota. A straddle such as `j`
versus `j+2` is the case that this test excludes.

Let `G_X` be the relaxed generation score, `s` the SWAP score, and `B` the
generation baseline. If the reuse condition holds at every priced gap,
the mean of the two cheapest output generation scores is `G_X`. More
generally, it is enough that this mean be at most `G_X`.

Let `C_P',C_Q'` now denote the complete realizer scores. The permutation
calculation gives

```
(C_P'+C_Q')/2 + B
  <= G_X + s*(E(P)+E(Q))/2 + B
  <= 2*G_X + s*E(X)
   = J(X),
```

where the second inequality uses `B<=G_X`. Therefore at least one output
satisfies

```
C_output + B <= J(X).
```

If a dual certificate supplies the same bound `J(X)=L`, this output meets
the already proved certificate condition `C_output+B<=L`. The result is
conditional on finding the stated recombination. It does not show that
one always exists or that a sequence of local steps preserves this bound.

## A split need not occur at the rows with excess births

The gap count argument gives two rows where `Q` has the value and `P`
does not. Exchanging their destinations need not meet lag, even if they
are in the same relative cycle.

Take

```
R = 2
target = [v,b,b,v,b,b,v,v]
P = [2,1,0,5,4,3,7,6]
Q = [0,1,6,3,2,7,4,5].
```

Both assignments meet lag. At the gap after target position `p=3`, there
are `j=2` target copies of `v`, and the cut is `k=5`. The prefix counts
are `2` for `P` and `4` for `Q`. The only rows through the cut where `Q`
has `v` and `P` does not are `0,3`. Both are fixed by `Q`. Exchanging them
would use edge `3 -> 0`, which misses reach 2.

The relative permutation has cycles

```
(0 4 6 5 3 7 2), (1).
```

Thus the two rows are in the same relative cycle. The safe equal-value
exchange instead uses `Q` edges `2 -> 6` and `5 -> 7`. Both rows already
have value `v` under `P`. This distinction matters when selecting a split.

## Check and scope

An exact finite check enumerated all pairs of permutations of sizes 2,
3, and 4, every pair of rows in one relative cycle, and every whole-cycle
recombination after their destination exchange. It checked that each
exchange splits the relative cycle, both outputs are permutations, and
the stated `W` bound holds.

The check covered 616 input pairs, 1,784 splits, and 11,816 recombinations.
The bound was an equality in 508 recombinations. The eight-position lag
example above was checked separately. These counts support the paper
calculation; they do not prove a global rounding theorem.

The remaining proposed global statement is stronger: round two value
words so that all corresponding prefix counts differ by at most one,
then find compatible endpoint assignments with

```
W(P')+W(Q') <= E(P)+E(Q).
```

The first part also has a direct two-color construction. Keep the two
birth tokens at each row, one from each input word. For each value, sort
all its birth tokens by row and pair consecutive tokens. Add one edge
between the two tokens at each row, and one edge for each value pair.
Each token has degree two. The components alternate between the two edge
types and have even length. Color each component alternately with two
colors.

Each row now has one token of each color. Each consecutive value pair
also has opposite colors, so the two value-prefix counts differ by at
most one at every cut. Match the two tokens of the `r`th value pair to
the two copies of that value's `r`th target occurrence. This is lag-legal:
the sorted union of the two original lag matchings puts both tokens of
that pair no later than that occurrence's deadline. This proves existence
of two balanced words and compatible assignments. It does not bound their
identity loss.

For a fixed permutation, `K=E-c` is also the rank of its undirected
assignment edges in the graphic matroid, with loops ignored. Each
nontrivial cycle has a spanning tree with one fewer edge than vertices.
Thus the missing cost statement can be viewed as a bound on the sum of
two output forest sizes. This observation does not give a matroid
exchange theorem for the birth-word objective.

Six focused cases were checked by enumerating every balanced pair of
birth words and, independently, every lag-valid endpoint permutation.
For each output word the check took the minimum `K` over its endpoint
assignments. A word pair must preserve the two input values at every row.
These checks found the following minima.

| Target | R | Input E sum | Minimum balanced K sum | Balanced word pairs | Endpoint permutations |
|---|---:|---:|---:|---:|---:|
| `a b c d a a` | 2 | 5 | 3 | 2 | 162 |
| `v b b v b b v v` | 2 | 11 | 4 | 4 | 1,458 |
| `a b b b b a a a` | 3 | 8 | 4 | 8 | 6,144 |
| `a a b b c c a a` | 2 | 8 | 4 | 8 | 1,458 |
| `a b a b c c a a` | 2 | 8 | 4 | 4 | 1,458 |
| `a b c a b c a b` | 3 | 8 | 2 | 2 | 6,144 |

The first case uses identity and `[0,4,5,1,2,3]`. The second uses the
displayed eight-position `P,Q`. Each remaining case uses identity and
`Q(i)=(i+n-R) mod n`. Complementary word pairs are counted separately.
The check examined 16,824 endpoint permutations in total. It was a check
of these six inputs, not a search over arbitrary targets or prices.

## More than two input words

The word-feasibility construction extends to any positive integer `k` of
input assignments. Keep their `k` birth tokens at each row. For each value,
sort its tokens by birth row and group consecutive blocks of `k` tokens.
Make a bipartite multigraph: one vertex for each birth row, one vertex for
each value group, and one edge for each token. Every vertex has degree `k`.

A regular bipartite multigraph has a perfect matching. Removing one
matching and repeating gives `k` edge colors, each used once at every
vertex. Each color supplies one token per birth row and one token from
each value group. Its value-prefix count is the floor or ceiling of the
mean input count, since a prefix contains whole value groups and at most
one partial group. Match every token in the `r`th group to the `r`th
target occurrence of that value. The sorted union of the input lag
matchings proves that all these assignments meet lag.

This is an existence construction for any rational mixture after expanding
its denominator into repeated input assignments. The denominator can be
large. This construction is not a production runtime bound, and it does
not imply an `O(n^2)` implementation.

The missing cost statement in this form is

```
sum_output K(output) <= sum_input E(input).
```

All endpoint cost checks in this note concern `k=2`. Neither the two-input
nor the general cost statement is proved here.

## Common fixed positions can be kept

Suppose both input assignments fix a position `i`. Both rounded words then
have `target[i]` at row `i`, because their row tokens have that same value.
All such common fixed positions can be reserved in both endpoint matchings.

For a value `v`, let `F_v(k)` count the reserved positions through `k`, and
let `a_v(k-R)` count its target endpoints whose deadlines are at most `k`.
After the reserved pairs are removed, each input satisfies the endpoint
Hall bound

```
C_v(k)-F_v(k) >= a_v(k-R)-F_v(k-R).
```

The right side and the removed counts are integers. The mean input count
satisfies the same inequality. Each balanced output count is its floor or
ceiling, so each output also satisfies the inequality. Matching the
remaining births and endpoints in deadline order therefore preserves all
the common fixed positions. This argument proves feasibility; it does not
bound the cost of losing positions that only one input fixes. The same
proof applies to a position fixed by every input in the `k`-input
construction: subtract the common integer pin counts before rounding.

## The stronger moved-position bound fails

One might require `E(P')+E(Q')<=E(P)+E(Q)` instead of using `K=E-c`.
That requirement is false, even after choosing the output endpoint
assignments optimally.

Take

```
target = [a,a,b,c], R=2
P = [0,1,2,3]
Q = [3,2,0,1].
```

The input birth words are `[a,a,b,c]` and `[c,b,a,a]`. Their moved-position
sum is 4. The requirement that each prefix differ by at most one copy,
together with preserving the two values at each birth row, forces the
output words, up to exchange, to be

```
[a,b,a,c]  and  [c,a,b,a].
```

The first word needs at least two moved positions. In the second word,
row 3 must supply target-a position 1, since position 0 has deadline 2.
Row 1 must then supply position 0. With the forced `0 -> 3` edge this
gives a three-cycle. Thus its minimum moved count is 3. The minimum total
is 5, strictly above the input bound 4.

The endpoint assignments

```
P' = [0,2,1,3]    E=2, K=1
Q' = [3,0,2,1]    E=3, K=2
```

attain those minima and have total `K=3<=4`. This example shows why the
cycle allowance can matter. It does not refute the required `K` bound.

The example also embeds at reach 16. Insert 14 distinct fresh values
between the first and second `a`, and keep their rows fixed in both
inputs. The four active positions are then `0,15,16,17`. The invalid edge
becomes `17 -> 0`; its distance is 17. Each fresh value has only one token
and one target, so its endpoint is forced in both rounded words. The same
minimum counts 5 and 3 follow on the four active positions.

## A bounded exhaustive check

`scripts/optimality-local-cycle-rounding.mjs` reproduces the 11,816 local
permutation checks and a separate exhaustive check of the global
two-word conjecture. The global domain is every canonical target
partition through length 6, reaches 1, 2, and 16, and every pair of
lag-valid input endpoint assignments.

The checker caches the minimum `E` and minimum `K` for each birth word by
independently enumerating all endpoint permutations. It checks each
unordered pair of birth words using the minimum input `E` sum. This is
the strongest bound for those words, so it covers every ordered pair of
input assignments with those words. For each pair that is not already
balanced, it enumerates all balanced colorings of the two row tokens.

The completed domain contains:

- 837 target/reach instances;
- 196,270 endpoint permutations;
- 111,699,278 ordered input assignment pairs, covered by 2,751,360
  unordered birth-word pairs;
- 410,670 word pairs requiring rounding, with 954,240 balanced colorings.

No `K` bound failure occurred in that domain. The stronger `E` bound
failed in 2,592 birth-word pairs. The evidence retains the first five
failures, including the four-position example above, and counts all of
them. Results are in `Bench/evidence-local-cycle-rounding.json`.

Reproduce with:

```
node scripts/optimality-local-cycle-rounding.mjs
```

No proof of the global endpoint cost bound is given here. In particular,
the local cycle allowance cannot be summed over an arbitrary sequence of
exchanges. The finite checks do not establish that bound, LP integrality,
or an efficient rounding algorithm.
