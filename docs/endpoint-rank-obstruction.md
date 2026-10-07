# Minimum moved count need not attain minimum SWAP count

This note rejects one proposed endpoint normalization lemma. It does not
change the production endpoint routine. The universal claim is refuted by
a short finite argument below. A Lean regression evaluates the actual
production routine on the example at reach 16.

For a lag-valid endpoint assignment `f`, write `E(f)` for its number of
moved positions, `c(f)` for its number of nontrivial cycles, and
`K(f)=E(f)-c(f)`. The empty-source realizer uses exactly `K(f)` SWAPs.
The birth word fixes the introduction choices and their least possible
score; choosing different equal-copy endpoints does not change that word.

The proposed lemma was:

> For any supplied lag-valid assignment, there exists a minimum-`E`
> assignment for the same birth word whose `K` is no larger.

This is false. The issue can require sacrificing a fixed position. A
different choice among minimum-`E` assignments is not always sufficient.

## Seven active positions

Use reach 3 and

```
target = [a,a,a,b,c,d,a]
births = [d,b,a,a,a,a,c].
```

There is only one position where the birth value equals the target value:
position 2. Therefore every compatible assignment moves at least six
positions. To attain `E=6`, it must fix position 2.

The unique values force `0 -> 5`, `1 -> 3`, and `6 -> 4`. After position 2
is fixed, the remaining a-birth rows are `3,4,5`, and the remaining a-target
positions are `0,1,6`. The deadline of target 0 is 3, so row 3 must supply
it. The deadline of target 1 is 4, so row 4 must supply it. Row 5 then
supplies target 6. Thus the minimum-`E` assignment is unique:

```
P = [5,3,2,0,1,6,4]
cycles: (0 5 6 4 1 3), (2)
E(P)=6, c(P)=1, K(P)=5.
```

Instead choose

```
Q = [5,3,0,1,6,2,4]
cycles: (0 5 2), (1 3), (4 6)
E(Q)=7, c(Q)=3, K(Q)=4.
```

Every edge of `Q` meets reach 3 and preserves the birth value. It sacrifices
the fixed position 2 but uses one fewer SWAP. It also attains the minimum
`K`: an assignment with six moved positions is the unique `P`, while an
assignment with seven moved positions has at most three nontrivial cycles,
so its `K` is at least four.

## The same obstruction at production reach 16

Put active position `i` at position `5*i`. Insert four distinct fresh
values between each two active positions. Each inserted value occurs once
in each word at the same position, so its endpoint is forced to be fixed.
There are 31 positions in total, with 24 forced filler identities.

Between active positions, the reach condition is

```
5*b <= 5*j+16  iff  b<=j+3.
```

Thus this embedding preserves exactly the reach-3 endpoint choices of the
seven-position example. It preserves their `E`, nontrivial cycles, and
`K`. The only optional fixed active position is 10. Keeping it forces the
six-cycle; moving it permits the three smaller cycles.

`Tests/OptimalityEndpointRank.lean` evaluates `Word.cachedOptimal` at reach
3 and on this reach-16 embedding. It checks both assignments, their moved
counts, their arbitrary-SWAP counts, compatibility, and lag. It also uses
the existing theorem that the production choice minimizes `E` among all
compatible lag-valid assignments. The uniqueness and minimum-`K` argument
above is a paper proof; it has not been added as a Lean theorem.

## Scope

The production fixed-word endpoint routine chooses `P`, so with SWAP
score `s` the realizer costs `G+5s` instead of the available `G+4s`.
Its proved factor-two comparison remains valid. This example does not
refute a two-word bound against the original moved-position budget, and it
does not establish any complexity lower bound for choosing endpoints.

It does refute both of these shortcuts:

- Treat minimum `E` as sufficient to attain minimum `K`.
- Assume that a choice among minimum-`E` matchings can always reach the
  `K` of a supplied matching.

An algorithm that retains minimum `E` as an invariant cannot attain the
minimum SWAP count on this word. A constructive cost proof must permit
some extra moved positions, or prove its desired allowance directly for
the endpoint routine it uses. Exact minimum `K` is not assumed to be an
efficient subroutine here.

## Discovery and reproduction

`scripts/optimality-endpoint-rank.mjs` compares minimum `E`, minimum `K`,
minimum `K` among minimum-`E` matchings, and the ordered endpoint model.
It independently enumerates lag-valid endpoint permutations and stops at
the first normalization obstruction. The first obstruction found is the
seven-position example above. Before stopping it checked 616,618
permutations and 69,982 distinct word instances. These are discovery
counts, not a proof for larger inputs.

The report is `Bench/evidence-endpoint-rank.json`. Reproduce the bounded
discovery check and the production regression with:

```
node scripts/optimality-endpoint-rank.mjs
lake env lean Tests/OptimalityEndpointRank.lean
```

The JavaScript endpoint model is used only in the discovery check. The
Lean regression calls the cached production endpoint function itself.
