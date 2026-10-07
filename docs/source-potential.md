# A source-entry potential for a fixed token assignment

This is a paper interface and proof. The full production-source theorem
and an optimizer for this potential are not yet proved in Lean. It does
not change the existing empty-source API.

Let `n` be the source length, with `n <= 17`, and let `f` assign every
source token and later birth token to its final target position. Let

```text
K(f) = moved positions - nontrivial cycles.
```

Run the empty-source token schedule virtually through the first `n`
births. These virtual births represent the already present source.
Let `P_f` be the permutation that these virtual SWAPs apply to the source
positions. Let `c(P_f)` count its nontrivial cycles that do not contain
the initial physical top, position `n - 1`. For an empty source, set this
count to zero. Define

```text
F(f) = K(f) + 2 c(P_f).
```

## Plan-to-trace interface

A source plan supplies:

- `f`, a value-compatible permutation of all source and birth tokens;
- the birth deadline `b <= f(b) + 16`;
- an available birth instruction at each real birth, using the source
  plus prior-birth counts from `docs/source-word-feasibility.md`;
- the source-size bound `n <= 17`.

First apply a minimum top-SWAP implementation of `P_f` to the source.
Its token-exact count is `K(P_f) + 2 c(P_f)`. Then run the remaining
virtual schedule as real births and SWAPs. Its SWAP count is
`K(f) - K(P_f)`. The total is exactly `F(f)`.

This entry preserves the whole prefix token permutation. It therefore
supplies the forward-position invariant needed by the remaining
schedule. The virtual prefix's frozen positions agree with the target.
The birth-count condition then proves DUP availability at every real
birth. A value-based entry algorithm may use fewer SWAPs; the token-exact
count still gives an upper bound.

## Trace-to-plan interface

A no-POP comparison trace supplies its final labelled assignment `f`.
Births expose fresh token positions. Each physical SWAP composes the
residual assignment with a transposition. Let `M` count the SWAPs that
merge two residual cycles. Then

```text
S = K(f) + 2 M,
```

where `S` is the comparison trace's SWAP count.

Let `q` count the full assignment cycles of length two whose positions
are both below the initial top. Each such pair is wholly in the source.
The first physical SWAP to touch it must use a top outside the pair:
no-POP execution never puts the top below its initial position. Until
that first touch, the pair remains a separate two-cycle. Its first touch
therefore merges cycles. Different pairs require different first-touch
SWAPs. Hence

```text
q <= M,
K(f) + 2 q <= S.
```

## The prefix-cycle bound

Every virtual SWAP stays inside one original full `f`-cycle, so every
`P_f`-cycle stays inside such a cycle.

Consider one nontrivial full cycle `C`.

- If it contains a future birth position, that position is fixed by the
  prefix. Each nontrivial prefix cycle uses at least two source positions.
  Thus twice the number of its prefix cycles is at most `|C| - 1`, which
  is its contribution to `K(f)`.
- If it lies wholly in the source, the virtual prefix completes it. Its
  restriction of `P_f` is that one cycle, up to inversion. If it contains
  the initial top, it contributes zero to `c(P_f)`. Otherwise it
  contributes one. Its `K` contribution is at least two except when it
  is a two-cycle; that exception contributes one to `q`.

Sum over the full cycles:

```text
2 c(P_f) <= K(f) + q.
```

Together with the first-touch bound, this gives

```text
F(f) <= 2 K(f) + q <= 2 S.
```

This comparison fixes the labelled assignment `f`. It does not justify
choosing an arbitrary minimum-`E` assignment among equal copies. The
counterexample in `docs/source-entry-cost.md` shows why that distinction
matters.

## What an endpoint optimizer would need

An optimizer that minimizes `F` over the valid assignments for a fixed
birth word could compare its plan with the assignment extracted from any
other trace with that word. Choosing the cheapest available birth
instructions would then give total and baseline-surplus factor-two
bounds, by the same weighted argument used for the empty source.

No such minimum-`F` optimizer is supplied here. No global birth-order
optimizer is supplied either. The source trace extraction, prefix-cycle
bound, first-touch bound, and source realizer must all be connected before
this can be called a full Lean result.

## An additive consequence for minimum moved count

All cycles counted by `c(P_f)` are disjoint and avoid the initial top,
so `c(P_f) <= floor((n - 1)/2)`. If `c(P_f) = 0`, then `F(f) <= E(f)`.
Otherwise `f` has a nontrivial cycle, so `K(f) <= E(f) - 1`, giving

```text
F(f) <= E(f) + 2 floor((n - 1)/2) - 1 <= E(f) + 15.
```

Thus minimum-`E` selection yields an additive bound of fifteen SWAPs
above twice a comparison trace's SWAP count for normalized sources.
This is a paper consequence with the same missing source-realizer
bridge. It is not the requested factor-two surplus bound.

## Exact checks

`scripts/optimality-source-potential.mjs` checks all reachable labelled
assignments through seven tokens, reaches 1, 2, 3, 4, and 16, and every
normalized source length. It compares against exact minimum-SWAP traces
with zero-cost birth edges. Distinct token values make the target fix the
assignment, so equal-copy reassignment cannot change the comparison.

All 82,233 cases passed both intermediate inequalities and `F <= 2 S`.
The largest ratio was exactly two. The report is
`Bench/evidence-source-potential.json`. This is finite evidence for the
paper argument, not a Lean proof of its full interface.
