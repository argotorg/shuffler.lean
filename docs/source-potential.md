# A source-entry potential for a fixed token assignment

The bound on this potential is now proved for production traces. The
source plan realizer and an optimizer for this potential remain separate
tasks. The existing empty-source API does not change.

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

This first-touch bound is now proved for production traces in
`SourceCycles.trace_selected_pairs_lower_bound`. The caller supplies a
finite set of ordered two-cycles of `traceAssignment`; both positions
must lie below the initial top. The proof extracts the actual SWAP
endpoints, proves their product agrees with the existing token frame,
and applies `selected_pairs_lower_bound` to that list. It has no
source-size restriction. This proves the trace side of the selected-pair
bound; it does not build a source plan or select a minimum-`F` assignment.

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

`trace_sourcePotential_le_twice` now proves the combined inequality in
Lean for every no-POP production trace. `SourceCycles.pairsBelow_card`
connects the ordered-pair count with the full-cycle count used by
`SourcePrefix.cycles_away_bound`. The final theorem includes the empty
source case and has no source-size restriction. It bounds the numeric
potential of the trace's extracted assignment; it does not yet build a
source trace with that cost.

The source-offset availability fact is also proved:
`traceEvents_available_from` uses the exact source length plus event
index and counts copies in `source ++ births`. Along with the existing
`traceAssignment_deadlines` and `traceAssignment_birthWord`, it supplies
the trace-side value, deadline, and birth-method conditions.

## What an endpoint optimizer would need

An optimizer that minimizes `F` over the valid assignments for a fixed
birth word could compare its plan with the assignment extracted from any
other trace with that word. Choosing the cheapest available birth
instructions would then give total and baseline-surplus factor-two
bounds, by the same weighted argument used for the empty source.

No such minimum-`F` optimizer is supplied here. No global birth-order
optimizer is supplied either. A source realizer must still be connected
to the proved potential bound before this can be called a source
approximation result.

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
`Bench/evidence-source-potential.json`. The Lean potential theorem now
covers all no-POP traces, beyond this finite check. It still leaves the
source realizer and assignment selection open.
