# Fixed birth word endpoint matching

Fix one value. Let `B` be its birth positions and let `T` be its output
positions. An endpoint map sends each birth `b` to an output `t` and must
satisfy `b ≤ t + R`. The two sets have equal size.

At each cut `k`, count births at or before `k`. Count outputs whose deadline
`t + R` is at or before `k`. The Hall condition says that the second count
does not exceed the first count. This condition is both necessary and
sufficient: matching the two sets in increasing order meets all deadlines.
Lean proves this in `Hall.condition_iff_ordered_deadline`.

An identity endpoint `c → c` uses one unit of Hall slack at each cut in the
half-open interval `[c,c+R)`. After all such intervals are removed, the
remaining sets meet the Hall condition exactly when their interval load
does not exceed the original slack. Lean proves this in
`Hall.remaining_iff_reservations`.

To keep as many identity endpoints as possible, scan their possible starts
in increasing order. Keep a start if one unit remains at every cut in its
interval. All intervals have the same length. An earlier accepted start
can replace the first start in any competing feasible set: it ends no
later, and the remaining intervals start after that first start. This
exchange proves that the scan keeps a maximum number of starts.
Lean proves this in `Reservations.select_optimal` and `Hall.fixed_optimal`.

`Endpoint.optimal` keeps these selected identity endpoints and matches the
remaining sets in increasing order. This is a computable equivalence.
`Endpoint.optimal_deadline` proves its deadline bound.
`Endpoint.fixed_card_le` proves that no other deadline-respecting
equivalence has more fixed positions. `Endpoint.optimal_fixed_eq` proves
that its fixed positions are exactly the selected reservations.

`Word.optimal` combines the maps for all values. Its forward and inverse
maps are executable. `Word.support_card_le` proves that this permutation
moves no more tokens than any other value-compatible endpoint permutation
that meets the same deadlines. The proof partitions the fixed positions
by their value and adds the per-value bounds.

The production wrappers use `Word.cachedOptimal`. It stores one endpoint
map per distinct birth value and reuses that map in both directions.
`Word.cachedOptimal_eq` proves exact equality with `Word.optimal`, including
its choice between equal-cost assignments. The raw-word parser uses the
same stored maps. Both input words are stored in vectors before the value
scans. The map table is explicit data, so the compiled lookup function does
not rebuild it.

`Bench/BirthEndpointCache.lean` runs both permutation directions on stored
lists with four repeated values. One local sample took 8893 ms for the
original map and 113 ms for the stored map at length 160. The saved sample
is `Bench/evidence-endpoint-cache.json`. These times are execution evidence,
not a proof of a time bound.

`Plan.optimizeEndpoints` uses this map in an existing birth plan. The
birth word and all birth events stay the same. The map has the least
possible number of moved endpoint tokens for that word. The realizer can
then turn the plan into a production `Trace`.

The Lean implementation uses finite sets and functions. Its tests execute
both permutation directions and replay the resulting production traces.
This file does not claim a proved runtime bound for that implementation.
The number of moved endpoint tokens is an optimization objective. It is
not the exact number of SWAP instructions.

## Cost with indexed data structures

There is an `O(n log n)` implementation of the fixed-word endpoint method,
where `n` is the word length, under the data-structure assumptions below.
This is an implementation design, not a time bound for the current Lean
evaluation.

For each value, store its birth positions `b` and output deadlines `t + R`
in one sorted event array. Combine events at the same cut. There are at
most `2n` events across all values. A sweep computes the Hall slack at each
event. Between two events, the slack is constant.

A candidate identity endpoint `c → c` reserves `[c,c+R)`. Both ends are
already events: `c` is a birth position, and `c + R` is an output deadline.
Thus there is no need to store every cut of the stack for every value.
Store the slack in a segment tree that supports a range minimum and a
range addition. Accept the candidate if the minimum in its interval is
at least one. On acceptance, subtract one from that interval. For `R = 0`,
the interval is empty and every candidate is accepted.

There are at most `n` candidates. Each range operation costs `O(log n)`.
Sorting the event arrays and grouping by value cost `O(n log n)` with
comparison maps. Tree construction and the slack sweeps cost `O(n)` in
total. The arrays and current tree states use `O(n)` live space. This
space bound assumes that old tree versions are discarded; it does not
bound total allocation for a persistent implementation.

After the scan, pair the remaining births and outputs in their stored
order. This costs `O(n)`. With constant-time indexed stack and token-map
updates, the existing schedule also needs `O(n)` work to emit its at most
`n` births and `n` swaps. The reach is fixed, so a scan of the reachable
stack window has constant cost. These assumptions give `O(n log n)` time
and `O(n)` live space for endpoint selection, matching, and trace emission
for one supplied word. They do not give an algorithm to choose a globally
optimal birth word.

The cache measurements above concern the current executable code. They
do not measure this segment-tree design.

## Trace comparison

`optimizeTraceWord` extracts a feasible birth word from an empty-source
trace without POP. It chooses the cheapest available introduction at each
birth and an endpoint map with minimum moved-token count. Lean proves a
factor-two bound against every trace with the same ordered birth values,
for both total weighted score and score above the generation baseline.
The comparison trace may use different direct or DUP instructions.

`improveTraceWord` compares this result with the supplied trace and keeps
the lower weighted score. It preserves the word, exact additions, source,
and target. It has no POP and no failure branch. Lean proves that it never
increases the input score and that it retains the same-word factor-two
bounds. The portfolio calls this API once after it selects a growing trace
with an empty source.

These results apply to a supplied birth word. They choose its introduction
methods, but do not choose the birth word. The number of moved endpoints can also
exceed the number of positions with unequal values. With reach 2, word
`b a b a` and target `a a b b`, the `a` at position 1 must move because the
other `a` is born too late for output position 0.
