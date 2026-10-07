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

These results apply to a supplied birth word. They do not choose the birth
word or its introduction methods. The number of moved endpoints can also
exceed the number of positions with unequal values. With reach 2, word
`b a b a` and target `a a b b`, the `a` at position 1 must move because the
other `a` is born too late for output position 0.
