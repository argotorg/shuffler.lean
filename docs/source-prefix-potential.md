# Source-prefix cycle bound

`SourcePrefix.run f h` runs the first `h` stages of the existing virtual birth
schedule. Let `P` be its swap product. The remaining assignment is `f * P`.
This definition does not produce a trace from a nonempty source.

For a chosen source top, let `c` count the cycles of `P` that do not contain
that top. Fixed points do not count. Let `q` count the full cycles of `f` that:

- have two positions;
- lie inside the source prefix;
- do not contain the source top.

Lean proves `2 * c ≤ K(f) + q`, where `K(f)` is the minimum number of swaps
when each swap can use any two positions. With `top + 1 = h`, the definition
of `q` is exactly the number of two-cycles strictly below the source top.

The proof uses the actual `SourcePrefix.run` program. It proves these facts:

1. Every prefix cycle lies inside one full cycle of `f`.
2. A full cycle inside the prefix is complete. On its positions, `P = f⁻¹`.
3. A full cycle with a future position leaves at least one position out of the
   prefix support. Each prefix cycle uses at least two of the other positions.
4. A complete cycle of length at least three has enough units in `K(f)` to pay
   for its prefix cycle. A complete two-cycle below the top needs one more unit.
5. Full-cycle supports are disjoint, so the local bounds add.

The main theorem is `SourcePrefix.cycles_away_bound` in
`Shuffler/Optimality/BirthPlacement/SourcePrefix/Bounds.lean`.
`SourcePrefix.closedPairs_eq_below` gives the source-top form of `q`.

The tests run the prefix program on an empty prefix, a two-cycle, a cycle through
the top, a longer complete cycle, and one open cycle with two prefix cycles.

This is a cycle-potential bound. It does not yet supply a source-plan realizer
or a general optimizer for source assignments.
