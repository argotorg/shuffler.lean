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

`SourcePrefix.permutation_cost_add_remaining` proves
`K(P) + K(f * P) = K(f)`. Thus an optimal top-swap entry permutation followed
by the remaining birth schedule has count `K(f) + 2 * c`. The entry uses
`P⁻¹`, since the stack permutation API sends old positions to new positions.
`SourcePrefix.entry_cost_add_remaining` proves this count identity. It does
not assert that the entry permutation meets the physical depth limit.

The tests run the prefix program on an empty prefix, a two-cycle, a cycle through
the top, a longer complete cycle, and one open cycle with two prefix cycles.

## Production source plans

`SourcePlan` adds an initial source to the birth-plan data. The source values
must agree with the first token positions. A source token below the initial
SWAP window must stay fixed. The boundary is `index + 17 < source.length`:
at source height 18, position 1 is reachable with SWAP16, but position 0 is not.
The remaining conditions are the birth deadlines and introduction availability.

`SourceEntry.build` restricts `P⁻¹` to the source positions and runs the existing
production permutation routine. Its proof shows that every moved source
position is reachable. `realizeSource` then emits the supplied births and runs
the remaining settle stages. It always returns a production trace, with no POP,
the exact additions, and the prescribed birth events. Its SWAP count is exactly
`K(f) + 2 * c`.

`traceSourcePlan` extracts these conditions from any production trace without
POP. This includes the source-window condition. `canonicalizeTraceAssignment`
realizes that plan. Lean proves that it preserves the ordered birth events
and additions and emits at most twice as many SWAPs as the supplied trace.
It also proves factor two for total weighted gas/byte score and score above
the generation baseline.

The comparison can use any trace with the same labelled assignment, provided
the plan's introduction cost is no greater. The canonical wrapper preserves
the input methods, so its unconditional comparison is with that input.

`SourcePlan.cheapest` chooses the least-cost available method at each absolute
birth height, including the initial source height. `optimizeTraceAssignment`
uses those methods before realization. It preserves the ordered birth values
and additions. Lean proves factor two for weighted total score and score above
the generation baseline against every no-POP trace with the same labelled
assignment. The comparison trace can use different LOAD, PUSH, and DUP choices.
Here, "same assignment" compares the other trace's extracted assignment with
the supplied plan's assignment. There is no theorem here that re-extracting an
assignment from the output trace returns the supplied assignment.
Tests cover a source LOAD replaced by DUP, DUP replaced by PUSH0, and the
DUP16/DUP17 source boundary.

This does not choose an assignment for a new input.
A general source-assignment optimizer remains open. Minimizing this potential
would be one sufficient method; the proofs do not require that to be the next
algorithm.
