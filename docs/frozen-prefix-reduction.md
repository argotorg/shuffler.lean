# Remove a fixed prefix before computing a bound

Let `k ≤ source.length - 17`. All indices count from the bottom of the stack.
The first `k` source values are outside SWAP and DUP reach. A trace without
POP cannot reduce the stack height. Those values therefore stay outside reach
for the full trace.

`FrozenPrefix.exists_drop` proves that every such trace has a reduced trace
from `source.drop k` to `target.drop k`. The reduced trace has the same
operations, in the same order, and the same added values with the same counts.
It also has no POP. This removes the initial fixed prefix once. It does not
discard newly frozen positions as the trace runs.

`FrozenPrefix.exists_lift` proves the converse construction. Any trace without
POP can run above any fixed prefix. Each instruction keeps its depth from the
top. This direction needs no height assumption.

For a fixed full target, the prefix must match:

```text
target.take k = source.take k
```

`FrozenPrefix.exists_operations_iff` proves an exact equivalence for each
specified operation list. A full eligible trace with that list exists exactly
when the prefixes match and a reduced eligible trace with that list exists.
Eligibility fixes the spill set and the multiset of additions, and excludes
POP. No Reserve hypothesis is needed.

`FrozenPrefix.exists_cost_iff` gives the same equivalence for each specified
gas/byte pair. It holds for every `PrimitiveCosts` model: the operation lists
are identical, so their summed costs are identical. Thus the reduced and full
problems have the same attainable cost pairs when the prefixes match.

`FrozenPrefix.score_lower_bound_of_drop` transfers any proved lower bound on
the reduced problem to each eligible full trace. For example, one can compute
the generation baseline and a placement bound after removing the fixed prefix.
An old occurrence in that prefix can no longer count as an available source or
cancel a gap among the active occurrences. To report excess above the original
baseline, first transfer the full reduced score bound, then subtract the
original baseline. The two baselines need not be equal.

`FrozenPrefix.baseline_le_drop` proves that removing source values cannot
decrease the baseline. This holds for every primitive cost model. A removed
source kind changes its surcharge from zero to a natural-number introduction
premium. `FrozenPrefix.twiceExcess_of_drop` uses this fact to transfer a proved
factor-two guarantee on a reduced trace to a full trace with the same cost.
The result compares against the original full problem's baseline.

The specialization `exists_window_eligible` removes the entire initial frozen
prefix. Its source is `window source`, which has at most 17 values. Its target
can be longer. For an initial stack of at most 17 values, the removed prefix
is empty.

The proof modules are in `Shuffler/Optimality/FrozenPrefix/`. Import
`Theorems.lean` for the trace and cost equivalences, or `Approximation.lean`
for the baseline and factor-two transfer results. They do not change `Trace`,
the planner, or its operation semantics. `Tests/OptimalityFrozenPrefix.lean`
checks maximum-depth SWAP and DUP, PUSH, LOAD, cost preservation, a changed
frozen prefix, and the height-17 boundary where removing one slot is invalid.

The runtime `staticExcess` wrapper now applies this reduction. If the source
has a frozen prefix, it recomputes baseline plus the core bound on the active
suffix, subtracts the original baseline, and takes the maximum with the full
bound. The height-at-most-17 path keeps the core bound. The saved frozen-gap
test now has excess bound 2. A value available only in the frozen prefix has
original baseline 1, reduced baseline 34, and excess bound 33.

The full Shuffler, Tests, and native benchmark build passes 3005 jobs after
this integration. The new bound and certificate audit uses only standard
axioms. The pinned executable is `/tmp/optimality-bench-frozen-v13`, with
SHA256 `0f6c8667f24b84e12a33eba5dda1aa0e264866b8df25fa826568245e715164e8`.
Its runtime change from v12 is this bound wrapper; no scheduler policy was
added. Targeted v12/v13 comparisons are recorded separately in Bench.
