# An incremental implementation of the scheduler

This is an implementation design, not a complexity theorem for the Lean list code.
Let w = 17 and N = |source| + |target|. Values are interned once. The spill set and
primitive prices are fixed for one call.

The current scheduler has three modes. The relaxed mode keeps
the earlier prefix list and local tie rules. The lineage mode also tries joined
old cycles and closed old circuits through the current top value, and uses the
lineage cost bound. The chain mode also tries open old paths from the current
top. Three regular policies run in each mode. An additional chain policy uses
the chain mode. All ten completed candidates remain in the final cost
comparison. Production replay checks their operations.
Raw candidate success is proved equivalent to Reserve in
`Shuffler/Optimality/Schedule/Soundness.lean`.

The retained local scores use `generationBase`, `sourcePressure`, the two
placement estimates, and `lineageBound`. They do not call the newer transport
area, gap-cost, forced-introduction, coupled, or combined static bounds. The
combined bound is used by the initial equality stop. An equality stop has a
proved optimal weighted score. Thus that stop cannot increase the primary
score. A production control in `Tests/OptimalityOpenChains.lean` still gives
19 SWAPs for the six original modes on the 17-value rotation; the chain
portfolio gives 17. These source facts and saved corpus comparisons support
version comparisons. Mode names alone do not establish preservation.

The equality stop also uses a proved bound on the initial state. It takes the
maximum of closed-group and top-cut entry costs, retained-lineage costs, and a
coupled retain-or-regenerate DP with a swap floor. The cut proposal is checked
against all old positions. The DP has at most 18 states. A direct implementation
of these initial-state bounds takes O(N²) time and O(N) space: each value needs
at most one linear scan, and the directed cut search can scan the old edges
once for each reached value. These checks run a fixed number of times, not once
for every candidate in every birth round.

The all-value lower-bound passes can also be shared. For the transport area,
keep each value's current prefix count difference, last update index, and
accumulated area. When a source or target occurrence changes that value, add
the elapsed length times the positive old difference, then update its count
and index. At most two values change per position. A final pass closes the
remaining intervals. For gap counts and capped gap costs, keep each value's
previous occurrence position and running sum. Indexed ids make both shared
passes O(N). Even a full shared pass for each of a fixed number of candidates
per birth gives O(N²) total time. This is an implementation argument; the
clear per-value Lean definitions have not been replaced by shared arrays.

## Shared immutable data

For each value, store its target positions in increasing order, direct price,
unit price, and whether it can be introduced. Store the target array. This takes
O(N log N) preprocessing with a balanced interning map, or expected O(N) with a
hash map. Later operations use integer value ids and arrays.

## Committed state between births

Store the actual stack in a vector, remaining requested counts, source occurrence
positions by value, a cursor into each target-position array, and current-window
counts. Also store the sums used by generationBase, sourcePressure, and
lineageBound. A committed operation updates only the touched values. The output
operation list is accumulated once.

## Candidate scoring

The birth pool has at most 52 entries before duplicate removal: the first
demanded kind, two target ranges of at most 17 positions, and the current
17-value window. It does not contain every distinct missing kind. The prefix
pool also has a polynomial bound in reach: at most two ready-cycle macros,
one joined-cycle macro, 16 top-value circuits, and 16 open paths, each followed
by at most 32 placement prefixes. Including the direct prefix gives a loose
bound of 1,152 prefix plans and 59,904 prefix/value pairs per round. Duplicate removal
and failed checks reduce that count. This is a structural upper bound, not a
measured typical count. This is a finite polynomial pool, with
no enumeration of subsets or stack states; the loose constant is substantial.

A candidate changes at most w old positions and appends one value. Keep its
changed positions and changed value counts in a local patch; do not copy the whole
stack or all count arrays. Discard the patch after scoring unless it is selected.

- generationBase changes by one unit price.
- sourcePressure changes only for values whose readable-window membership,
  multiplicity, demand count, or next-boundary reservation changed.
- lineageBound changes only for the appended value and values moved by the macro.
  Their greatest source positions are read from occurrence-position structures;
  the target maxima are fixed. Requested counts change for one kind.
- The mismatch graph contains at most w edges, so all graph work is bounded by a
  polynomial in w. The top-value circuit macro uses one breadth-first return
  path for each old edge that starts at the top value. Future target membership
  uses cached suffix counts.
- Open paths follow reverse old mismatch edges from the current top value.
  Each SWAP fixes the selected old position and puts its former value on top.
  One breadth-first traversal visits each value once and returns one path per
  reached endpoint. It includes shorter paths because a birth can stop a chain.
- Reserve fixes every position before the active w-slot suffix. In the sorted
  source-to-earliest-target pairing, these fixed copies pair with themselves.
  Only the at-most-w live source copies need evaluation. For each kind, its
  earliest remaining target positions are read from its stored ordered list;
  prefix counts give the offset. A cursor or binary search locates this offset.

These scalar updates preserve the numeric definitions. To preserve the actual
Lean choice, an implementation must also keep the candidate enumeration order,
duplicate removal order, generator tie order, and policy tie order. Equal ranks
for different next states do not permit arbitrary reordering.

Scoring therefore need not scan N values. A direct local implementation costs
poly(w) + O(w log N) per candidate. Candidate storage can be streamed, retaining
only the best candidate and a local patch. The literal Lean definitions instead
use repeated full list scans and allocate complete candidate lists.

## Exact no-growth graph construction

`ValueGraph.build` uses graph traversal, with no search over subsets, stack
states, occurrence assignments, or alternative cycle decompositions. Each
movable mismatch is one edge from its source value to its target value. A
correct top self-loop can join its value component. There are at most 17 edges.
`walk` removes an unused outgoing edge or pops a pending entry. `decompose`
repeats that Hierholzer tour on the remaining components, then forms one
occurrence permutation for the production permutation routine.

For E edges, the current edge-list `find?` and `erase` traversal takes O(E²)
time. There is no exponential dependence on reach. An array implementation
with indexed values takes O(N + E²) time and O(N + E) space for the full
construction and checks. Adjacency lists can reduce the graph pass to O(E).
The literal Lean code also has list indexing, full-range scans, and composed
permutation functions. The cycle-factor expressions in the cost proofs do
not enumerate alternative decompositions in the builder.

## Checked original-BBU candidate

The initial portfolio also calls the original mapping builder and unchanged
`BuildBottomUp.buildBottomUp`. `originalCandidate` replays its operation list
and checks the concrete target, exact additions, and absence of POP. An error
or failed check leaves the incumbent in place.

`Schedule.originalCandidate_cost` proves that this replay preserves the
original trace cost. `Schedule.build_retains_original` proves that every
accepted original result makes the portfolio succeed with no greater weighted
score. The no-growth path uses the proved optimal value-graph constructor,
so it satisfies the same comparison without running the original candidate.
This statement concerns the wrapper's default mapping, not every supplied
occurrence mapping.

With indexed stacks and source/target mapping arrays, the original mapping
builder uses nested source/target scans. The BBU loop has O(N) cursor advances
and generation retries, each with at most O(N) scan work. Its output has O(N)
operations by the bounds in `OldBBU.CostBounds`. This gives an O(N²) design for
the added call and replay. The Lean list and composed-mapping definitions are
not asserted to have that implementation bound.

## Attaining the generation baseline

The existing append candidate is proved to succeed with no greater cost than
any eligible trace that has no SWAP. An eligible trace also has no POP and has exactly the
requested additions. Its source must therefore be a prefix of its target,
and the appended values have a fixed order. Every legal generator for the
next value gives the same next stack. Choosing the cheapest generator cannot
remove a later legal operation. The proof checks the actual `appendFrom`,
including each Reserve check and the final production replay.

If the weighted SWAP price is positive, a trace at the generation baseline
has zero SWAPs. `Schedule.appendCandidate_attains_baseline` therefore proves
that the append candidate reaches that baseline whenever any eligible trace
does. `Schedule.build_attains_baseline` proves the same for the full portfolio.
The positive-price assumption holds for the C++ and EVM SWAP prices under
every allowed weight pair. A custom free-SWAP model needs the explicit
assumption: `[a,b] -> [b,a]` can then attain baseline 0 by a SWAP, while the
append candidate rejects the changed prefix. `Tests/OptimalityAppend.lean`
includes this boundary case.

## Joined old cycles without a large root graph

The current prototype calls ShortGrowth.graph to reuse its proved-safe replay
path. An optimized implementation need not materialize all future birth edges to
obtain just the old cycles:

1. Extract the old top circuit in the at-most-w mismatch graph.
2. Remove those old edges.
3. Find the remaining weak components with no future target value in them.
4. Those components are balanced. Compute their Euler circuits.
5. Splice each circuit sharing a value with the top circuit into that circuit;
   leave the other unserved circuits as separate old cycles.

This is a proposed way to obtain the old-cycle part of the augmented-root
construction. Future target membership is a cached suffix-count query. It has not
been proved to preserve the prototype's Euler traversal order, emitted operation
list, or final greedy choice. It must not silently replace that construction in
a claim about the exact current algorithm.

## Bounds and their limits

- An implementation that keeps the augmented-root graph and its edge order can
  use an O(N) adjacency-list Euler pass in each birth round. Combined with local
  scoring and streamed candidates, this gives the design bound O(poly(w) N²)
  time and O(N + poly(w)) space. For fixed EVM reach, this is O(N²) time and O(N)
space. It does not require the proposed graph compression.
- If the small old-cycle construction is shown to preserve the needed choice
  semantics, the same design suggests O(poly(w) N log N) time and O(N + poly(w))
  space. Monotone target cursors and suitable occurrence lists could remove most
  logarithmic factors. This stronger bound depends on that unfinished work.
- Neither bound is asserted for the literal Lean list implementation. No C++
  implementation or machine-checked runtime/space proof has been added.

## Keeping a chain across a birth

The additional chain policy changes only a tie between equal cost estimates.
It prefers a birth that leaves the same value in the top two slots when an
unfinished old mismatch still wants that value. The birth then keeps the
value available as the next chain pivot. This check scans the fixed-size
active window and adds no graph-state search or numerical penalty.

The repeated-chain regression needs four births. The earlier policies return
60 gas before normalization; this policy returns the 45-gas trace at the
proved static bound. The normalized earlier candidate set has 48 gas.
`Tests/OptimalityChainContinuity.lean` retains all nine raw 60-gas controls and
checks the new result, baseline 12, and static excess 33. The first different
birth in the earlier trace does not force a loss: a different continuation
still costs 45. The second birth does force a loss.
It makes the next wrong boundary depend on a sole copy in a correct old slot.
That slot must be disturbed and restored. The proved
`GroupEntry.correctBoundaryBound_le_swapCount` gives eleven required residual
SWAPs. A checked continuation attains this bound at 39 gas, for a total of
51 gas with the prefix. The test checks both the bound and the replay. The
policy's correctness uses the same Reserve and production-replay checks.

## Complete-constructor operation count

A source check gives a conservative SWAP count of `k + 34` for
`Placement.buildOfReserve`, where k is the number of required additions.
There are at most 17 initial working-source slots. `prepare` either emits no
operation or consumes one of these slots with `placeExisting`. The recursive
constructor consumes each other old slot once. Each such call uses at most
two SWAPs. Each of the k `generateAndPlace` calls emits one birth and at most
one SWAP. Thus the preparation call is already included in the 34 term.
This argument does not depend on the length of the frozen prefix. It has
been checked against the source, but no Lean count theorem is stated yet.

## Shared prefix-introduction scan

The new `PrefixIntroduction.requiredDirect` definition protects all source
value kinds except the tracked value. With indexed value counts, these
per-value cutoffs can share one target scan. Let n be the source length, O
the number of old-kind target values seen so far, s(v) the source count, and
t(v) the target-prefix count. A source-present value with n−s(v)≥16 reaches
its cutoff when O reaches the key `n−s(v)−15+t(v)`. Reading an old-kind value
x increments O and only x's key. Update x's key before checking reached keys.
All source-absent values share the cutoff where O first reaches n−15.

The keys and O only increase. Integer buckets over O(N) possible key values
can record reached keys in O(N) total time and O(N) space. A key update may
leave a stale bucket entry; each entry is inserted once and checked once.
Record t(v) at each cutoff, then use total target counts to test later demand.
One scan of occurrence lists handles all values absent from the source.
Thus this bound has an O(N) shared-scan implementation design for each
candidate, consistent with the earlier O(N²) planner design. The literal
Lean code scans protected lists per value. No scan-equivalence or runtime
proof for this optimized version has been added.

## Normalization before comparison

Every proposed built trace now passes through `SwapRuns.normalizeBuilt`
before the portfolio compares its cost. The complete fallback passes through
it once. This replaces each SWAP run by minimum placement for that run's
endpoints. Birth choices, exact additions, and birth order stay unchanged.
The original BBU and complete-constructor bodies stay unchanged.

The normalized-original and normalized-complete comparison bounds are proved.
`Schedule.Comparison` also bounds the result by every normalized raw strategy
candidate in the requested list, including the static-bound early-return
case. The saved wide-LOAD raw-chain fixture now returns 127 bytes from the
actual `Schedule.build`; the raw original BBU still has 146 bytes. See
`docs/swap-run-normalization.md` for the exact proof and test scope.
