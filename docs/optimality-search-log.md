# Placement cost search log

## Deadline and scope

This work started on 2026-10-06 near 23:57 UTC. The authorized end time is
2026-10-07 08:00 UTC (10:00 CEST). No commits or pushes are authorized for this
work. The starting commit is `4b8dfa77f43080089bd880d82cdcdccce3569419`.

The problem fixes the spill set, source, exact target, and exact multiset of
additions. A new trace suffix must contain no POP. Candidate planners must
succeed exactly when `Reserve` holds. Selection uses a supplied weighted sum
of static gas and encoded bytes, and must not cost more than `Placement.build`.
The C++ design target is O(n²) worst-case time and space, preferably less. This
is an implementation-model requirement; no C++ implementation is requested.
The Lean implementation must be small, clear, and easy to inspect. Algorithm
definitions are kept separate from proof details and checked trace wrappers.
Gas and byte weights are generic inputs, including endpoint and mixed weights.
An excess-cost factor-two bound is a research target, not an established fact.

## Roles and files

- `/root`: coordination, scope, user communication.
- `/root/prove_static_predicate`: this log, `Optimality/ValueGraph*.lean`, exact
  no-growth construction, short-stack construction, proofs, final integration.
- `/root/predicate_explainer`: `Optimality/Replay.lean` and
  `Optimality/Schedule*.lean`, general placement planner and weighted selection.
- `/root/static_prefix`: oracle, benchmarks, and counterexamples.

Focused module checks can run separately. The integration lead serializes full
`lake build Shuffler Tests` runs. Existing `Stack`, `Trace`, BBU definitions, and
the complete placement fallback remain unchanged.

## Initial proof and test status

- `Placement.canPlace_iff_reserve` proves exact no-POP feasibility.
- `Placement.build` constructs a typed trace exactly when `Reserve` holds.
- `Optimality/Cost.lean` defines static gas, byte costs, and weighted and Pareto
  specifications. It does not prove a cost-optimal planner.
- The last complete build passed 1325 jobs. Cost tests included 24 runtime
  checks and 18 static proofs. The audit found no `sorryAx`.
- The no-growth graph formula and the final-height-at-most-17 graph formula
  have mathematical arguments and finite test evidence. Neither graph formula
  is currently a Lean theorem.
- Weighted generation has a mathematical formula and finite test evidence.
  It is not currently a Lean theorem.

## Checkpoints

Planned checkpoints: first integrated candidate and baseline benchmark by
02:00 UTC; substantive iterations until 06:30; freeze the best implementation
near 07:00; final validation and review from 07:00 to 07:45; report by 08:00.

### 2026-10-07 00:00 UTC

The integration lead resumed with a clean working tree. The structural notes
in `/tmp/OptimalityStructuralNotes.md` specify the candidate construction.
The no-growth mismatch graph has one edge `source[i] -> target[i]` for each
mismatched movable position. An Euler circuit per value component gives an
occurrence permutation. The initial top must join its component even when its
value is already correct; otherwise the construction can emit an extra swap.
The proposed count is `m + k - b`, where `b` is 2 for a mismatched top, 1 for a
correct top whose value occurs in the graph, and 0 otherwise.

Public flat instruction and checked replay definitions belong to the schedule
agent. Value-graph construction can emit these instructions or a typed trace.

### 2026-10-07 00:06 UTC

`ValueGraph/Defs.lean` implements the no-growth Euler occurrence assignment.
`ValueGraph/Permute.lean` proves that successful production `Permute` traces
contain no POP and no additions. Its checked wrapper carries the existing
exact swap count for the supplied occurrence permutation. Both modules pass
focused Lean checks. Completeness and value-optimality of the new occurrence
assignment are still open.

The user requested a commit of the cost model. Commit `4b8dfa7` already contains
the cost model, its tests, and its documents. There were no later cost-model
changes and the index was empty, so no new commit was made. The separate
overnight planner changes remain uncommitted.

### 2026-10-07 00:20 UTC

The no-growth constructor is now proved complete in Lean.
`ValueGraph.build_succeeds_iff_reserve` states success exactly when
`Reserve spills source target 0` holds. The construction does not call the
placement fallback. The proof establishes balanced mismatch edges, closed
Euler trails, an exact edge partition, disjoint occurrence cycles, the concrete
endpoint, and SWAP reach. A focused build and all sixteen graph tests pass.
The minimum-cost formula over all equal-occurrence assignments remains open.

`ShortGrowth/Graph.lean` now implements the augmented root graph, a directed
cycle through the old top, insertion of unserved value components into that
cycle, and one old-edge trail per birth. Its checked flat-operation wrapper is
being compiled and tested. This new growth construction has no completeness
or optimality proof yet.

### 2026-10-07 00:32 UTC

The checked short-growth constructor passes seventeen regression guards. The
first native oracle run found its cost exact on all 500 small cases (6,285
oracle states). The no-growth constructor was exact on all 42 no-growth cases
in that sample. These are finite tests, not minimum-cost theorems.

The padded-prefix extension is only a candidate. A boundary sample confirmed
that it can lose a cheap source before a later birth. For example, a value at
DUP16 depth can be copied before a zero birth, while a plan that keeps the
final prefix fixed must introduce it again. Thus the short-stack cost argument
is restricted to full final length at most seventeen. A 120-case boundary run
(93,481 oracle states) found the general scheduler exact in all cases; raw
short-growth returned 66 plans, of which 48 were exact and 18 cost more.

The integration lead also proved that completed no-growth Euler circuits use
disjoint value groups. The next proof target is the lower bound from those
groups: required moved positions below top, plus one cycle for every group
whose value label differs from the initial top label.

The generation lower bound `B` is now a Lean theorem in
`Optimality/Baseline/Theorems.lean`. A legal trace whose weighted cost equals
`B` is proved weighted-optimal. The scheduler uses this certificate to stop
search when equality holds. `B` is a cost lower bound; the *incumbent* is the
existing complete plan from `Placement.build`. The separate theorem that the
selected plan costs no more than the incumbent is a dominance guarantee. It
does not prove a multiplicative or excess-cost approximation bound.

### 2026-10-07 00:36 UTC

First full integration passed `lake build Shuffler Tests optimality_bench`
(2665 jobs). Public `Shuffler` imports the new scheduler and proof modules.
A fresh audit through that public import checked the no-growth constructor,
the disjoint-value proof and lower bound, the generation lower bound and its
optimality certificate, and the scheduler's success, reserve, and incumbent
cost theorems. All use only `propext`, `Classical.choice`, and `Quot.sound`;
none uses `sorryAx`. There are 78 new runtime regression guards across replay,
baseline, no-growth, short-growth, and scheduler tests at this checkpoint.

The optimized implementation model interns relevant values in O(N log N), then
uses integer IDs, array counts, window marks, and target occurrence lists.
The window width is fixed at w=17. There are at most O(w²) candidates per birth
and at most N births. With O(N) score scans, total time is O(w²N²+poly(w)N),
and streaming candidate selection uses O(N+poly(w)) space. This is an informal
bound for that implementation model. The Lean list and multiset representation
has separate costs and is not claimed to attain this bound.

### 2026-10-07 00:43 UTC

`ValueGraph.buildCertified` now returns an `OptimalTrace` only after checking
a finite value-label certificate and equality with its lower bound. The
`min_swaps` proof compares against every production trace with no POP and no
additions. `OptimalTrace.weightedOptimal` proves minimum weighted cost for
every cost model and every gas/byte weight pair. Fifteen certification guards
pass. This is a proved optimum for each returned result, not merely a test
against a small oracle.

Completeness of this additional certificate checker is still open. The
separate `ValueGraph.build` remains proved complete exactly under `Reserve`
with empty additions. No minimum-cost statement depends on assuming that the
certificate check always succeeds.

## Remaining proof work

- ShortGrowth has checked exact traces, but still has no separate general
  completeness or optimality proof. Its padded-prefix extension is a candidate.
- No universal excess-cost factor-two theorem is established for the general
  scheduler. Conditional per-input certificates are a separate claim.
- Stronger static lower bounds for general growth remain a research task.
- The implementation complexity bound describes an optimized representation;
  it is not a formal Lean runtime bound.
- Repeat the full build and public axiom audit after later changes.

### 2026-10-07 00:56 UTC

No-growth optimality is now unconditional. The theorem
`ValueGraph.buildCertified_succeeds_iff_reserve` proves that the certified
solver succeeds exactly when `Reserve spills source target 0` holds.
Every returned result has minimum SWAP count among all eligible production
traces, and therefore minimum weighted cost for every primitive cost model
and weight pair. The proof includes duplicate values, a correct initial top
that joins a moved group, and a frozen prefix below the swap window.

The new proof modules establish that each circuit contains a mismatch, the
finite label checker always passes, the graph edges are exactly the support
of the assigned permutation, and the emitted count equals the group lower
bound. The focused build passed 1325 jobs. The public build and axiom audit
are in progress at this checkpoint.

The scheduler agent also proved
`Schedule.candidate_succeeds_iff_reserve`: the raw checked scheduler succeeds
for every feasible input, for all three policies and all cost/weight choices.
The proof covers the original candidate lists, one-birth progress, fuel, and
exact replay. The complete placement fallback remains in the selected
portfolio to guarantee incumbent cost dominance.

The current finite oracle evidence is recorded in `Bench/evidence-v4.json`.
That manifest includes executable and artifact hashes, seeds, limits, result
counts, and reproduction commands. The full generated reports remain in
`/tmp`. The next native snapshot will add large certificate-only coverage and
rerun the saved growth boundary cases.

### 2026-10-07 01:03 UTC

The public build passed `lake build Shuffler Tests optimality_bench` with
2812 jobs. The audit through `import Shuffler` covers certified no-growth
completeness and optimality, raw scheduler completeness, and Lineage. It uses
only `propext`, `Classical.choice`, and `Quot.sound`. The v5 runner is pinned
at `/tmp/optimality-bench-integrated-v5`, SHA256
`0ec8b1fa92ed43a2089a600af232840b4498f58bd3cd1cdc25488912f17deae8`.

`Approximation/Build.lean` now provides a per-input factor-two certificate.
`certifyTwiceLineage` checks `cost ≤ B + 2X`, where `X` is the proved summed
lineage/reintroduction excess bound. Every returned result proves
`candidateCost + B ≤ 2 * competitorCost` for every eligible production trace.
A second theorem proves equivalence with the usual subtracted excess formula.
Ten actual-replay tests cover baseline equality, an exact factor-two boundary,
rejection above that boundary, and rejection of an optimal plan when this
particular static bound is too weak. A failed check is not a feasibility or
cost-quality conclusion. This is not a universal approximation theorem.

### 2026-10-07 01:11 UTC

The plain `ValueGraph.build` now has direct `build_min_swaps` and
`build_weightedOptimal` theorems. Callers can use the exact no-growth result
without running the finite certificate checks at runtime. The native v5
certificate-only suite checked 1,000 cases at heights 0 through 128, with
alphabet sizes 2, 3, 5, and 17. All 1,000 returned an `OptimalTrace`; this suite
skipped the oracle and records that fact.

`OldPositions.mismatches_le_swapCount` proves a further lower bound for every
no-POP production trace: each original mismatched position below the initial
top requires a lower-slot selection by SWAP. `requiredSwaps_le_swapCount` also
adds a one-SWAP floor when only the initial top changes. The proof uses the
fact that births preserve the old prefix. Twelve old-position guards pass.

`staticExcessLowerBound` takes the maximum of the old-position cost and the
summed lineage/reintroduction bound. The maximum is proved; the two bounds
must not be added because they can charge the same swaps. `certifyTwiceStatic`
uses this bound. Fourteen approximation guards now pass, including a case
that the lineage-only check rejects and the static maximum certifies. The
focused build passed 1264 jobs. Public/native rebuild is held while the
scheduler agent tests the next bounded policy change.

### 2026-10-07 01:27 UTC

The v6 public/native build passed 2826 jobs. The pinned runner is
`/tmp/optimality-bench-integrated-v6`, SHA256
`a9553564b9bbaeb15c80c9d3d8a3add1325caa3fdf145153444ddd0c4acb2fa8`.
The public audit includes plain-builder no-growth optimality, summed
reintroduction/lineage, old-position bounds, and factor-two certificates. Only
standard axioms appear. One native link attempt found a stale generated
initializer from direct Lean output; rebuilding the affected Lake artifacts
resolved it without a source change. Agents now use Lake to generate imported
artifacts, and direct Lean checks omit `-o`.

`GroupEntry.Certificate.bound_le_swapCount` now proves the closed-group entry
term. Its bound is the number of original mismatches below top plus one for
each certified closed value group. The initial top has no group label, source
and target labels agree at each old position, every requested birth is
unlabelled, and each group has a mismatched representative. The proof counts
lower-slot SWAP selections. Before the first selection of a closed group,
its values are absent from top. That first selection cannot fix its lower
slot, so it contributes one extra step. Selection counts for disjoint groups
sum to at most the trace's total SWAP count.

A finite weak-component finder now proposes these labels from the movable
window. `GroupEntry.checked` verifies the full initial-state certificate.
`GroupEntry.requiredSwaps` takes the maximum of its bound and the old-position
floor. Sixteen graph-entry guards pass, including rejected bad labels and an
actual growth trace that attains the bound. The focused build passed1271 jobs.
The pure `staticExcess` now uses this proved graph bound with the lineage bound.

The scheduler's later focused checkpoint passed1354 jobs and26 guards. It uses
the proved exact no-growth builder directly and applies an equality stop only
when both weights are positive, so a zero-weight cost tie can still improve
the other cost. Its new public theorem audit also uses only standard axioms.
See `docs/optimality-scheduler-implementation.md` for the separate optimized
O(N²) implementation design and its explicit limits.

### 2026-10-07 01:34 UTC

New user requirement: bound the worst-case trace cost of the original
`buildBottomUp` and use it for comparison. This is part of the same search.
The original definitions stay unchanged. The scheduler agent will inspect
per-operation counts and successful-run excess ratios. The benchmark agent
will add an original-algorithm comparator with explicit failure statuses and
separate scopes for the BBU suffix and final placement.

`GroupEntry.topCut_lowerBound` now builds (1252 jobs). For any value cut, its
original slots must be below the initial top and keep cut values in the
target. The wanted value at the original top must be in the cut. Then its
original mismatches plus one are at most the selections of its slots and the
original-top slot. The proof splits at the first birth if the old top is
never selected as a lower slot. It applies to all no-POP production traces.
The finite top-cut checker and its combination with closed groups are still
to be written.

Transport, its scan equivalence theorem, CoupledBound, and coupled-bound
guards built (1262 jobs). The coupled DP uses at most18 entries and jointly
prices retained values, regeneration, and a proved swap floor. Integration
uses `GroupEntry.requiredSwaps` for that floor; the graph bound is also kept
separately because the DP caps its floor at17.

### 2026-10-07 01:39 UTC

The checked top-cut bonus is now part of `GroupEntry.requiredSwaps`.
`TopCutCertificate.bound_le_swapCount` adds it to all closed-group bonuses.
The cut contains the wanted old-top value, excludes the source old-top value,
and is closed under every old-position edge below top. Its source values are
all unlabelled by the closed-group certificate. A forward graph walk proposes
the cut; the finite checker verifies all conditions. The resulting bound is
original mismatches below top plus closed groups plus the optional top-cut
bonus, combined by maximum with the old-position floor.

There are now29 GroupEntry guards and18 approximation guards. Positive
examples attain the bound of two swaps for `[a,b] → [0,a,b]`, and five swaps
for `[a,b,c,d,e] → [b,a,0,d,c,e]`. Negative checks cover a cut containing the
source top, a cut that is not closed, a cut that omits the wanted top, an
empty source, and a cut that overlaps charged group labels. Actual production
replay witnesses attain both bounds. The focused build passed1287 jobs.

`staticExcess` now takes the maximum of the graph-entry, lineage, and coupled
DP bounds. The coupled DP receives the proved graph-entry swap floor. Its
new attainment theorems prove that the finite DP computes the minimum of its
stated retained/regenerated choices; this does not prove that the trace
planner is optimal. The next full build will pin these changes as v7.

### 2026-10-07 01:45 UTC

The v7 full `Shuffler`, `Tests`, and native-runner build passed2863 jobs.
The pinned executable is `/tmp/optimality-bench-integrated-v7`, SHA256
`2ad9828e168315872dbd214bf1a933d27b42e3dc687839919023e56e35a31362`.
It includes the checked top-cut bonus, the coupled DP, the top-value circuit
macro, and the benchmark algorithm-selection option. The updated public
audit passed and reports only `propext`, `Classical.choice`, and `Quot.sound`.

A source review of the first `Placement.buildOfReserve` constructor found
a linear optimized construction loop for fixed reach16: one target position
per recursive call, at most two operations per position, and a working suffix
of at most17 values. Dense value ids and count arrays give O(N) time and O(N)
space including output. Hash interning gives expected O(N) preprocessing;
comparison maps give O(N log N). The literal Lean implementation has repeated
list membership/erase, growing-prefix append, and trace concatenation over
the recursive suffix. It can therefore use O(N²) time. Trace constructors
retain old stack lists at runtime, so repeated prefix copies can also use
O(N²) space. This estimate is separate from the later scheduler design.

The requested inventory/flow research found an exact-looking feasibility
abstraction but no cost-preserving reduction yet. At full height, one round
removes the next fixed target value from the17-value bag, then inserts a
required birth. A hard birth must have a copy in the residual16-value bag.
Every such transition can be lifted with at most two placement swaps plus
the birth, but that bound is too large for a factor-two excess guarantee.
The bag omits physical transport during long gaps. A usual cache of value
kinds also omits exact-copy conservation: emitting a value consumes one
active copy, and the old copies cannot be evicted before their target slots.
No O(N²) flow reduction or universal factor-two theorem is claimed.

### 2026-10-07 02:05 UTC

The repeated-gap lower bound `GapCount.requiredSwaps_le_upwardCount` is now
proved for production traces. For occurrence positions p₁<…<pₖ, define

```
Q = ceil(p₁/16) + sum floor((pᵢ₊₁ - pᵢ - 1)/16),
```

and set Q=0 when the value is absent. A DUP adds a gap of at most 16 and
does not increase Q. A SWAP that moves the value upward increases Q by at
most one. A downward move does not increase it. Thus every no-POP trace with
no direct introduction of that value satisfies
`Q(target) - Q(source) ≤ upwardCount(value, trace)`. The executable definition
uses the linear `findIdxs` scan and a gap fold; ordered-list and trace proofs
are in separate files. Unlike the old last-position bound, Q detects several
separate long gaps and is not weakened by repeated copies after a gap.

The coupled DP now uses the maximum of transport, the old retained bound,
and Q difference on its retained branch. Twenty-eight guards pass, including
the four saved v7 planted gaps, the 16/17 gap boundary, multiple separated
long gaps, a frozen prefix, and a LOAD trace that shows why the no-direct
premise is required. All four saved gap costs now equal baseline plus the
proved static bound. The focused build passed 1291 jobs. A focused axiom
audit reports only the three standard axioms.

Before this proof, the Q formula passed 405,787 local operation checks,
11,985 exact-oracle costs, and 1,070 legal witnesses. The later capped monetary
gap formula also passed finite tests, but remains experimental. It is not
part of the proved public bound yet. The benchmark agent is proving a
separate surcharge statement for introductions after the first.

### 2026-10-07 02:16 UTC

The capped monetary gap bound is now proved and part of `staticExcess`.
`GapCost` prices each separate Q gap by the SWAP price and caps it by the
direct-introduction premium when the value can be introduced directly. It
omits the leading term for values absent from the initial source, because
baseline already pays for their first introduction. The trace theorem bounds
the potential increase by upward SWAP cost plus premiums for later direct
introductions. Its sum combines with `GenerationSurcharge` to prove
`baseline + GapCost.bound ≤ score` for every eligible production trace.
The static certificate keeps the maximum of this and the earlier bounds,
because their charges can overlap. There are22 GapCost guards and seven
GenerationSurcharge guards. The focused combined build passed1300 jobs.

For byte weights and a spilled value a, source `[a]` and target
`[a,0×16,a,0×16,a]` give baseline34 and gap bound2. A trace with32 PUSH0 and
two LOADs has cost36 and attains the bound. The earlier coupled bound gives1
on this input. For an empty initial source and the same target, baseline36
and gap bound2 account for the first LOAD separately. The exact-oracle check
of these fixtures is pending.

The original BBU cost results are now public in `OldBBU.CostBounds`.
A successful call has a suffix with no POP and exactly the requested births.
Its SWAP count is at most `2N + k + 24`; the final production permutation
uses at most24 SWAPs. Separate theorems give C++ gas and byte bounds.
The default `[0] → [0,0]` result uses DUP, while PUSH0 attains baseline.
This proves that original BBU has no finite excess factor. Seven production
guards and the nine-result axiom audit pass. See `docs/old-bbu-cost.md` for
the definitions of N and k and the precise theorem scope.

The v8 full `Shuffler`, `Tests`, and native-runner build passed2903 jobs.
The fixed executable is `/tmp/optimality-bench-integrated-v8`, SHA256
`86ff3f56a00e57200386105f0abc7e8a5a1186b843af5266cfd13f09e9376fa1`.
It includes Q, capped F, GenerationSurcharge, and the public OldBBU cost
proofs. The extended public axiom audit passes and reports only `propext`,
`Classical.choice`, and `Quot.sound`. The benchmark agent has this snapshot
for the saved and planted gaps. The scheduler agent can now integrate its
separate open-chain candidate after this fixed checkpoint.

### 2026-10-07 02:23 UTC

The v9 full build passed2906 jobs. Its runner is
`/tmp/optimality-bench-integrated-v9`, SHA256
`60eb38ec9099631f3948ea346592e5d3f057b10fc50ef25e6e442f8b47466a9e`.
The public axiom audit passes with the same three standard axioms. This
snapshot adds the open-chain scheduler modes and their benchmark names.
The original six strategy candidates remain in the default selection; three
chain modes are added. A rotate17 test takes17 SWAPs with the new default
and19 with the six old modes. The graph helper follows at most16 paths;
the candidate pool remains bounded for fixed EVM reach.

The exact oracle confirms both capped-F fixtures: the source-present case
has baseline34, bound2, and optimum36 after6,663 oracle states; the
source-absent case has baseline36, bound2, and optimum38 after6,681 states.
Both results include valid production replays and are saved in
`Bench/optimality-regressions.jsonl`.

`ForcedIntroduction.reserve_singleton_of_no_direct` now proves a stronger
necessary condition for a retained source. For any value v added by a
no-POP trace with no direct introduction of v,
`boundary(source,target,additions) + {v} ≤ window(source)` as multisets.
This applies even when v can be pushed or loaded. It forces an introduction
when all initial v copies are below the movable window, or when the first
fixed output consumes the only window copy of v. `Required.directCount_pos`
is the executable-test contrapositive.

The cost corollary sums mandatory premiums only over source-present values
and combines them with the actual SWAP cost. Source-absent values pay their
first introduction through baseline. Eighteen guards and the six-result
axiom audit pass. For source `[0×16,a]`, target `[a,0×16,a]`, and missing
`{a}`, the forced LOAD premium is3 bytes for a two-byte address, while a
PUSH32 value has premium32. Valid `SWAP16; LOAD` and `SWAP16; PUSH32` traces
cost5 and34 bytes. Lean examples also prove that all eligible traces cost
at least5 and34 bytes respectively, using the graph SWAP floor. The old
static bound was1 on both. Coupled-bound integration now passes1304 jobs.
For a forced value, the finite DP keeps only the unconditional transport
requirement and adds its mandatory premium outside the DP. Its proof
subtracts that premium from actual introduction accounting, then restores
it after summation. The generic DP theorems are unchanged. The static bound
keeps the maximum with capped F to avoid overlapping charges.

### 2026-10-07 02:44 UTC

Two further full checkpoints are fixed. The v10 build passed2926 jobs;
runner `/tmp/optimality-bench-integrated-v10`, SHA256
`768b8d0a5b3f2fd2420d5fdab8cbbf2a6b2f5877412f04a9be68b3130c9d915d`.
It includes the forced-introduction DP constraint and the checked original
BBU candidate. The v11 build passed2940 jobs; runner
`/tmp/optimality-bench-integrated-v11`, SHA256
`8477dbee7b1f74012d47a7de609adcb8981c050ace141015017a64b64ad9e656`.
It adds the per-value accounting bound and public append proofs. Both public
axiom audits pass with the three standard axioms.

`ValueAccounting` takes a maximum separately for each value, then sums over
source and target values. One term is the capped gap bound; the other is
unconditional transport cost plus a mandatory source-present introduction
premium. Both use the same per-value budget: upward SWAPs of that value plus
its later direct introductions. Different values have disjoint such budgets.
This sum can exceed the maximum of aggregate bounds, and it provably
dominates aggregate `GapCost.bound`. It replaces that aggregate term in the
static maximum. Sixteen guards and the existing gap/certificate tests pass
in1307 jobs. The focused five-result axiom audit also passes.

For source `[0×16]`, target `[a,0×16,a]`, and a LOAD address using PUSH0,
the zero transport term is1 and a's gap term is1. Their sum gives2, while
each old aggregate bound gave1. The actual `LOAD; SWAP16; LOAD` trace has
baseline3 and byte cost5. Wider LOADs reveal a further need: both births
must introduce a directly, regardless of the cheaper gap price.

`PrefixIntroduction` now proves that general count result. Choose any set
of protected value kinds K and a tracked value v outside K. If the source
has at least16 K-valued copies and the target prefix before c has at most
`source.countK - 16` such copies, then

```
target.take(c).count(v) + [v occurs in target.drop(c)]
  ≤ source.count(v) + directCount(v, trace).
```

A DUP of v before height c+17 would leave at most15 protected copies in
its readable region. Too many protected copies would then be frozen below
c, contrary to the target prefix count. All later DUPs stay above c. The
proof counts every v in the prefix plus one seed for any remaining v demand.
It uses production traces and does not require v to be absent initially.

The executable `requiredDirect` protects all source kinds except v and
chooses c just before the protected target occurrence that would exceed the
allowed prefix count. It subtracts existing source copies of v. The theorem
`requiredDirect_le_directCount` and20 guards pass1260 jobs. Guards include
prefix lengths1/2/3/8/17/33, mixed absent values, remaining demand after the
prefix, source-present consumed copies, and a15-copy negative case with an
actual valid DUP. Cost integration is delegated to the benchmark/bound agent.
The current native v11 snapshot predates this new count theorem.

### 2026-10-07 02:58 UTC

The v12 full build passed 2960 jobs. Its runner is
`/tmp/optimality-bench-integrated-v12`, SHA256
`e3a116256ffef648ac0404d04006e46b4335df01c2ce9dbad42e4d1eba8e3f0b`.
The public axiom audit passes through the new prefix, boundary, and gap
results. It reports only `propext`, `Classical.choice`, and `Quot.sound`.
The saved-suite check now uses this fixed executable.

The prefix count now contributes its full mandatory introduction premium
to `ValueAccounting`. It takes the maximum with the earlier singleton
reserve test, subtracts the first introduction when baseline already pays
for an initially absent value, and combines that premium with unconditional
transport in the same per-value budget.

`GapCost.tailValueBound_le_accounting` proves a second gap potential with
the leading term omitted for every value. `ValueAccounting` takes its
maximum with the first gap potential before summing. This prevents a lost
leading-distance credit from cancelling a new internal gap. Fourteen new
guards pass. For source `[0×15,a]`, target `[a,0×16,a]`, and additions
`{0,a}`, the old gap difference for a is zero, the new difference is one,
and zero transport contributes one more. Baseline two plus bound two equals
the production byte cost four.

`CorrectBoundary.mismatches_add_two_le` proves a further SWAP floor. If
growth must first fix a wrong boundary to value v, the current top is not v,
and every initial v copy is already in a correct position, then at least
two SWAPs are needed in addition to the count of initial wrong positions.
The first selection of a correct v slot makes it wrong; a later selection
must restore it. The proof counts these selections separately from the
initial wrong positions. `GroupEntry.requiredSwaps` takes the maximum with
this floor. Twelve guards and a focused axiom audit pass. A four-operation
trace attains the bound of three SWAPs on the small fixture.

The scheduler adds one chain-continuity policy and keeps the previous nine
candidates. The repeated-chain fixture now costs 45 gas, compared with 60
for the previous nine policies. Its bad second-birth prefix has nine wrong
positions; the new theorem proves a residual floor of eleven SWAPs, and a
production residual trace attains it. Temporary ranking trials show that
adding only this boundary floor to the existing estimate also gives 45 for
all three old policies on this fixture. Those trials are not runtime changes.

A reported v8-to-v11 cost change from 81 to 90 was a report-field error.
Both fixed executables give 81 on the same input, with identical retained
policy operation lists. The value 90 was the witness score. A report test
now covers witness ratios below one.

Collective seed capacity remains a research task. For source `[0×15]` and
target `(a,b)^k ++ [0×15]`, exact searches confirm k+1 direct introductions
for k equal to 2, 3, and 8. The current planner attains the optimum. At k=8
with 32-byte LOAD addresses and byte weights, baseline is 82, the current
static excess floor is 15, and optimum is 328. An interval packing bound
could force the remaining introduction premiums, but its trace reduction
and terminal-window argument are not proved.

The restricted interval proof plan now includes virtual deletion of the
last movable outputs. Its scope is source length q≤R, a fresh target prefix
followed by a permutation of the source, and additions exactly that prefix.
Every post-output bag has at most R values and must retain all q old copies.
Each retained consecutive-value interval uses one of the other R−q slots;
each interval without a retained seed needs a new direct introduction.
See `docs/optimality-inventory-research.md` for the weighted bound and the
remaining formal proof work. Exhaustive reduced-reach tests checked 1134
inputs and 23988 states without a counterexample.

The pinned v12 prefix suite passes all 18 production-cap fixtures. Each
scheduler cost equals baseline plus the proved static bound; the largest
saved prefix case has baseline66, excess1089, and cost1155. All30 saved
regressions pass, with no scheduler result above its stored witness cost.
The gap-only fixture has exact cost4. Nine collective-capacity fixtures
remain optimal by the exact oracle but are not fully covered by the current
static bound. The evidence is in `Bench/evidence-v12.json`.

### 2026-10-07 03:31 UTC

The user authorized regular commits. Commit `ed8894a` records the v12
scheduler, cost proofs, and their tests. The current `Shuffler` and all
non-red optimality test targets passed1498 jobs. Its staged imports were
closed, and the public axiom audit reported only the three standard axioms.
Commit `f1ae845` records frozen-prefix operation/cost equivalence, baseline
monotonicity, and lower-bound/factor-two transfer lemmas. Eight audited
frozen-prefix results use only the standard axioms. Neither commit changes
`Stack.lean` or `Trace.lean`. The pending frozen-bound integration test stays
outside these commits until its runtime definition is changed and checked.

The frozen-prefix reduction is proved for every no-POP production trace.
It preserves operation lists, additions, and all gas/byte pairs. An exact
full/reduced equivalence also requires matching frozen prefixes. Removing
source values can increase the generation baseline; the transfer API first
transfers the total score bound and then subtracts the original baseline.
The saved frozen-gap runtime fix remains pending while the v12 evidence run
continues on its pinned executable.

The collective proof now has two checked parts. Production-trace lemmas
split at birth heights and at the last prefix below a height limit. For the
disjoint fresh-prefix/old-suffix family, each real or virtual residual has
at most16 entries and retains every old copy. A separate finite-interval
theorem turns a feasible selected set and explicit per-value direct-count
inequalities into a weighted introduction floor. The selected-set transfer
between these parts is not proved yet. The finite maximum is a specification
and is not a production optimizer.

The next proof work uses a global mandatory-copy profile and one retention
plan. It does not add heuristic scheduler modes. The source-count profile,
plan realization, and its SWAP-cost bound remain proof obligations.
Transport and old-position repair can share a SWAP, so their charges need
one stated combination argument. The restricted interval floor alone does
not establish the general factor-two excess guarantee. That guarantee
remains open.

### 2026-10-07 03:49 UTC

Commit `a1c8493` records the residual-window and finite weighted interval
lemmas. The next checked group extends the mandatory inventory to repeated
source values. It proves nested height cuts, residual persistence, and the
need for a later PUSH or LOAD after a residual loses a value. Each production
trace now gives one retained paid-interval set whose crossings, plus the
mandatory inventory, fit16 slots at every positive cut. Every omitted paid
interval forces a strict direct-count increase between its output cuts.

The per-value sum of those increases is not yet proved. Plan realization,
SWAP cost, and the global factor-two excess theorem remain open. The tests
use production traces and include the height17/fresh-first-output obstruction.
The v12 benchmark evidence run is still in progress on its pinned executable.

### 2026-10-07 03:56 UTC

Commit `0b1f68a` records the global retained-set capacity and strict direct
count increases. The next group completes the introduction-cost lower bound.
Each omitted paid interval gets a distinct direct-count level. Values absent
from the source exclude the first level because baseline pays for it.
This proves the omitted interval weight is bounded by generation surcharge.
The score theorem adds the paid-weight floor to baseline and actual SWAP
cost. Its finite maximum is a specification, not a production optimizer.

The deadline-count proof gives an exact equality between new jobs due, old
inventory, and crossing paid intervals. Its signed deadline bound preserves
the source-height-17 obstruction. Tests cover repeated old values, capacity
released by an old output, paid source-present reuse, empty states, and
negative capacity cases. Plan realization and the global factor-two excess
theorem remain open.

The pinned v12 saved-suite run has finished: 590 cases, no errors or witness
violations, 589 factor-two certificates, and 410 exact certificates. Compared
with v8, 24 costs decrease and none increase. The frozen-prefix runtime bound
integration is being checked separately before a new full build.

The full `lake build Shuffler Tests optimality_bench` checkpoint passes
3005 jobs, including the repaired frozen-bound test. Fourteen audited
inventory-cost and deadline results use only the three standard axioms.
