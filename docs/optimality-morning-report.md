# Proof and implementation report: 7 October 2026

The public Lean API now includes the birth realizer, the final portfolio pass,
and finite dual cost certificates. The global polynomial factor-two optimizer
is still open. The current approximation theorems fix a birth word or an input
token assignment, unless a separate finite certificate covers all traces.

## Success and trace correctness

- For the original BBU, `buildBottomUp_succeeds_iff_static` proves success
  exactly when `StaticSuccess` holds, under `State.Valid`. The condition uses
  fixed initial data and has no stack-length limit.
- `buildBottomUp_correct_iff_static` also requires mapped values to equal the
  target values. Without that premise, success gives `expectedStack`.
- The complete constructor and portfolio have success exactly when `Reserve`
  holds. This is a different theorem from the original BBU result.
- The new constructors return the production `Trace`, with fixed spills,
  exact additions, and no POP.

See [BBU theorems](../Shuffler/BuildBottomUp/Theorems.lean),
[complete BBU wrapper](../Shuffler/BuildBottomUp/Complete.lean), and
[portfolio theorems](../Shuffler/Optimality/Schedule/Theorems.lean).

## Cost theorems and their comparison sets

Let `C` be the weighted gas/byte score of the result and `B` the generation
baseline. The surplus guarantee is `C-B ≤ 2*(score(other)-B)`.

| API or theorem | Comparison set |
|---|---|
| `optimizeTraceWord`, `improveTraceWord` | All no-POP traces with the same empty source, target, and ordered birth values. Equal-copy assignments and birth methods can differ. |
| `optimizeTraceAssignment` | All no-POP traces with the same source, target, and extracted input token assignment. Birth methods can differ. |
| `postPass_empty_surplus_le_twice` | The same-word set above. |
| `postPass_source_surplus_le_twice` | The input-assignment set above. |
| `Certificate.surplus_le_twice` | All same-target empty-source no-POP traces, when the finite certificate test passes. |
| `Certificate.source_surplus_le_twice` | All same-source, same-target no-POP traces, when the source certificate and required quotas pass. |

The source realizer has no source-size cap. It proves that each moved source
token is in the initial SWAP window. The frozen boundary is
`index + 17 < source.length`; at height 18, position 1 permits SWAP16.
Its SWAP count is `K(f) + 2*c(P)`, where `K` is the arbitrary-swap distance
and `c(P)` counts prefix cycles that do not contain the source top. The proof
bounds this count by twice the SWAP count of a trace with assignment `f`.

The output has the prescribed values and births. No theorem states that
extracting its token assignment again returns the supplied assignment.
See [source proof](source-prefix-potential.md),
[source method choice](../Shuffler/Optimality/BirthPlacement/SourceCheapest/Theorems.lean),
and [post-pass guarantees](../Shuffler/Optimality/Schedule/PostPass/Guarantees.lean).

## Current builder behavior

The portfolio selects its completed growing trace, then runs one final birth
pass. Empty sources use the word optimizer. Nonempty sources use the input
assignment and choose the cheapest available method at each absolute height.
The cost comparison keeps the incumbent when the candidate costs more.
`postPass_le` proves no increase in the selected weighted score. It does not
assert a componentwise decrease in both gas and bytes for every weight pair.
The exact no-growth dispatch is unchanged.

The checked original-BBU candidate, SWAP-run normalization, Reserve checks,
and final production replay remain in the builder. Historical regression
checks retain the pre-pass values and test the new result separately.

## Finite certificates and the next algorithm target

A checked dual certificate gives `L ≤ 2*score(other)` for every eligible
comparison trace. For denominator one, it is enough to construct a feasible
candidate and certificate with

```
C + B ≤ L.
```

This proves factor-two surplus without minimizing a joint plan objective.
The stronger test `2*C ≤ L` proves exact weighted optimality. For denominator
`Q`, multiply the left sides by `Q` and use the stored lower-bound numerator.

The empty-source byte example `[Var42, PUSH0×16, Var42]` has a proved global
optimum of 52 bytes, certified by `L=104`. The saved periodic example has
`C=591`, `B=575`, and `L=1166`; its all-trace surplus bound is proved in Lean.
The saved source example has `C=81`, `B=66`, and `L=147`; its all-trace surplus
bound is also proved. The saved offline optimum for that source case is 78,
so the certificate does not prove its 81-cost candidate optimal.

`sourcePlan_hard_quota` proves the required source quota: if a value cannot
be introduced directly, the source count is no larger than the target count
through position `p`, and a later copy is required, then more than that count
must be born before position `p+17`. The source certificate uses this theorem
with the generation baseline. General optional source generation rewards are
still an offline model.

See [dual certificate details](joint-dual-certificate.md),
[source quota proof](../Shuffler/Optimality/BirthPlacement/Dual/SourceQuota.lean),
[source certificate test](../Tests/OptimalitySourceDual.lean), and
[conditional global plan theorem](joint-optimizer-certificate.md).

## Implementation cost and measured cost

With indexed data, a supplied word needs `O(n log n)` time and `O(n)` live
space for endpoint selection and trace emission. There are at most `2n`
slack events and `n` candidate intervals; range-minimum/range-add queries
take `O(log n)` each. Remaining ordered matching and fixed-reach emission
take `O(n)`. Input trace extraction also counts the seed operation length.

The complete portfolio has an `O(n²)` time, `O(n)` live-space implementation
design at fixed EVM reach. It retains the augmented-root graph order, uses
indexed local updates, and streams candidate storage. The new final pass
fits this bound. These are data-structure arguments, not runtime theorems
for the current Lean list code. No C++ implementation is supplied here.
See [endpoint design](birth-endpoint-hall.md) and
[portfolio design](optimality-scheduler-implementation.md).

The final production helper was run on 700 saved actual portfolio traces.
All 700 outputs passed independent JavaScript replay. Two costs decreased:
`107 gas / 36 bytes → 101 gas / 34 bytes`, and
`95 gas / 65 bytes → 94 gas / 65 bytes`. None increased. The comparison
rejected 42 more costly raw source candidates. Total wall time was 5.08 s;
median case time was 1.48 ms and the maximum was 240.5 ms. These times include
replay, checks, reporting, and serialization. The portfolio and broad oracle
studies were not rerun. The saved v15 executable hash is unchanged.
See [measurement scope and evidence](birth-postpass.md).

The fixed-word examples reach surplus ratio `127/64` at `k=64`. Lean proves
the general lower bound and the exact `k=8` witness. The all-`k` output formula
and asymptotic sharpness argument are not yet Lean theorems.
See [sharpness scope](fixed-word-sharpness.md).

## Research after the production freeze

For an empty source with legal direct introduction of every value, the
minimum generation score is `D-M_R`: `D` is the all-direct score and `M_R`
is maximum-weight gap-interval packing at capacity `R`. The paper proof
handles the final boundary and constructs births in deadline order. A
min-cost-flow implementation takes `O(R*n*log n)` arithmetic operations,
or `O(n log n)` at reach 16. This result excludes SWAP cost and is not a
Lean theorem. See [exact generation](empty-source-generation.md).

With fixed gap prices, a sparse flow graph solves the priced assignment
problem and supplies row/column dual potentials. Seven small named cases
were compared with exact permutation enumeration. Replacing the row/column
data for the two saved witnesses preserves lower bounds 1166 and 147.
The ordinary implementation design takes `O(n² log n)`, above the strict
`O(n²)` ceiling. The cited faster flow theorem retains a cost-bit factor;
the outer price algorithm and its price-size bound remain open. See
[the fixed-price oracle](priced-assignment-oracle.md).

A paper proof gives one local recombination with
`W(P')+W(Q')≤E(P)+E(Q)` for the empty-source realizer. Extra quota and
generation conditions, together with `J(X)=L`, give `C+B≤L`. The proof does
not justify repeated use of the same cycle credit or prove that a required
recombination always exists. The permutation check covers 11,816 local
recombinations. See [local rounding](local-cycle-rounding.md).

The source objective `H=E+2c-r` satisfies `F≤H≤2S` on paper. It counts full
cycles only where source entry affects the cost. At reach 16, at most eight
marked source paths carry the needed connections through future rows.
For at most one marked open path, fixing the source partial map reduces
the remaining objective to ordinary matching. The general connection
problem remains open.

Two separate kernel theorems limit simpler source bounds. No signed rational
edge matrix can give universal pointwise bounds `F≤W≤2S` for this canonical
realizer: six feasible assignments force `13≤12`. No function of only the
moved count and all old rows can do so either: two assignments force `9≤8`.
These statements do not rule out a global factor-two optimizer or a different
realizer. See [the source assignment assessment](source-assignment-surrogate.md).

## Validation and remaining work

`lake build Shuffler Tests optimality_bench` passed with 3261 build jobs on
7 October 2026. This includes the source certificate, BBU proofs, portfolio
tests, and the benchmark executable. The final log is
`/tmp/FinalBirthBuild2.log`. The final public-theorem axiom audit is in
`/tmp/FinalBirthAudit.log`; the source quota audit is in
`/tmp/SourceQuotaAudit.log`. A source scan found no `sorry`, `admit`, new axiom,
unsafe code, `noncomputable`, or `Classical.choose` in the birth-placement
modules, final pass, and new source/sharpness tests. No classical runtime choice is
part of these additions. Audited theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

The remaining global task is to choose birth values and assignments in
polynomial time with a factor-two surplus guarantee for every feasible input.
A general method that produces a candidate and dual certificate with
`C+B≤L` would suffice. The current source dual may be too weak: endpoint
movement omits some initial-cycle SWAP costs. No LP integrality or general
rounding theorem closes this gap.

`lake build Tests.OptimalitySourceEdgeObstruction` passed with 1590 jobs;
both obstruction axiom audits list only the same three standard axioms.
The source and local-rounding notes received independent read-only review.
The exact-generation proof received a separate review of its interval bound,
final-boundary injection, and deadline schedule.

Against the starting commit `4b8dfa7`, `Stack.lean`, `Trace.lean`, the original
BBU implementation, and the mapping builder are unchanged. The Placement
constructor body is unchanged; its only edit is a complexity comment.
All completed work is committed locally. No changes have been pushed.
