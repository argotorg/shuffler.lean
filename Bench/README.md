# Optimality benchmarks

The production planners remain in Lean. The Node program is an offline exact
oracle and benchmark driver; it is not part of a production planner.

Use Node 20 or later and the repository's Lean toolchain. Build the planner
modules first, then run:

```sh
node --test scripts/optimality-oracle.test.mjs
node scripts/optimality-bench.mjs --suite smoke --state-limit 50000 \
  --output /tmp/optimality-smoke.jsonl --summary /tmp/optimality-smoke-summary.json
node scripts/optimality-bench.mjs --suite small --seed 20261007 --cases 500 \
  --output /tmp/optimality-small.jsonl
node scripts/optimality-bench.mjs --input Bench/optimality-regressions.jsonl
```

For a run that remains fixed while other agents build, first build the native
runner with `lake build optimality_bench`, then pass
`--runner .lake/build/bin/optimality_bench`. The driver copies that executable
to a task-specific temporary directory and records its SHA-256 hash. The
snapshot path stays in the summary so the same executable can be used again.

`--suite boundary` covers initial heights 15, 16, 17, and 18, gaps around reach
boundaries, and literal widths 1, 2, and 32. `--suite random` makes feasible
inputs from legal no-POP walks. `--suite medium` uses target lengths 5 through
8 and three distinct values. `--suite sparse` uses initial heights 16 through
20, at most two nonzero source values, and up to three births. `--seed` fixes
sampling. `--suite two-seed` tests two carried literal values across gaps near
16 and 32, in both final orders, with literal widths 32/1 and 32/32.
All suites use gas and
byte weights `(1,0)`, `(0,1)`, `(1,1)`, `(4,1)`, `(5,1)`, and `(6,1)`. Spilled
inputs also use address widths 1, 2, and 32. Sampling can select a subset of
these combinations; the full generated cases can be saved with `--emit-cases`.

`--suite two-seed-placement` also swaps the two initial values in the target
prefix and includes hard unspilled variables. `--suite loads` uses actual EVM
and C++ LOAD gas models with address widths 0, 1, and 32. `--suite no-growth`
uses heights through 128 and up to seventeen values in the working window.
`--suite mixed` uses sparse legal walks through height 20, literal widths
0/1/2/32, unspilled and spilled variables, return labels, and both gas models.
Use `--skip-oracle` for certificate coverage on those larger inputs. It
records `not-run` and still checks all production traces and any witness.

The driver calls `lake env lean --run Bench/Optimality.lean` once per suite.
Each oracle trace and each candidate trace passes the real `replayExact`
checker, including instruction bounds, source, target, and the exact multiset
of additions. The driver also checks that Lean and Node compute the same gas
and byte cost. Literal PUSH width is derived from its actual 256-bit value.
The default gas model is the C++ estimate; `gasModel: "evm"` instead prices a
PUSH0 LOAD address at five gas. Memory expansion and spill stores are excluded.

Cases use JSONL. Values are `l:<decimal literal>`, `v:<variable id>`, `return`,
or `wildcard`. Stack arrays run from bottom to top. Fields are `source`,
`target`, `spills`, `weights`, and optional `missing`, `loadWidths`, `mapping`,
and `referenceOps`. If `missing` is absent, it is the target count difference.
`mapping` supplies a value-compatible destination for every source occurrence.
Otherwise the old BBU uses the production `MappingBuilder.buildMapping` with
zero dropped counts and the `Leave` wildcard policy. The four historical BBU
failure fixtures deliberately supply their known occurrence assignments;
they do not claim that the mapping builder chooses those assignments.

The exact oracle searches value stacks with Dijkstra's algorithm. It allows
only required additions. A state therefore determines its remaining demand.
It removes equal-value swaps, keeps the cheapest available generator for each
value, and rejects a wrong frozen prefix. It does **not** use `Reserve` to
prune: `Reserve` is computed separately for comparison with Lean. A state limit
returns `limit`, never `infeasible` or `optimal`. Limited cases do not contribute
to optimum ratios. This search is intended for small offline problems only.

The standalone oracle also accepts `caps: {swap: d, dup: d}` for `1 ≤ d < 16`.
Those results are labelled `reduced-cap`. A production comparison uses the
actual ordinal limits 16 and 16, which give a seventeen-slot swap window.
The Lean bridge does not run production candidates for reduced-cap cases.

The generation lower bound `B` ignores reach limits. For a value demanded `k`
times, let `d` be DUP cost and `g` its cheapest permitted direct introduction.
If the value is initially present, its contribution is `k min(d,g)`. Otherwise
it is `g + (k-1) min(d,g)`. The report measures both total-cost and excess-cost
ratios. If the oracle attains `B` and a candidate exceeds it, the excess ratio
is `"inf"`; this is not hidden by an average. An unavailable introduction for
an absent value makes the baseline undefined and the problem infeasible.

Reports include case ids, seeds, limits, explored states, actual instruction
lists, and production source/artifact fingerprints before and after the run.
When another agent changes an artifact during a run, `stableArtifacts` is
false. With `runnerSnapshot`, the copied executable still stays fixed. Without
that snapshot, re-run before attributing the suite to one compiled revision.
Instruction counts measure output size, not planning complexity. The runner's
elapsed time includes checking and JSON serialization; it is not an optimized
C++ timing claim.

Candidate certificate flags are separate from oracle exactness. They report
equality with the proved baseline, equality with baseline plus lineage bound,
the no-growth optimality certificate, equality with the static bound, and
the sufficient factor-two lineage and static certificates. Certificate rejection does not show a cost or feasibility error.
Saved manifests `evidence-v4.json`, `evidence-v5.json`, and `evidence-v6.json` retain checkpoint
hashes and reproduction commands. To create another manifest, run:

```sh
node scripts/optimality-evidence.mjs v6 Bench/evidence-v6.json \
  /tmp/optimality-v6-*-summary.json
```

The regression file records discovered oracle optima and valid witness traces.
It does not assert that a particular candidate must retain its earlier cost.

`Shuffler/Optimality/Baseline/Theorems.lean` proves the generation baseline is
a lower bound for every eligible production trace. The Lean definition uses
a finite DUP fallback for values that have no direct introduction. Feasible
cases cannot require such an absent value. The benchmark checks the Lean and
Node bounds agree whenever the Node baseline is finite.

`scripts/optimality-bounds.mjs` checks further experimental graph, transport,
and lineage bounds. These are not proved certificates. Running it with
`--output /tmp/bounds.jsonl` saves every reduced-cap-2 input and oracle result.
It enumerates source lengths 0 through 3, target lengths through 4, the values
`0`, `v:42`, `v:43`, two spill sets, and four weight ratios. The `--reports`
mode checks saved actual-cap benchmark reports without searching again.

The v6 checkpoint includes 17 suites and 3,703 cases. It has no model or
feasibility disagreement. The exact oracle returns 2,681 optima, 12 infeasible
cases, 10 limited searches, and 1,000 intentional omissions. Of the oracle
optima, 2,560 match the portfolio cost. The largest measured excess ratio is
4/3. Every relaxed policy matches the corresponding v4 status, cost, and
operation list on all 1,970 shared inputs. These finite results do not prove
a general approximation bound.

`old-bbu` means original `BuildBottomUp.buildBottomUp`, including its final
`Permute` call. Its returned trace must replay to the exact target. A BBU
error remains an error with its reason. The metric does not report a
separate generation-only cost. A supplied occurrence mapping can change the
comparison: with source and target `[0,0]` and mapping `[1,0]`, BBU emits one
SWAP although the value-stack optimum is zero. The default mapping emits no
operation for this case.

`--suite planted --skip-oracle` constructs inputs from legal no-POP traces.
It includes sparse random walks and one- or two-value carry traces, with
source heights through 128, generation runs through 128, and at most eight
SWAPs. The witness and candidate pass production replay. The test checks
`candidateCost + B > 2 * witnessCost`; a true result disproves factor two
because the optimum is no greater than the witness cost. A false result is
only a test result. Use `--algorithms schedule,old-bbu` to select those two
planners and avoid computing the raw policies again. The default runs all
seventeen algorithms. The saved manifest records this selection.

The Lean transport scan takes linear time per value. Across all source
kinds, one initial-state bound can take quadratic time. Repeating it after
every birth can take cubic time. These measurements do not establish the
full planner's time bound; the C++ design needs shared prefix counts or
cancellation of the fixed prefix with occurrence lists for the live values.

The chain policies are `schedule-chains-balanced`, `schedule-chains-eager`,
and `schedule-chains-preserve`. The v9 schedule keeps the earlier candidates
and adds these three. V10 also checks a complete trace from original BBU with
the default production mapping and includes it in the minimum. A benchmark
case can still give `old-bbu` a different occurrence mapping.

The offline descent experiment enumerates SWAPs before and after exactly one
birth. It checks
`cost(prefix) + B(next) - B(now) + 2*D(next) <= 2*D(now)`.
At zero remaining births it uses exact permutation cost for the residual.
The default has one birth; `--births 2` tests whether a first birth can preserve
the proposed accounting. Each report states its bound version and domain:

```sh
node scripts/optimality-descent.mjs /tmp/descent.json --forced-introduction
node scripts/optimality-descent.mjs /tmp/descent-two.json \
  --combined-value-accounting --births 2 --case-limit 10000
node --test scripts/optimality-forced-introductions.test.mjs
node scripts/optimality-forced-introductions.mjs /tmp/prefix-count.json --prefix-run
```

These searches are research tools. A failed descent check can expose a gap in
the bound while the planner still returns an optimum. The saved descent
reports preserve that distinction and include actual-depth production checks
where available.

`forced-prefix-run.jsonl` contains eighteen cases with source `0^16` and target
`a^k ++ 0^16`, for six values of `k` through 33 and three LOAD widths. The v10
oracle results give exactly `k` LOADs and `k` SWAPs in every optimum trace it
returns. The schedule matches all eighteen optimum costs. The width32,
`k=33` fixture also stores original BBU's complete trace: 33 LOADs and 54 SWAPs,
versus 33 of each in the optimum. These measurements include final permutation.

Witness reporting version 2 measures the largest ratio only where the witness
has positive excess above `B`. It starts with `null`, keeps the actual case
and both scores, and can report a value below one. Witnesses with zero excess
have separate counts and violation fields. Exact-oracle approximation ratios
remain separate. Earlier manifests used a maximum initialized at one, so a
reported one did not imply equality with the witness. Those historical files
are preserved; `evidence-reporting-fix.json` records the reporting correction.

`collective-capacity.jsonl` has source `0^15` and target `(a,b)^k ++ 0^15`,
with both new values spilled, for `k=2,3,8` and LOAD widths 0, 2, and 32. The exact
oracle and v11 schedule agree on all nine costs. Those optimum traces use
`k+1` LOADs and `k-1` DUPs. A separate finite reachability check excludes all
traces with at most `k` LOADs for the three fixed width32 cases; its evidence
is in `evidence-collective-introductions.json`. These cases expose a cost
shared by the two new values that the current per-value bounds do not charge.
