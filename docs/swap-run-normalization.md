# SWAP-run normalization

`SwapRuns.normalize` replaces each consecutive run of SWAP operations with a
minimum-SWAP trace between the same two concrete stacks. A DUP, PUSH, LOAD, or
POP ends the current run. The pass uses `ValueGraph.build`, which accounts for
equal values. It skips empty runs.

The pass has a separate trace API. The portfolio applies it to each proposed
candidate before comparing costs, and to the complete fallback once. It does
not change the original BBU, `Stack`, or `Trace` definitions. It does not
search stack states.

## What Lean proves

The source and target remain the same by the result type. The theorem module
also proves these statements for every input trace:

- `normalize_noPop`: the result has no POP if and only if the input has no POP.
- `normalize_additions`: the multiset of added values stays the same.
- `normalize_withoutSwaps`: all non-SWAP instructions keep their arguments and
  execution order.
- `normalize_births`: the actual values introduced by DUP, PUSH, and LOAD keep
  their execution order.
- `normalize_cost_le`: gas and byte costs do not increase, for every
  `PrimitiveCosts` model.
- `normalize_score_le`: every permitted weighted cost does not increase.

`improve_min_swaps` proves that the replacement of one run has minimum SWAP
count for its endpoints. `normalize_noGrowth_min_swaps` gives the same result
when the whole input has no POP and adds no values.

`normalizeBuilt` preserves the full `BuiltTrace` type, including its exact
additions. This is the interface for callers that already have a built trace.

## Checked example

Let the source contain fifteen zero values. Let the target be:

```text
a, b, b, b, b, b, b, b, b, b, b, b, b, a, fifteen zeros
```

Both `a` and `b` are spilled values. With 32-byte LOAD addresses and the C++
cost model, the original BBU trace costs 150 gas and 146 bytes. Its last run
contains twenty SWAP operations. The pass replaces that run with one SWAP15.
The resulting trace costs 93 gas and 127 bytes.

`Tests/OptimalitySwapRuns.lean` checks this result against the actual original
BBU and the actual normalization pass. It also checks empty traces, equal
values, a necessary single SWAP, round trips, mixed operations, POP, and the
SWAP16 boundary on a stack with a fixed lower prefix.

This result does not prove a global factor-two bound for traces with growth.
It optimizes placement inside each existing run. It does not select new birth
orders or new retention plans. General idempotence is not proved here.

## Portfolio integration

`Schedule.build` now returns 127 bytes on the example above. The same result
holds for `buildWith []`, before any scheduler policy is tried. The changed
guard failed before integration and passed after it. Other guards retain the
raw-policy controls: all six raw rotation policies have 19 SWAPs, while their
normalized candidate portfolio has 17. The nine raw continuity policies have
60 gas each; the normalized earlier candidate set has 48 gas, and the full
portfolio still has 45 gas.

Lean proves the portfolio's weighted score is at most the normalized original
BBU score, the normalized complete-fallback score, and every normalized raw
strategy candidate in its selected list. The original cost bounds, baseline
attainment, and exact Reserve success condition remain proved. Each run
replacement decreases both gas and bytes. Selection between different
candidate traces uses the requested weighted score and existing tie rule.

The v14 benchmark provides two explicit reference hooks. Its 2,509 saved
production traces all pass replay, exact additions, non-SWAP order, actual
introduced-value order, componentwise cost, and finite two-pass checks.
931 traces shorten and 1,895 SWAPs are removed. These are tests of the pass.
V15 is the separate checkpoint that applies the pass inside `Schedule.build`.
General idempotence and a global factor-two result remain unproved.
