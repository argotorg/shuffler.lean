# Final birth pass

The schedule portfolio selects its complete trace first. For a trace with
growth, it then runs one birth pass. The existing cost comparison retains the
incumbent if the candidate has a greater weighted score, or a worse secondary
cost at a score tie. The no-growth path still uses its exact permutation solver.

For an empty source, the pass uses `improveTraceWord`. It keeps the ordered
birth values, selects birth methods by cost, and chooses a minimum moved-token
assignment. For a nonempty source, it uses `optimizeTraceAssignment`. That
construction starts from the seed assignment and selects available birth
methods at their absolute stack heights.

The production result still has the exact source, target, additions, and no-POP
proofs. `postPass_births` proves that ordered birth values stay the same.
`postPass_le` proves that the selected weighted score cannot increase.
The complete builder still succeeds exactly when `Reserve` holds.

The two approximation results have different comparison sets:

- `postPass_empty_surplus_le_twice` compares all no-POP traces with the same
  source, target, and ordered birth values. Equal-copy assignments can differ.
- `postPass_source_surplus_le_twice` compares no-POP traces with the same seed
  assignment. Birth methods can differ.

Neither result optimizes the global birth order. No theorem says that
extracting the output trace's token assignment returns the seed assignment.

## Saved-trace measurement

`Bench/evidence-birth-postpass.json` records the first assessment. It calls the
actual production functions on saved portfolio outputs and independently
replays their instructions in JavaScript. It does not rerun the portfolio or
an optimality oracle.

The empty-source pass checked 97 traces in 142 ms wall time. Their costs did
not change. The source constructor with the original birth methods checked
603 traces in 5.11 s. One trace decreased from 107 gas and 36 bytes to 101 gas
and 34 bytes. Forty-two raw candidates cost more and are rejected by the final
incumbent comparison.

The integrated assessment in `Bench/evidence-birth-postpass-integrated.json`
also tests source-offset birth-method selection and the final production
`postPass` helper. Its records preserve the input, output, and executable
hashes. All 700 final outputs pass independent replay. The final helper takes
5.08 s wall time and decreases two costs, with no increases:

| Source / target size | Saved portfolio cost | Final cost |
|---|---|---|
| 16 / 32 | 107 gas, 36 bytes | 101 gas, 34 bytes |
| 256 / 272 | 95 gas, 65 bytes | 94 gas, 65 bytes |

The second decrease comes from source-offset birth-method selection. The
incumbent comparison rejects all 42 more costly raw source candidates. The
median measured case takes 1.48 ms, the 95th percentile takes 19.4 ms, and the
maximum takes 240.5 ms. Reported per-case times include replay, the post-pass, result checks,
cost and certificate reporting, and JSON serialization. They are not a
complexity bound or a measurement of only the core pass.

The pinned v15 executable and its earlier portfolio evidence stay available.
`scripts/optimality-birth-postpass.mjs` rebuilds the post-pass inputs from those
saved result files and reruns only the post-passes.
