# A family with surplus ratio close to two

Let `k ≥ 2`. Use distinct spilled variables `v₀, …, vₖ`, an empty source,
and this ordered birth word:

```text
v₀, v₁, v₁, v₂, v₂, …, vₖ₋₁, vₖ₋₁, vₖ
```

The word has `2k` entries. Swap these disjoint position pairs to get the target:

```text
(0,2), (1,4), (3,6), …, (2k−5,2k−2), (2k−3,2k−1)
```

For `k = 2`, this is `abbc → bcab`. For `k = 3`, it is
`abbccd → bcadbc`.

## Why the comparison needs exactly k SWAPs

No position has the same value in the word and target. Thus every occurrence
assignment moves every one of the `2k` positions. This remains true when equal
copies can exchange their target assignments. The production trace endpoint
bound says that one SWAP can account for at most two moved positions. Every
same-word no-POP trace therefore needs at least `k` SWAPs.

A comparison trace attains this bound. LOAD `v₀`. For each `vᵢ`, where
`1 ≤ i < k`, LOAD it and use DUP1. Then use SWAP2 for `i = 1`, or SWAP3 for
later `i`. Finally, LOAD `vₖ` and use SWAP2. It has exactly `k` SWAPs and uses
depth at most three.

## Why the endpoint optimizer uses more SWAPs

There are no positions that can stay fixed. The current endpoint matcher pairs
the remaining equal-value occurrences in order. Its assignment is one cycle:

```text
0 → 2 → 4 → … → 2k−2 → 2k−1 → 2k−3 → … → 1 → 0
```

The realizer uses `2k−1` SWAPs for that assignment. It uses SWAP1 after the
second birth. After each later odd birth position, it uses SWAP2 then SWAP1.
The second copy of `v₁` uses DUP2. The other second copies use DUP3.

Both assignments have the minimum possible moved-position count `E = 2k`.
The different SWAP counts come from their cycle structure. No tie rule is added
by this experiment.

Normalizing each SWAP run does not remove this cost. Each run has one or two
SWAPs on distinct values and already uses the minimum count for its own endpoints.
The `improveTraceWord` wrapper also keeps the same count when it receives the
canonical trace as its input. If it receives the comparison trace, it keeps
that cheaper trace instead.

## Cost and ratio

The checks use the production EVM cost model with PUSH1 spill addresses:
each first LOAD costs six gas and three bytes, and each DUP costs three gas
and one byte. Both traces use one LOAD for each of `k+1` kinds and `k−1` DUPs.
Their generation cost equals the lower bound:

```text
gas baseline   B = 9k + 3
byte baseline  B = 4k + 2
```

The SWAP surplus ratio for either objective is

```text
(2k−1) / k = 2 − 1/k.
```

This is a claim about surplus after subtraction of the generation baseline.
For these costs, the total gas ratio tends to `5/4`, and the total byte ratio
tends to `6/5`.

| k | Optimizer SWAPs | Minimum SWAPs | Surplus ratio |
|---|---:|---:|---:|
| 2 | 3 | 2 | 1.5 |
| 3 | 5 | 3 | 1.666… |
| 8 | 15 | 8 | 1.875 |
| 16 | 31 | 16 | 1.9375 |
| 32 | 63 | 32 | 1.96875 |
| 64 | 127 | 64 | 1.984375 |

## Proof and test status

`FixedWord/Sharpness/Theorems.lean` proves for every `k ≥ 2` that:

- the word and target disagree at every position;
- every compatible assignment moves all `2k` positions;
- every same-word no-POP trace requires at least `k` SWAPs;
- the corresponding gas and byte lower bounds apply to every such trace.

`Tests/OptimalityFixedWordSharpness.lean` has kernel proofs that the `k = 8`
comparison trace has the specified target and birth word and attains the
SWAP, gas, and byte lower bounds.

Execution checks call the production `replay`, `optimizeTraceWord`, realizer,
`SwapRuns.normalize`, and `improveTraceWord`. They pass for `k = 2, …, 16, 32, 64`
under both gas and byte objectives. The checks compare the complete optimizer
instruction list with the proposed pattern, then replay that list.

The all-`k` formulas for the optimizer output and the comparison trace remain
paper arguments. The asymptotic sharpness statement is not yet a Lean theorem.
The checked finite examples and the general lower bounds are separate results.
