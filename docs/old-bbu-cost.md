# Cost of the original BuildBottomUp

Let `n = initial.stack.length`, `k = initial.pending_generations`, and
`N = target.length = n + k`. Assume `initial.Valid` and a successful return.
The bounds below concern the operations added by this call. A caller can supply
an earlier trace; its operations and cost must be added separately.

`buildBottomUp` already calls `Permute.permute` when generation is complete.
The `old-bbu` benchmark therefore measures a completed trace, including that
final permutation. It reports a failed call as an error, not as a zero cost.

## SWAP bounds

The following bounds are proved in Lean:

- The final `Permute` emits at most 24 SWAPs. More generally, its count is at
  most `MAX_SWAP_DEPTH + MAX_SWAP_DEPTH / 2`.
- The full `buildBottomUp` call emits at most `2N + k + 24` new SWAPs.

The full bound is conservative. Each cursor advance emits at most two SWAPs.
A generation retry at the same cursor emits at most one SWAP and reduces the
pending count by one. There are at most `N` advances and at most `k` retries.
The final permutation adds at most 24 SWAPs.

The 24 bound is sharp. Use 17 distinct source values. Exchange eight pairs
among the lower 16 target positions and keep the top fixed. Each disjoint
2-cycle needs three top SWAPs. The production mapping has no repeated-value
choice in this example.

The full bound is not claimed sharp. A run with `n=17, k=1` can already emit
31 SWAPs. For example, source `[v0,...,v16]` and target
`[v1,...,v16,99,v0]`, where `99` is a new literal, does so with the default
mapping. The birth is one PUSH. This rules out a full-call bound of `2k+24`.

The theorem names are:

- `OldBBU.permute_swapCount_le_reach`
- `OldBBU.permute_swapCount_le_24`
- `OldBBU.buildBottomUp_swap_bound`

They are in `Shuffler/Optimality/OldBBU/PermuteBound.lean` and
`Shuffler/Optimality/OldBBU/LoopCounts.lean`.

## Birth counts and static cost

The theorem `OldBBU.buildBottomUp_suffix` gives the exact new trace suffix.
It proves that this suffix has no POP and has exactly `k` births:
`DUP + PUSH + LOAD = k`. Each separate birth count is at most `k`.
The suffix SWAP count is at most `2N + k + 24`.
The output trace is the supplied trace followed by this suffix. The supplied
trace can contain POPs; the theorem only excludes POPs from the new suffix.

Let `s` be the new SWAP count. Under `PrimitiveCosts.cppEstimate`, static gas
is at most `3s+6k` and encoded bytes are at most `s+34k`. These upper bounds
allow a LOAD with a 32-byte address. For a known trace, use its exact birth
kinds and immediate widths instead of these maxima. This gas model excludes
memory expansion and spill stores.

`OldBBU.noPop_cost_bound` proves the cost bound for any supplied upper bound
on birth prices. `OldBBU.cpp_noPop_cost_bound` gives the stated gas and byte
bounds. `OldBBU.buildBottomUp_cpp_cost_bound` adds the earlier trace cost and
substitutes the full-call SWAP bound. These theorems are in
`Shuffler/Optimality/OldBBU/CostBounds.lean`.

`Tests/OptimalityOldBBU.lean` runs the production mapping builder and BBU on
the zero-copy case, the eight lower transpositions, the 17-value rotation,
the wide-literal case, and a blocked case. It keeps errors as errors.

## Limits on approximation statements

There is no finite excess factor above the generation baseline for all
successful original-BBU calls with positive gas weight. This already fails
for the default production mapping on `[0] -> [0,0]`:

- BBU emits `DUP1`, with cost `(3 gas, 1 byte)`.
- `PUSH0` has cost `(2 gas, 1 byte)` and attains the generation baseline.

The optimum excess is zero and BBU's excess is the positive gas weight.
`Counterexamples.lean` proves the production result, the witness's optimality,
and the failure of every natural-number excess factor. These proofs use kernel
reduction of the production code; they do not use `native_decide` or `sorry`.

A separate tested byte-cost gap uses a PUSH32 literal `a`:

```
source = [a, 0 repeated 15 times]
target = source ++ [0,a]
```

The default-mapped BBU emits `DUP1; PUSH32 a`, which costs 34 bytes. The
baseline is 2 bytes. `DUP16; PUSH0; SWAP1` costs 3 bytes. The lineage lower
bound is one SWAP byte, so this witness is optimal. The excess ratio is 32.
This production outcome is measured; a dedicated kernel proof for this
larger example has not yet been added.

The carry family `[a] -> [b repeated k times,a]` does not show a gap. For a
hard value `a` and a nonzero free literal `b`, tested values of `k` from 1
through 64 use exactly `ceil(k/16)` SWAPs. BBU delays placement in this family.

With an arbitrary supplied occurrence mapping, even a total-cost factor can
fail: source and target `[0,0]` with mapping `[1,0]` cause a SWAP although the
empty trace reaches the target. The production mapping for this same source
and target is the identity and emits no operation. Claims about arbitrary
valid mappings must be kept separate from claims about the mapping builder.
