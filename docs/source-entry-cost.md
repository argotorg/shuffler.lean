# Source entry cost and a failed factor-two extension

The following source extension fails the factor-two bound on cost above
the generation baseline. It is an offline research proposal, not a
production mode.

The proposal was to treat `source ++ births` as a virtual empty-source
birth word, choose a deadline assignment with the minimum moved-token
count `E`, and run the proved empty-source token schedule. Replace the
virtual operations before the first real birth with an exact minimum
SWAP trace from the actual source to the virtual prefix result. Then
run the remaining births and scheduled SWAPs.

## Production-reach counterexample

Use three distinct unspilled variables `a`, `b`, and `c`:

```text
source = [a, b, c]
births = [b, c]
target = [b, c, c, a, b].
```

The endpoint matcher selects the assignment

```text
[3, 0, 2, 4, 1].
```

It has `E = 4`. Its virtual source prefix result is `[b, a, c]`, which
needs three top SWAPs from the actual source. The candidate trace is

```text
SWAP1; SWAP2; SWAP1; DUP3; DUP2; SWAP3; SWAP1.
```

It has five SWAPs. This comparison trace has only two:

```text
DUP2; SWAP3; DUP2; SWAP3.
```

Both traces use production reach sixteen, have no POP, and introduce
exactly `[b,c]`. `Tests/OptimalitySourceEntry.lean` constructs both with
the production replay. It also proves that every no-POP trace with these
endpoints and this word needs at least two SWAPs: every compatible token
assignment moves positions 0, 1, 3, and 4, while each SWAP can account for
at most two moved positions.

| Quantity | Candidate | Optimum | Baseline |
|---|---:|---:|---:|
| Gas | 21 | 12 | 6 |
| Bytes | 7 | 4 | 2 |
| Gas above baseline | 15 | 6 | |
| Bytes above baseline | 5 | 2 | |

Thus each cost above baseline has ratio `5/2`. The total cost in this
example remains within factor two. This example does not disprove a
factor-two total EVM cost bound.

A different assignment, `[3,4,2,0,1]`, also has the minimum `E = 4`. It
needs no source entry and realizes the two-SWAP trace. Thus the moved
count alone does not select a source assignment with the required cost
bound. This is evidence against that objective as a complete source
interface, not a request for another tie rule.

## The cycle accounting identity

For a fixed final token assignment, let `K` be its arbitrary-transposition
distance, namely the number of moved positions minus the number of
nontrivial cycles. Each physical SWAP either splits a cycle and decreases
`K` by one, or merges two cycles and increases `K` by one. Births expose
fresh token positions but do not change this full assignment permutation.
If `M` SWAPs merge cycles, then a trace ending at the identity satisfies

```text
SWAPs = K + 2 M.
```

The empty-source realizer uses only splits. Initial sources can force
merges because the current top belongs to a different cycle from the
cycle that must be repaired before a boundary becomes unreachable.
Source-only cycles do not describe every such case: an open cycle can
also need entry before its future top arrives. This is why a source
extension needs a proved entry term, not only `E`.

The source-cycle lower bound and a factor-two realization theorem for a
fixed assignment are now proved; see [the source proof](source-prefix-potential.md).
Choosing an assignment remains open. The objective `H=E+2c-r` is sufficient
on paper, but cannot be reduced to plain edge costs for this realizer; see
[the source assignment note](source-assignment-surrogate.md).

## Reproduction

`scripts/optimality-source-entry.mjs` compares the research construction
with exact minimum-SWAP search for a fixed source and word. Birth edges
cost zero and SWAP edges cost one. The search does not use target-prefix
pruning. It found the reduced-reach form of this failure after 369,281
endpoint cases. The production-reach case is pinned in its test file and
in the Lean test above.

The search report is `Bench/evidence-source-entry.json`. The general
fixed-word feasibility paper proof is separate, in
`docs/source-word-feasibility.md`; this failed approximation claim does
not affect it.
