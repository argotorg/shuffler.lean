# Latest residual matching with the labelled realizer exceeds the source cost bound

This example refutes one proposed fixed-word selection rule:

1. Choose the maximum set of earliest feasible identity pins.
2. Process the other targets in increasing order. Choose the latest
   eligible equal-value row for each one.
3. Run the current labelled canonical source realizer.

The word "labelled" matters here. The existing value-based SWAP normalizer
reduces this example from nine SWAPs to seven. Thus this example does not
refute the same rule followed by that normalizer. The distinct-source
example in [source entry cost](source-entry-cost.md) survives normalization.

The residual matching is feasible. Its nested deadline sets let an earlier
row replace a later one at any remaining target. But feasibility and the
minimum moved count do not imply the required cost bound for this rule.

Use reach four:

```
source = [a,b,b,a,b]
births = [c,d]
target = [b,a,d,c,b,a,b]
```

All four values are distinct. Only position 4 has the right value before
permutation. Thus every minimum-moved assignment fixes that position and
moves the other six. There is no pin-set choice in this example.

The latest-residual rule chooses

```
f = [5,6,0,1,4,3,2].
```

Its full assignment has one six-cycle, so `K=5`. Its virtual source prefix
has cycles `(0 2)` and `(1 3)`, both below the initial top. Hence `c=2` and
the canonical realizer uses `F=K+2c=9` SWAPs.

This valid trace uses four:

```
SWAP4; SWAP3; PUSH c; SWAP2; PUSH d; SWAP4
```

Therefore the unnormalized selected plan fails the factor-two SWAP bound. Both birth
values are absent from the source and distinct, so their required direct
generation cost is the same in both traces. The factor-two surplus bound
fails as well.

This example has no moved value-correct old row. A rule that only promotes
such a row to a later equal-value source slot cannot change this assignment.
The two source paths must instead be connected to future rows differently.

The ordinary earliest-residual assignment is

```
[1,0,6,5,4,3,2],
```

which has the same minimum moved count and canonical cost 5. Thus the
example does not refute the existence of a suitable minimum-`E` assignment.

The same seven-position example also works at production reach sixteen.
Every repeated value occurs only in source rows, and all its candidate
edges were already legal at reach four. Thus the wider reach changes
neither residual assignment in this example.

An alternative production embedding maps each active index `i` to `4*i` and puts
distinct fixed filler values in the unused positions. This gives source
height 17 and final height 25. Filler rows have one possible target, and
the active lag edges are exactly those of the reduced example. The selected
assignment still costs 9 canonical SWAPs. Scale the four comparison SWAP
depths by four and insert the filler PUSH instructions between real births.
That trace still uses four SWAPs.

`scripts/optimality-source-normal-form.mjs` checks all three instances. It uses
the existing pin selector, applies the proposed residual rule, checks the
two canonical costs, and replays the comparison with the exact instruction
guards. This is a finite executable check, not a Lean theorem. No production
selection rule changes.

`Tests/OptimalitySourceNormalization.lean` checks the actual production
`SourceEntry.build`, `realizeSource`, and `SwapRuns.normalize` functions.
Its counts are:

| Example | Raw total | Labelled entry | Value entry | Normalized total | Comparison |
|---|---:|---:|---:|---:|---:|
| Latest residual, above | 9 | 6 | 4 | 7 | 4 |
| Lag pair-exchange example | 9 | 6 | 5 | 8 | 4 |
| Distinct-source entry example | 5 | 3 | 3 | 5 | 2 |

The first two examples lose their factor-two failure after value
normalization. The last one keeps it. Its entry requirement is a concrete
value permutation with minimum cost three. A constructor that insists on
that virtual prefix stack cannot attain the two-SWAP comparison merely by
improving each separate SWAP run. It must also change how source work and
real births are interleaved, or choose a different source assignment.
