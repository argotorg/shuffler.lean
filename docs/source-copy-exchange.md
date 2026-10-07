# A source pin can require more than one equal-copy exchange

This finite example rules out a proposed source repair lemma. It uses the
current canonical realizer cost `F=K+2c`. The starting assignment minimizes
the moved count `E`. No feasible exchange of two equal-value rows preserves
that minimum, but its canonical cost exceeds twice a comparison trace's
SWAP count.

The example does not rule out a factor-two assignment somewhere else among
the minimum-`E` assignments. Such an assignment exists in this example.
The checks below are executable regressions, not Lean theorems.

## A reduced example

Use reach four and zero-based positions:

```
source = [a,b,c,d,b]
births = [b,b]
target = [b,b,d,b,b,c,a]

f = [6,0,5,2,4,1,3]    E=6, K=5, c=2, F=9
g = [6,1,5,2,0,3,4]    E=6, K=4, c=1, F=6
```

Here `a,b,c,d` are distinct values. A comparison trace uses four SWAPs:

```
SWAP4; DUP4; SWAP2; SWAP3; DUP3; SWAP2
```

It has exactly the stated source, target, and ordered births. Thus `F(f)=9`
exceeds twice this trace's SWAP count.

Only positions 1 and 4 can be fixed: every other position has different
input and target values. Both cannot be fixed together. Target position 0
needs a `b`, and the two new `b` rows 5 and 6 cannot reach it. Thus one of
the old `b` rows 1 and 4 must move to position 0. Therefore `E≥6`, and
both `f` and `g` attain the minimum.

Only the four `b` rows can exchange endpoints. These are all six pairs:

| Exchanged rows | Feasible | New E |
|---|---|---:|
| 1,4 | yes | 7 |
| 1,5 | no: row 5 cannot reach target 0 | 5 |
| 1,6 | no: row 6 cannot reach target 0 | 6 |
| 4,5 | yes | 7 |
| 4,6 | yes | 7 |
| 5,6 | no: row 6 cannot reach target 1 | 6 |

The failed lag checks cannot supply the proposed factor-two lower bound:
the four-SWAP comparison remains valid. Moving from `f` to `g` transfers
the fixed position from row 4 to row 1 through one alternating cycle of
four equal-value rows. A sequence of pair exchanges must either leave the
minimum-`E` set or pass through an infeasible assignment.

The feasible exchanges above do decrease `F` from 9 to 8 while they raise
`E` to 7. Thus this example specifically refutes repair constrained to the
minimum-`E` set by individual pair exchanges. It does not refute a method
that changes `E`, a method based on alternating cycles, or another realizer.

## Production reach sixteen

Replace each old index `i` by `4*i`. Put a distinct new filler value at
each unused index, with identical input and target positions. The source
has length 17 and the final stack has length 25. Every filler has exactly
one possible target, so it stays fixed in every value-compatible assignment.
An active edge satisfies reach sixteen exactly when its reduced edge
satisfies reach four. The counts `E,K,c,F` are unchanged.

The comparison is:

```
SWAP16;
PUSH filler17; PUSH filler18; PUSH filler19;
DUP16; SWAP8; SWAP12;
PUSH filler21; PUSH filler22; PUSH filler23;
DUP12; SWAP8
```

It still uses four SWAPs, and every DUP and SWAP is within its production
limit. The script `scripts/optimality-source-exchange-obstruction.mjs`
replays both traces, checks both potentials, enumerates all 24 assignments
of the four equal rows, proves the minimum moved count by enumeration,
and checks every pair exchange. On both instances the minimum `F` among
minimum-`E` assignments is 6. No production constructor changes.
