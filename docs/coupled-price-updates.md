# A price update can need more than one gap

This note gives one exact obstruction and a local price-direction rule.
It concerns an empty source at reach one. It is a paper result with a
small exact check, not a Lean theorem, a reach-16 embedding, or a
production algorithm.

## A coordinate update can force a score increase

Take

```
target = [a,b,a,b]
R = 1
DUP score u = 1
SWAP score s = 1
direct scores d_a = 11, d_b = 6.
```

There are two gaps. Their quota bases are both one, their cuts are one
and two, and their doubled reuse rewards are `w_a=20,w_b=10`. The all-
direct score is `D=34` and the generation baseline is `B=19`.

The gaps cannot both be retained. Retaining a requires two a births
through row one. Retaining b requires two b births through row two.
Those requirements need four births in the first three rows.

The three relevant plans are:

| Assignment | Birth word | Gap retained | G | E | c | S=G+E-c |
|---|---|---|---:|---:|---:|---:|
| `[0,1,2,3]` | `a b a b` | none | 34 | 0 | 0 | 34 |
| `[0,2,1,3]` | `a a b b` | a | 24 | 2 | 1 | 25 |
| `[0,1,3,2]` | `a b b a` | b | 29 | 2 | 1 | 30 |

Each retained-gap class needs a nonidentity permutation, hence at least
two moved positions and at least one SWAP. The displayed plans attain
both bounds. The all-direct plan has the largest possible identity
count. Thus the fixed-price oracle reward for prices `x,y>=0` is exactly

```
A(x,y) = max(4+x+y, 2+2*x+y, 2+x+2*y).
```

This formula accounts for every legal assignment: the only possible
prefix-count pairs are `(1,1)`, `(2,1)`, and `(1,2)`. Within each pair,
the displayed plan has the least moved-position count.

At `x=y=2`, all three displayed plans are oracle-optimal. Choose the
a-retaining plan `f=[0,2,1,3]`. Its score is 25. The dual lower bound is

```
L = 2*D+4 - (A-x-y+(20-x)+(10-y)) = 42.
```

Its surplus certificate still fails: `S+B=44>42`.

Now raise only the price of the missed b-gap. For every `0<epsilon<=8`,
the prices `(x,y)=(2,2+epsilon)` obey the full optional caps. The third
oracle branch is strictly largest. Every oracle-optimal assignment
retains b, misses a, and has score at least 30. Thus there is no outgoing
oracle-optimal assignment whose score is at most the previous score 25.
Throughout this coordinate segment, the dual lower bound stays at 42.

In particular, the following proposed exchange rule is false:

> If a missed-gap price reaches an assignment breakpoint before the
> current trace is certified, one can continue that coordinate price
> increase through a score-nonincreasing oracle exchange.

This example does not disprove a global algorithm that uses joint price
changes, keeps a separate best trace, or permits temporary cost changes.

## A joint update succeeds on the same instance

Raise both prices together: `x=y=t`. For `2<=t<=4`, the two retained-gap
plans stay oracle-optimal, so the a-retaining plan can be kept. On this
segment,

```
A(t,t) = 2+3*t
L(t,t) = 40+t.
```

At `t=4`, `L=44=S(f)+B`. The original 25-score trace is now certified.
No assignment exchange or new cycle allowance is needed. Both prices
also lie below half their gap reward, although a half-price cap is not
proved to suffice in general.

The cheap price of the retained a-gap was the obstacle to the coordinate
update. Raising that price protects the current assignment against the
competing b-retaining assignment. Since the current plan has exactly one
spare a copy, this protecting price increase has zero direct effect on
the dual objective's slope.

## The exact local direction rule

Use the notation of
[the certificate identity](direct-certificate-invariant.md). Fix capped
prices `lambda`, and let `f` be an oracle-optimal assignment. Let `F` be
the finite set of assignments with the same oracle reward as `f`.
Choose a real direction `d` consistent with the price bounds: at a zero
price it cannot point below zero; at a capped price it cannot point
above the cap.

For an assignment `h`, write

```
sigma_h = reward_lambda(f)-reward_lambda(h) >= 0
r_h = sum_g d_g*(C_g(h)-C_g(f)).
```

At prices `lambda+tau*d`, the reward of `h` minus that of `f` is
`-sigma_h+tau*r_h`. Therefore `f` stays oracle-optimal for all sufficiently
small positive `tau` exactly when

```
sum_g d_g*(C_g(h)-C_g(f)) <= 0   for every h in F.
```

Necessity follows from any tight assignment with positive slope. For
sufficiency, each nontight assignment has `sigma_h>0`; finitely many
assignments give a positive common step before any of them can overtake
`f`. A step ends at a price bound or the next ratio
`sigma_h/r_h` with `r_h>0`.

While `f` stays optimal and the prices stay within their full caps,

```
L(lambda+tau*d)-L(lambda)
  = tau*sum_g d_g*(a_g+1-C_g(f)).
```

Thus a missed gap contributes `+d_g`, a retained gap with exactly one
spare copy contributes zero, and each further copy contributes `-d_g`.
This is a proved local criterion for a useful joint price move. It does
not say that such a move always exists, or that it can be found within
the required total runtime.

In the example, the active competition with the b-retaining assignment
requires `d_b<=d_a` to keep the a-retaining assignment. The active
identity assignment also requires `d_a>=0`. The direction `(1,1)` meets
both conditions and increases `L` at rate one. Direction `(0,1)` fails
the first condition.

## The next proof question

A direct method could keep the current oracle assignment and dual data,
the best trace found so far, and the actual current permutation cycles.
The best trace need not itself be oracle-optimal; its assignment slack
is already included in the exact certificate identity. This removes
the need to accept an increased candidate score merely because the
oracle changes assignment.

The unresolved step is to use the tight competing assignments to select
a joint price direction, or a legal exchange, that makes certificate
progress. A connected set of tight constraints may identify which
retained-gap prices must move with a missed-gap price. The local rule
above defines that requirement, but it does not give a combinatorial
construction or an iteration bound. Priced extra copies, price caps,
and exchanges that merge current cycles still require a global charge.

## Exact check

`scripts/optimality-price-coupling.mjs` enumerates all 24 permutations and
checks the eight lag-valid ones. It confirms the three prefix-count
classes and their least moved counts and realizer scores. It calls the
existing sparse fixed-price oracle at `(2,2)`, `(2,3)`, `(2,10)`, and
`(4,4)`, then passes its exact integer row/column potentials to the
existing joint certificate checker. The saved evidence includes all
certificate coefficients and comparisons:

```
Bench/evidence-price-coupling.json
```

Two focused tests cover the failed coordinate rule and the successful
joint update. The formula for every positive `epsilon` is the paper
argument above; the check does not approximate a continuum with samples.
