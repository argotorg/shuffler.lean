# Exact models for the empty-source plan problem

This note concerns the remaining joint optimizer. It does not change BBU,
`Stack`, or `Trace`. The new checks are offline JavaScript checks. The
algebra below has not been added as a Lean theorem.

Use target indices `0,...,n-1` and a common DUP and SWAP reach `R >= 1`.
Every target value must have a legal direct introduction. Let `d_v` be
that introduction's score, and let `s` be the score of DUP or SWAP. Put
`p_v = max(d_v-s,0)`. A birth plan has generation score `G` and moved
endpoint count `E`. The objective is

```
J = 2*G + s*E.
```

This objective supports the conditional factor-two theorem described in
[joint-optimizer-certificate.md](joint-optimizer-certificate.md). It does
not equal the minimum trace score or count the exact number of SWAPs.

## A finite optimization specification

Let `x[b,j]` say that birth `b` supplies target endpoint `j`. These variables
are binary, every row and column sums to one, and `x[b,j]=0` if `b>j+R`.
For each consecutive equal-value gap `g=(p,t,v)`, let binary `y[g]` say
that the plan retains value `v` across this gap. Define

```
a_v(q) = number of target-v endpoints at indices <= q
C_v(k) = sum of x[b,j] with b <= k and target[j]=v.
```

Each retained gap adds the constraint

```
C_v(p+R) >= a_v(p) + y[g].
```

Prefix counts clamp at the ends of the target. The joint integer problem
minimizes

```
2 * sum_v d_v*a_v(n-1)
  - 2 * sum_g p_value(g)*y[g]
  + s * (n - sum_b x[b,b]).
```

A selected gap saves one direct premium. Values whose direct introduction
is cheaper than DUP have zero premium and can always use direct births.
This is a finite specification. It does not give an efficient optimizer.

## Eliminate the assignment after fixing its diagonal

Fix the retained gap set `Y` and a set `P` of endpoint identities to keep.
A pin `c in P` requires `x[c,c]=1`. Extra identities are permitted.
For each value define

```
F_v(k) = number of pins of value v at indices <= k
r_v(k) = number of generation jobs of value v due by k
u_v(k) = a_v(k-R) - F_v(k-R)
h_v(k) = max(0, max_{0<=q<=k}(r_v(q)-F_v(q)), u_v(k)).
```

The exact pinned quota condition is

```
sum_v h_v(k) <= min(k+1,n) - sum_v F_v(k)
```

at every cut from `0` through `n-1+R`. These cuts include all generation
and endpoint deadlines. One can construct a completion by putting free
jobs in deadline order into free birth slots and matching equal values.

There is an interval form with no running maximum. For every selected
gap `g=(p,t,v)`:

1. If some pin of value `v` lies in `(p,p+R]`, add no interval.
2. Otherwise let `u` be the next unpinned endpoint of value `v` after `p`.
   Add the interval `[p+R,u+R)`. Use an infinite end if `u` does not exist.

Let `delta_v(k)` be one when the union of these value-v intervals covers
`k`, and zero otherwise. Let

```
pinCount(k) = number of pins c with k-R < c <= k
width(k)    = number of target indices c with k-R < c <= k.
```

The exact condition is

```
for every k in {0,...,n-1+R},
  pinCount(k) + sum_v delta_v(k) <= width(k).
```

In the interior `width(k)=R`. The smaller widths at the two ends matter.
The sets and intervals depend only on the target, reach, retained gaps,
and pins. The condition has no stack execution or recursive state.

To obtain a second exact joint optimization specification, choose `Y`
and `P` subject to this condition and minimize

```
2 * sum_v d_v*a_v(n-1) - 2 * sum_{g in Y} p_value(g)
  + s * (n - |P|).
```

If a completion has extra identities, add them to `P`. Therefore the
minimum agrees with the assignment specification.

### Derivation of the interval form

Let `z_v(q)` indicate that a selected consecutive gap of value `v`
contains `q`, with its right end excluded. Consecutive gaps for one value
do not overlap. Moving a selected generation deadline from `t+R` to
`p+R` gives

```
r_v(k) = a_v(k-R) + z_v(k-R).
```

Thus `r_v(k)-F_v(k)` is `u_v(k)` plus `z_v(k-R)` minus the number of
value-v pins in `(k-R,k]`. Since `u_v` is nondecreasing,

```
h_v(k) = u_v(k) + delta_v(k),
delta_v(k) in {0,1}.
```

The extra unit occurs exactly when some earlier cut `q<=k` had a
selected gap at `q-R`, no pin of that value in `(q-R,q]`, and no
unpinned endpoint deadline between `q` and `k`.

Within a consecutive gap `(p,t)`, no endpoint of its value lies strictly
between its ends. If any cut of this gap has no pin in its forward
R-window, the first cut `p` has no such pin. The extra unit therefore
starts at `p+R` and lasts until the next unpinned endpoint deadline.
This gives exactly the intervals above. Finally, subtracting `sum u_v`
from the pinned quota inequality gives the window capacity inequality.

### Why a simpler colored overlap rule fails

Take target `a b b a b a`, `R=2`, retain gap `a0 -> a3`, and pin
`{0,2,3}`. There is no value-a pin in `(0,2]`. The extra a requirement
starts at cut 2 and ends at cut 7, the deadline of unpinned endpoint 5.
At cut 3 the two current pins are b2 and a3. The older a requirement is
still present. Three slots are required and only two exist.

The proposed rule `sum_v max(pinCoverage_v,retainedPresence_v)<=R`
would accept this case. It incorrectly lets a3 meet a requirement that
was already due before a3 was born. A pin and an older requirement of
the same value can both consume capacity.

## An exact frontier DAG

Before birth `b`, let `I_b` contain the endpoints assigned to earlier
births. The lag constraint implies that every index below
`max(b-R,0)` belongs to `I_b`. Define

```
S_b = I_b minus {0,...,max(b-R,0)-1}.
```

Then `|S_b|=min(b,R)`. A DAG state is `(b,S_b)`. A transition selects an
unassigned endpoint `j>=max(b-R,0)`. If `b>=R`, index `b-R` must be in
`S_b union {j}`. Remove that index to obtain the next frontier. Before
`b=R`, only insert `j`.

A DUP of `target[j]` is available exactly when that value occurs in
`S_b`. Indeed, the prior birth count minus the mandatory frozen-prefix
count is the number of entries of that value in `S_b`. Choose the
cheapest available generation method and charge

```
2 * generationPrice + s * [j != b].
```

Each full path gives one lag-valid assignment and legal birth choices.
Each such assignment gives a path. Its edge sum is `J`. Shortest path
therefore solves the plan problem exactly. This uses endpoint sets,
not a physical stack, but it still enumerates states.

The number of states is at most

```
sum_{b=0}^n binomial(n-max(b-R,0), min(b,R)).
```

If `R<=n`, the layers `b>=R` sum to `binomial(n+1,R+1)`. Earlier layers
add `sum_{b<R} binomial(n,b)`. At layer `b>=R`, put `q=n-b`. The number
of edges is

```
(R+1) * binomial(q+R-1,R).
```

There are `binomial(q+R-1,R-1)` states that contain the due endpoint;
each has `q` choices. Every other state has one forced choice. This
proves the edge formula. For fixed `R`, the state and edge totals have
degree `R+1` in `n`. If `R>=n`, the state count is `2^n`. This model is
not a production method at `R=16` and does not meet an `O(n^2)` target.

## Reverse buffer interpretation

Reverse both births and target order. The lag constraint becomes

```
reversed endpoint index <= reversed output index + R.
```

This gives a token buffer of capacity `R+1`. Fill it with the first
`min(n,R+1)` reversed input tokens, remove one token, read the next input
token if any, and drain the buffer at the end. At the reverse step for
forward birth `b`, the buffer before removal is `S_b union {j}`. After
removal it is `S_b`.

The direct premium is paid exactly when the removed token is the last
buffered copy of its value. Movement has zero cost exactly when `j=b`.
After the initial fill, this identity reward concerns the token at age
`R`; the initial fill needs its own boundary rule.

For each value, a presence episode starts when a token arrives to an
absent value and ends at a last-copy removal. Starting and ending with
an empty buffer gives equal counts of starts and ends, also with fixed
weights by value. This is a token-capacity model: multiple copies use
multiple slots. It is not a reduction to ordinary paging.

## Known limits and literature

The feasible pin sets are not a matroid, even with fixed retained gaps.
In the six-token case above, `{0,1,3}` and `{0,1,4,5}` are feasible.
Neither 4 nor 5 can be added to the smaller set. Thus its augmentation
axiom fails. Ordinary matroid greedy does not apply.

The separate evidence also contains a generic-cost fractional LP gap
and failures of the one-value valuated-matroid exchange law, both with
fixed generation and with direct premiums included. The generic gap
does not refute integrality for the specific moved-token objective.
No gap for that objective or its optional-retention version is known
from the checked cases. These finite checks do not prove integrality.

[Ranking with Fairness Constraints](https://arxiv.org/abs/1704.06840),
by Celis, Straszak, and Vishnoi, has disjoint groups and nested prefix
quotas of the relevant form. Its min-cost-flow and objective-specific
integrality results use monotone Monge weights. Our identity reward
fails the Monge inequality: rows 1,2 and columns 2,3 give
`[[0,0],[1,0]]`, with `0+0 < 0+1`. Lag also forbids some edges. Its
theorems do not establish a flow solution for this objective.

[Ranking and Rank Aggregation with Matroid Prefix Constraints](https://arxiv.org/abs/2607.07153)
uses Kendall tau distance. Moved-token count is a different objective;
the cited exchange result does not apply to it.

[The Sorting Buffer Problem is NP-hard](https://arxiv.org/abs/1009.4355)
and [A Constant Factor Approximation Algorithm for Reordering Buffer Management](https://arxiv.org/abs/1202.4504)
charge color changes or setup. Our cost charges last-copy removals and
individual token movement. The buffer transition systems are related,
but no cost-preserving reduction has been given. Their hardness and
approximation results do not transfer on the basis of that relation.

[Caching with Time Windows and Delays](https://arxiv.org/abs/2006.09665)
uses page-capacity and request-window costs. No reduction from the
token buffer and identity rewards to that model has been established.

One uncrossing fact still holds. For two equal-value assignment edges
that cross, if neither is diagonal, swapping their endpoints preserves
generation counts and the lag bounds, and cannot increase `E`. Thus
after retaining diagonal assignments, residual equal-value matching
can be sorted. This proves a fixed-diagonal construction; it does not
prove a joint rounding or augmentation theorem for choosing diagonals.

No reviewed result supplies a compact polynomial optimizer for this
objective. In particular, there is no proved `O(n^2)` method here. Such
a method still needs a global exchange, network, or rounding theorem
that handles the way pins suppress seed intervals and change their
right ends. It also needs a runtime proof and a certificate accepted
by the proved fixed-word and trace constructions.

## Small independent checks

- `scripts/optimality-frontier-dag.test.mjs`: five focused tests.
- `Bench/evidence-frontier-dag.json`: 14 named cases, 466 visited states,
  no difference from exhaustive endpoint-permutation optimization;
  each resulting plan is realized and replayed independently.
- `scripts/optimality-colored-pins.test.mjs`: seven focused tests,
  including failed capacity, absent free endpoint, duplicate selections,
  and both boundary windows.
- `Bench/evidence-colored-pins.json`: 296 retained plans and 41,324 pin
  choices from eight named targets at reaches 1,2,3,16. All per-value
  quotas, first failed cuts, and feasibility results match the separate
  pinned-quota implementation; 23,402 choices are feasible.

These checks support the implementations. They do not replace the
derivations above or supply a Lean theorem for the new models.
