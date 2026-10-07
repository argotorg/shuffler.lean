# A finite certificate for a joint plan minimum

This certificate concerns an empty source and a common reach `R`.
It permits different prices for DUP and SWAP. Let their scores be `u`
and `s`. Let `d_v` be the cheapest legal direct introduction score of
value `v`. Every target value must permit a direct introduction.

Define

```
D = sum_v count_target(v) * d_v
C = 2*D + s*n.
```

For each consecutive target-v gap `g=(p,t,v)`, define

```
k_g = p+R
a_g = number of target-v occurrences at indices <= p
w_g = 2 * max(d_v-u,0).
```

There are `count_target(v)-1` gaps of each value. The first copy has no
gap reward and must pay its direct cost. If direct is cheaper than DUP,
the reward is zero. These facts include the absent-first-copy and
PUSH0 cases in the bound.

## Certificate inequalities

Supply signed rational row potentials `alpha_b`, column potentials
`beta_j`, and nonnegative rational multipliers `lambda_g` and `mu_g`.
Check

```
alpha_b + beta_j
  - sum_{g: value(g)=target[j] and b<=k_g} lambda_g
    >= s * [b=j]
```

for every legal endpoint edge `b<=j+R`, and

```
lambda_g + mu_g >= w_g
```

for every gap. Put

```
U = sum_b alpha_b + sum_j beta_j
      - sum_g a_g*lambda_g + sum_g mu_g
L = C-U.
```

Then `L` is a lower bound on `J=2*G+s*E` for every feasible plan. A
feasible plan with `J=L` is globally minimal. This conclusion does not
require LP integrality. A plan with a larger objective only receives a
lower bound from this certificate.

## Why the bound holds

Let `x[b,j]` be the endpoint assignment, and let `y_g` be a retained-gap
indicator. Each row and column of `x` sums to one. Each `y_g` lies in
`[0,1]`. With

```
C_v(k) = sum_{b<=k, target[j]=v} x[b,j],
```

the retained-gap constraint is `C_v(k_g)>=a_g+y_g`. Multiply each edge
inequality by `x[b,j]`, each gap inequality by `y_g`, and add. The result
is

```
s * sum_b x[b,b] + sum_g w_g*y_g
  <= sum alpha + sum beta
       + sum_g lambda_g*(y_g-C_v(k_g)) + sum_g mu_g*y_g
  <= U.
```

The left side is the identity and reuse reward. Subtracting it from
`C` gives the plan objective when each birth uses its cheapest legal
method, and a lower bound otherwise. Thus `J>=C-U`.

For the bridge to actual births, let `b_k` be the index of the kth birth
of value `v`, and let `t_(k-1)` be the preceding target occurrence.
The first birth cannot DUP. For `k>=2`, the available-copy count before
birth `b_k` is positive exactly when

```
b_k <= t_(k-1)+R.
```

The prior v-birth count is `k-1`. Subtract the v count in the frozen
target prefix, which consists of indices below `max(b_k-R,0)`.
The result is positive exactly when that prefix contains fewer than
`k-1` v occurrences. This is the displayed inequality. Equivalently,
the kth v birth is inside the prefix quota for its preceding target
gap. Each actual DUP with `d_v>u` can therefore receive one valid gap
reward. If `d_v<=u`, the direct cost is already a lower bound on either
birth method. This proves the generation lower bound used above.

## Exact integer check

Use one positive integer denominator `Q`. Store `Q*alpha`, `Q*beta`,
`Q*lambda`, and `Q*mu` as integers. The row and column entries can be
negative. The other entries must be nonnegative. Multiply each right
side by `Q`. The lower-bound numerator is

```
Q*C - sum A - sum B + sum_g a_g*Lambda_g - sum M.
```

An exact check compares that numerator with `Q*J`. No floating point
or solver output is trusted. The certificate has `O(n)` integers.
Value-specific suffix sums give all edge checks in `O(n^2)` integer
operations with `O(n)` temporary space. This is an arithmetic-operation
bound; it does not bound the bit length of arbitrary supplied numbers.

`scripts/optimality-joint-dual.mjs` checks the certificate and the supplied
candidate's endpoint permutation, lag bounds, birth methods, and exact
objective. It does not solve an LP or run in production. The script uses
seven focused tests and six hand-supplied examples, checked against an
independent exhaustive endpoint optimizer. The examples include unequal
DUP and SWAP prices and a case where reuse is too costly in movement.
Invalid dual signs, an invalid edge inequality, a missing DUP source,
an invalid endpoint permutation, and a zero denominator are rejected.

For example, take `a b a`, `R=1`, `d_a=d_b=34`, and `u=s=1`. The plan
with assignment `[0,2,1]` has methods direct, DUP, direct. Its generation
score is 69, `E=2`, and `J=140`. The certificate

```
alpha  = (2,1,0)
beta   = (1,0,1)
lambda = (2)
mu     = (64)
```

has `C=207`, `U=67`, and `L=140`, which meets the candidate objective.

`Dual.Certificate.reward_le` and `Dual.Certificate.lower_le` prove the
finite sum argument in Lean. `Dual.generation_discount` constructs the
needed cost bound for every actual `Plan`. It maps each DUP to a distinct
preceding target occurrence using an order-preserving equal-value copy
matching. The available-copy count proves that the mapped prefix quota
is met. Thus the first copy receives no reward, and no gap receives two
rewards.

`Dual.Certificate.globallyMinimal` now gives `Plan.GloballyMinimal` from
the finite validity checks and attainment alone. It has no remaining
universal-word or generation-discount premise. The Lean representation
uses one gap slot per target position, with zero reward at a value's last
position. This avoids a separate enumeration of nonempty gaps. Its
validity proposition states the mathematical sums directly; no kernel
reduction-time bound is claimed. The offline checker uses suffix sums
for its `O(n^2)` arithmetic-operation bound.

`Tests/OptimalityPlanDual.lean` checks the actual EVM byte model on
`[Var42, PUSH0 repeated 16 times, Var42]`. The certified plan swaps
endpoint identities 16 and 17, has `E=2`, and has `J=104`. The direct
birth word has `J=168`, while twice the generation baseline is 102.
The finite certificate feeds the existing all-word factor-two surplus
theorem. Another test uses different DUP and SWAP prices. The finite
core tests also reject invalid certificate fields and a failed reuse
quota, and check signed rational scaling.

The certificate also does not establish that every instance has an
integer candidate meeting its LP lower bound. That would require an
integrality or rounding theorem that is still missing.

## Certify a trace without minimizing the plan objective

Let `L` be the scaled lower-bound numerator above, with denominator `Q`.
`Dual.Certificate.trace_lower_le` proves

```
L <= 2*Q*score(other)
```

for every empty-source trace to the target without POP. Trace extraction
provides a feasible plan whose moved-token count is at most twice the
trace's SWAP count. No minimizing plan is needed for this bound.

For any valid candidate trace, write `S=score(candidate)` and let `B` be
the generation baseline. Two finite comparisons now suffice:

```
Q*(S+B) <= L  implies  S-B <= 2*(score(other)-B)
2*Q*S   <= L  implies  S <= score(other).
```

The Lean theorems are `Certificate.surplus_le_twice`,
`Certificate.score_le`, and `Certificate.weightedOptimal`. The last
also takes the candidate's eligibility proof. The surplus theorem uses
the already proved baseline bound for the comparison trace.

These tests do not require the candidate to attain the LP or plan
minimum. They give a separate algorithm target: find a feasible trace
and valid dual data that meet the required comparison. A general
algorithm with this guarantee and `O(n^2)` time is still not proved.

The EVM example above has actual trace score 52 and `L=104,Q=1`.
`Tests/OptimalityPlanDual.lean` proves that this trace is exactly optimal
against every empty-source trace to the same target without POP. It
also checks the direct surplus certificate, independently of the plan
minimum theorem.

The saved periodic case `a (x1 ... x15)^3 a`, at reach 16 with all LOAD
widths 32 and byte-only weights, is a second example. The saved production
trace costs 591 and its generation baseline is 575. One external
feasibility call supplied integer dual data with `L=1166,Q=1`. The exact
checker verified every coefficient. Thus `591+575=1166` certifies the
factor-two surplus bound. The trace's extracted plan has `J=1167`, so
attainment of the plan bound is not needed here. The certificate does
not pass the exact-score test, which would require `L>=1182`.

`Tests/OptimalityPeriodicDual.lean` replays the actual saved operations,
proves their 591-byte cost, checks the supplied integers with `decide`,
and proves the surplus bound for every same-target empty-source trace
without POP. Its finite validity check uses a larger local heartbeat
limit and took 42 seconds in the targeted build. The external call is
only a data supplier. No trust in that solver enters the Lean theorem.
Evidence and reproduction commands are in
`Bench/evidence-periodic-joint-dual.json`. This was one named case, with
no production scheduler rerun or new broad trace search.
