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

The weak-duality argument is mathematical. At this checkpoint, no Lean
theorem connects this numerical checker to `Plan.GloballyMinimal`.
The certificate also does not establish that every instance has an
integer candidate meeting its LP lower bound. That would require an
integrality or rounding theorem that is still missing.
