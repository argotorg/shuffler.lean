# An exact condition for the empty-source trace certificate

This is a paper proof. It gives an exact finite comparison for a supplied
assignment and supplied prices. It does not give an algorithm that finds
them. It uses the empty-source plan model and the proved empty-source
realizer. It is not a new Lean theorem, a BBU success condition, or a
production change.

The repository's proved realizer uses reach 16. Its application below
takes `R=16`; statements at other values of `R` use the corresponding
abstract common-reach model.

## Definitions

Assume an empty source, common reach `R>=1`, and a legal direct
introduction for every target value. Target positions and birth rows are
`0,...,n-1`. Let `d_v` be the least direct score of value `v`, `u` the DUP
score, and `s` the SWAP score. All scores are nonnegative. Set

```
D = sum_j d_target[j].
```

For each consecutive equal-value target gap `g=(p,t,v)`, define

```
a_g = number of target-v occurrences at positions <=p
k_g = p+R
w_g = 2*max(d_v-u,0).
```

Let `f` be a permutation of target positions that meets `b<=f(b)+R`.
Its birth word at row `b` is `target[f(b)]`. Define

```
C_g(f) = number of v births at rows <=k_g
y_g(f) = 1 if C_g(f)>=a_g+1, and 0 otherwise
I(f) = number of fixed positions
E(f) = n-I(f)
c(f) = number of nontrivial permutation cycles
W(f) = E(f)-c(f).
```

Lag implies `C_g(f)>=a_g`: all target-v occurrences through `p` must
have birth rows at most `p+R`. Thus a missed gap has `C_g(f)=a_g`.
The birth-availability argument in
[the joint certificate note](joint-dual-certificate.md) says that `y_g=1`
is exactly when the next copy can use DUP. Use the least legal score at
each birth. Then the generation score, generation baseline, plan score,
and score of the proved realizer are

```
G(f) = D - (1/2)*sum_g w_g*y_g(f)
B    = D - (1/2)*sum_g w_g
J(f) = 2*G(f)+s*E(f)
S(f) = G(f)+s*W(f).
```

The formula for `B` charges the first copy directly and each later copy
at `min(d_v,u)`. The realizer score equality follows from
`BirthPlacement.realize_score`; its arbitrary-SWAP count is `W(f)`.

## Optional prices can be capped

For nonnegative gap prices, let

```
A(lambda) = max_f (s*I(f)+sum_g lambda_g*C_g(f))
U(lambda) = A(lambda)-sum_g a_g*lambda_g
              +sum_g max(w_g-lambda_g,0)
L(lambda) = 2*D+s*n-U(lambda).
```

The maximum ranges over lag-valid permutations. The sparse oracle in
[the priced assignment note](priced-assignment-oracle.md) supplies this
maximum and tight row/column potentials. These give a valid lower bound
`L` for every feasible plan objective `J`.

If `lambda_g>w_g`, reduce this coordinate by
`delta=lambda_g-w_g`. Every assignment has `C_g>=a_g`, so its oracle
reward drops by at least `a_g*delta`. Consequently `A` drops by at least
this amount. The term `-a_g*lambda_g` increases by `a_g*delta`, and the
cap term stays zero. Therefore `U` does not increase. Applying this to
each coordinate shows that prices can be restricted to

```
0<=lambda_g<=w_g.
```

This statement concerns optional canonical gaps. It does not cap a
multiplier for a required hard-value quota.

## The exact defect identity

Use capped prices and tight oracle row/column potentials. For any
lag-valid permutation `f`, define its assignment slack by

```
Delta_f = A(lambda)-(s*I(f)+sum_g lambda_g*C_g(f)) >= 0.
```

It is zero exactly when `f` maximizes the fixed-price assignment reward.
The exact identity is

```
J(f)-L = Delta_f
           + sum_{g: y_g(f)=0} (w_g-lambda_g)
           + sum_{g: y_g(f)=1} lambda_g*(C_g(f)-a_g-1).
```

To prove it, substitute the definition of `Delta_f` into `U`. Since
the prices are capped, the result is

```
U = s*I(f)+Delta_f
      +sum_g lambda_g*(C_g(f)-a_g-1)+sum_g w_g.
```

Subtract `L=2*D+s*n-U` from
`J=2*D-sum_g w_g*y_g+s*E`. At a missed gap, `C_g=a_g`, so its term is
`w_g-lambda_g`. At a retained gap its term is
`lambda_g*(C_g-a_g-1)`. This proves the identity.

There are three causes of a positive defect: assignment reward below the
oracle maximum; a missed gap with price below its cap; and priced copies
beyond the one spare copy that earns the gap reward.

Also,

```
G(f)-B = (1/2)*sum_{g: y_g(f)=0} w_g
J(f)-(S(f)+B) = G(f)-B+s*c(f).
```

Combining these identities gives the exact equivalence

```
S(f)+B <= L
  iff
Delta_f + sum_{g: y_g(f)=1} lambda_g*(C_g(f)-a_g-1)
  <= sum_{g: y_g(f)=0} (lambda_g-w_g/2)+s*c(f).
```

This is necessary and sufficient for this supplied realizer and dual
certificate to pass the finite surplus comparison. It is not necessary
for the trace itself to have a factor-two surplus bound: a different
certificate, or a proof without this certificate, can establish that
bound.

For an oracle-optimal integer assignment, the following sufficient
condition is direct:

- Each missed gap has `lambda_g>=w_g/2`.
- Each retained gap with positive price has `C_g=a_g+1`.

Here `Delta_f=0`, the left side is zero, and the right side is
nonnegative. The exact equivalence permits more general cases: distinct
permutation cycles and prices above half the reward can pay for the
left side. No method to reach or maintain either condition is proved.

## What an optimal fractional pair supplies

Let `X` be a convex combination of lag-valid assignments. Let `C_g(X)`
and `I(X)` be its mean prefix and fixed-position counts. The fractional
reward problem has variables `0<=y_g<=1` and constraints

```
y_g <= C_g(X)-a_g.
```

Its objective is to maximize `s*I(X)+sum_g w_g*y_g`. The least generation
score at `X` uses `y_g=min(1,C_g(X)-a_g)` whenever `w_g>0`.

Take optimal fractional primal and dual solutions, with the optional
dual prices capped as above. Put `mu_g=w_g-lambda_g`. Complementary
slackness gives

```
lambda_g*(C_g(X)-a_g-y_g) = 0
mu_g*(1-y_g) = 0.
```

Thus the price boundary cases are:

- If `lambda_g=0<w_g`, then `y_g=1` and `C_g(X)>=a_g+1`.
- If `0<lambda_g<w_g`, then `y_g=1` and `C_g(X)=a_g+1`.
- If `lambda_g=w_g>0`, then `C_g(X)=a_g+y_g<=a_g+1`.
- If `w_g=0`, then `lambda_g=mu_g=0`; no further count restriction is
  needed for the zero reward.

Suppose rounding gives integral lag-valid assignments whose gap counts
lie between the floor and ceiling of `C_g(X)`. Every retained gap with
positive price then has exactly one spare copy. Also, every missed gap
has price at its cap. In the zero-reward case that cap is zero. Therefore
the exact comparison for each rounded assignment reduces to

```
Delta_f <= G(f)-B+s*c(f).
```

The assignment slack need not be zero after rounding. The count facts
alone do not establish this last bound.

If the rounding also preserves each gap count in expectation, it
preserves the generation score in expectation. For positive-reward
gaps, the floor and ceiling lie in one linear segment of
`min(1,C-a_g)`, or at the endpoints of that segment. Hence
`E[G(f)]=G(X)`.

A separate sufficient global rounding statement would be

```
E[W(f)] <= E(X),
```

where `E(X)=n-I(X)` is the fractional moved-position count, and the
outer `E[...]` means expectation. With this statement,

```
E[S(f)]+B <= G(X)+s*E(X)+B
            <= 2*G(X)+s*E(X)
             = L.
```

The middle inequality uses `G(X)>=B`; the last equality uses primal/dual
optimality. At least one output then has `S(f)+B<=L`. This proof does
not require the rounded assignments to preserve fixed positions, or
to maximize the fixed-price assignment reward separately.

## The remaining construction problem

An exact fixed-price assignment oracle is available on paper. The
[local cycle note](local-cycle-rounding.md) proves one local permutation
bound. The following parts remain open here:

- A procedure to obtain a suitable optimal fractional primal/dual pair
  within the required total runtime, including exact price bit lengths.
- A global rounding construction that preserves the required prefix
  expectations and floor/ceiling bounds and proves the displayed mean
  bound on `W`.
- A proof that a sequence of local steps does not count the same cycle
  allowance more than once.

Another possible route is to construct integral oracle assignments and
prices that satisfy the exact defect comparison directly. It need not
minimize the fractional objective. A price update and assignment-change
rule with that guarantee has not been proved. These are empty-source
statements; a source can require extra initial SWAPs, so its realizer
needs a separate cost argument.
