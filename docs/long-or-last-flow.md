# A joint flow model when every rewarded gap is long or last

This is a paper construction for an empty source and common reach `R>=1`.
Every target value must have a legal direct introduction. It solves the
joint generation and moved-endpoint objective in the stated regime. It
does not minimize actual SWAP count, change production code, or give a
general arbitrary-gap optimizer. The flow construction is not proved in
Lean. Its output can use the existing finite Lean certificate theorems.

Let `d_v` be the least direct score, `u` the DUP score, and `s` the SWAP
score. All are nonnegative. For each consecutive target-v gap `g=(p,t)`,
write

```
k_g = p+R
a_g = number of target-v copies through p
w_g = 2*max(d_v-u,0).
```

The required structural condition is:

> Every gap with `w_g>0` is long (`t-p>R`) or is the last gap of its value
> (`t` is that value's final target occurrence).

The condition permits three or more copies. It includes the regime where
each positive-premium value occurs at most twice. It also includes
arbitrarily many separated copies, followed by one short final gap.

## Separate linear and saturating rewards

For a lag-valid assignment `f`, let `C_g(f)` count births of the gap value
through its cut, and let `y_g=[C_g>=a_g+1]`. Lag gives `C_g>=a_g`.

Treat every last gap as linear. There are only `a_g+1` copies of its value
in total, so

```
y_g = C_g-a_g.
```

Let `H` be these last gaps. Define their birth-price function and constant

```
h_v(b) = sum_{g in H, value(g)=v, b<=k_g} w_g
C0 = sum_{g in H} a_g*w_g.
```

Every remaining positive-reward gap is long; call this set `T`. The total
identity and reuse reward is exactly

```
s*I(f) + sum_g w_g*y_g(f)
  = s*I(f) + sum_b h_target[f(b)](b)
      + sum_{g in T} w_g*y_g(f) - C0.
```

Zero-reward gaps impose no extra condition.

## The network

Use the sparse graph from [the priced assignment construction](priced-assignment-oracle.md).
Birth row `b` occurs at time `b`. Target `j` has deadline `j+R`. A global
time chain permits waiting forward. Each value chain visits its target
deadlines in increasing order. Each birth supplies one unit, and each
target demands one unit.

- Birth `b` has a direct identity arc to target `b`, with reward
  `s+h_target[b](b)`.
- A generic path enters the global chain at its birth time. At a target
  deadline `d`, it can enter that target value's chain, receiving reward
  `h_v(d)`. It can continue to a later target deadline of that value.
- On the value-chain segment from `p+R` to `t+R` for each gap in `T`, put
  two parallel arcs. The first has capacity one and reward `w_g`. The
  second has sufficient capacity and reward zero.
- All other internal arcs have reward zero.

The first-unit reward is an ordinary pair of linear-cost network arcs.
An optimal flow uses the reward arc whenever positive flow crosses that
segment. It therefore earns exactly `w_g*[flow_on_segment>0]`.

Internal capacities `R+2` suffice and remain strictly inactive in any
complete flow. At a positive-time cut, the number of open paths is the
number of births so far minus the number of target deadlines so far,
which is at most `R`. At a zero-time value entry, at most `R+1` paths can
arrive before the target exit. The reward arcs keep their explicit unit
capacities. There are `O(n)` vertices and arcs.

## Why a long gap has no bypassing identity

Fix a long gap `(p,t,v)` and its cut `k=p+R`. An identity path for the
same value has endpoints at times `j` and `j+R`, where `j` is a target-v
position. There is no such position strictly between `p` and `t`.

If `j<=p`, that identity path ends by the cut. If `j>=t`, it starts after
the cut because `t>p+R`. Thus no identity path of value `v` crosses this
cut. Every spare v birth at this cut must use a generic value-chain path.

This fact fails at a short gap: the identity of a later same-value target
can cross the gap cut without using the value chain. The last-gap linear
formula handles that case separately. A positive gap that is both short
and nonlast is the excluded interaction.

## Equality of optimal rewards

Given an assignment, route each fixed row through its identity arc.
For every other edge `b -> j`, enter its value chain at the first target
deadline at or after `b`, then continue to target `j`.

The linear birth price is unchanged by this wait. All its price changes
occur just after a deadline of the same value, and no such deadline lies
between `b` and the first eligible deadline.

At the cut of a gap in `T`, canonical generic flow equals `C_g-a_g`.
All due target copies have exited. No identity bypasses the cut, by the
previous argument. The first-unit arc therefore gives exactly the gap's
retention reward. The complete flow reward is the assignment reward plus
`C0`.

Conversely, decompose an integral complete flow into birth-to-target
paths. Time only moves forward, so every decoded edge meets lag. If a
path entered its value chain after the earliest possible time, its linear
entry reward is at most the decoded birth price. Also, every unit crossing
a rewarded value-chain segment supplies a later same-value target from a
birth at or before the gap cut. Thus a rewarded segment guarantees that
the decoded assignment retains that gap. A generic path that decodes as
an identity can only gain the nonnegative identity bonus.

The decoded assignment consequently has reward at least the flow reward
minus `C0`. Together with canonical routing, this proves equality of
optima. Integral minimum-cost flow therefore supplies an integer minimum
of

```
J(f) = 2*G(f)+s*E(f).
```

This also proves that the structured gap relaxation has an attaining
integer candidate under the long-or-last condition. It does not assert
integrality of the full feasible polytope.

## Extracting the existing finite certificate

Use costs equal to negative rewards. Let `p(node)` be residual potentials
with nonnegative reduced costs. Write `e_j` for the value node at target
deadline `j+R`. The zero-cost bulk segment gives

```
delta_g = p(e_p)-p(e_t) >= 0.
```

For each last gap set `lambda_g=w_g` and `mu_g=0`. For every other gap set

```
lambda_g = min(w_g,delta_g)
mu_g = w_g-lambda_g.
```

This includes zero-reward short nonlast gaps, whose multipliers are zero.
For target column `j`, define a suffix over the nonlinear gaps only:

```
q_j = sum_{g not in H, value(g)=target[j], j<=p_g} lambda_g.
```

Use certificate rows and columns

```
alpha_b = p(birth_b)
beta_j = -p(target_j)+q_j.
```

Along a canonical generic path, the non-chain arcs contribute at least
the linear birth price. The bulk-chain potential drops contribute at
least the `lambda` values of the crossed nonlinear gaps. Adding `q_j`
supplies the remaining suffix. This proves the required edge inequality

```
alpha_b+beta_j >= s*[b=j]
    + sum_{g: value(g)=target[j], b<=k_g} lambda_g.
```

For an identity edge, the direct arc gives the identity and linear birth
terms. Every nonzero nonlinear multiplier belongs to a long gap, so the
no-bypass argument gives its full required birth suffix exactly as `q_j`.
The gap inequalities hold because `lambda_g+mu_g=w_g`.

The network's only active internal capacity bounds are the unit reward
arcs. Their upper-bound multipliers are
`max(w_g-delta_g,0)=mu_g`. Flow optimality therefore gives network reward

```
sum_b p(birth_b) - sum_j p(target_j) + sum_g mu_g.
```

Each nonlinear gap appears in exactly `a_g` target suffixes, so
`sum_j q_j=sum_{g not in H} a_g*lambda_g`. Substitution into the existing
joint dual objective cancels these nonlinear constants. The linear
constants leave precisely `-C0`. Thus the extracted certificate attains
the assignment reward, and its lower bound satisfies `L=J(f)`.

The already proved empty-source realizer and surplus certificate then
give a trace with the factor-two surplus bound. This last step uses the
existing Lean theorems once the finite output data and validity are
supplied. A general Lean implementation and correctness proof for this
flow solver have not been added.

## Check and runtime scope

`scripts/optimality-long-or-last-flow.mjs` builds the network, solves its
small instances with exact BigInt arithmetic, decodes an assignment,
chooses legal cheapest birth methods, and extracts the joint certificate.
The existing independent certificate checker verifies every coefficient
and checks attainment.

Seven named cases include three separated copies, a long gap followed by
a short last gap, two interacting values, zero SWAP price, movement that
costs more than reuse, and a zero-reward short nonlast gap. The check
compares every lag-valid endpoint assignment in each case, 1,645 in total.
It checks every canonical assignment route as well as the optimal flow.
A positive short nonlast gap is rejected. Evidence is saved in
`Bench/evidence-long-or-last-flow.json`.

These checks support the paper construction; they are not a Lean flow
proof. The checker uses Bellman-Ford and makes no production runtime
claim. Successive shortest paths with potentials and Dijkstra on this
sparse graph gives `O(n^2 log n)` arithmetic operations. That exceeds the
strict `O(n^2)` production ceiling. Faster exact flow methods have their
own arithmetic and bit-length bounds. No production solver is proposed
here.

Reproduce with:

```
node scripts/optimality-long-or-last-flow.mjs
```
