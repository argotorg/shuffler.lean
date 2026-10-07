# Full prices suffice when each premium value has at most two copies

The following restricted result is proved in Lean. It concerns an empty
source, target values that all permit direct introduction, and the actual
reach-16 plan realizer. DUP and SWAP scores can differ. Scores can use
arbitrary `PrimitiveCosts` and gas/byte `Weights`.

Let `d_v` be the least legal direct score of value `v`, and let `u,s` be
the DUP and SWAP scores. Require

```
d_v > u  implies  count_target(v) <= 2.
```

Values for which direct introduction costs at most DUP can occur any
number of times. This condition is `Dual.PairwisePremiums`.

Set each optional gap price to its full doubled reuse reward:

```
lambda_g = w_g = 2*max(d_value(g)-u,0).
```

Supply a lag-valid endpoint permutation that maximizes the fixed-price
assignment reward. Select the cheapest legal method for its births and
use the proved plan realizer. The resulting trace has at most twice the
surplus of every empty-source trace to the same target without POP.
The plan also minimizes `J=2*generation+s*moved`, over all feasible birth
words, endpoint assignments, and birth methods.

The maximum-reward assignment is an explicit input. This result does not
implement an assignment solver or prove an `O(n^2)` runtime. The sparse
oracle described in [the fixed-price note](priced-assignment-oracle.md)
is a separate paper-level construction. No outer price search or
fractional rounding is needed for this restricted theorem.

## The proof

For a gap after target position `p`, let `a` be the number of copies of
its value through `p`, and let `C` be the number of births of that value
through row `p+R`. Lag forces all target positions through `p` to have
been born by then. Their multiset is contained in that birth prefix.
Subtracting these required births leaves at most `R` copies in total.
It also leaves at most the remaining target count of each value. Thus

```
C-a <= min(R, count_target(v)-a).
```

`birth_prefix_surplus_le` proves this count bound for any natural reach
`R`. The actual plan specialization uses reach 16. The count proof also
includes the shrinking final prefix, since the prefix length is the
minimum of the cut length and target length.

At a positive-reward gap, the copy condition gives `count_target(v)<=2`,
while `a>=1`. Therefore `a<=C<=a+1`. Its retained-gap indicator is exactly
`y=C-a`, so

```
w_g*C_g = w_g*(a_g+y_g).
```

The same equality holds at zero-reward gap slots without a count bound.
Consequently the capped reuse reward is linear on every legal assignment
in this restricted class.

The next step is an equality for the cheapest birth methods:

```
2*D = 2*G + sum_g w_g*y_g.
```

The existing proof mapped each DUP to its preceding target occurrence.
The new converse starts with a retained gap, selects the next equal-value
birth in occurrence order, and proves that this birth is within the gap's
deadline. A prior copy is then available. If its reuse reward is positive,
the cheapest-method function selects DUP. This gives both directions of
the discount sum. `cheapest_generation_discount_eq` proves the equality
for every all-direct-legal target, without the two-copy restriction.

Define the full-price assignment reward by

```
A_f = s*fixed(f) + sum_g w_g*C_g(f).
```

For every plan under the copy restriction,

```
J(f)+A_f >= 2*D+s*n+sum_g w_g*a_g.
```

For the cheapest birth methods this is an equality. Therefore maximizing
`A_f` minimizes `J`. `pairwise_cheapest_globallyMinimal` proves this step
from `FullPriceOptimal`, which states only the finite assignment
optimization problem.

Finally, the existing global plan theorem compares the realized trace
against every same-target empty-source trace without POP. It gives the
total-score bound and the factor-two surplus bound above. The wrapper
`pairwise_cheapest_surplus_le_twice` has no same-word or fixed-order
premise.

## A finite certificate entry point

An oracle can instead supply row/column potentials and a permutation.
The finite checks are:

- `Certificate.Valid`: every legal assignment edge satisfies the dual
  inequality, and the scale is positive.
- `Certificate.FullPrices`: quota weights equal the scaled gap rewards;
  cap weights are zero.
- `Certificate.TightFor`: every edge of the supplied permutation attains
  its row/column bound.

Under the copy restriction and direct-introduction premise,
`Certificate.pairwise_attains` proves exact equality of the lower bound
and the cheapest plan objective. `Certificate.pairwise_globallyMinimal`
then proves the global plan minimum. These checks need no trust in the
program that supplied the assignment or potentials. They also do not
prove that a program finds such data within a given runtime.

## Scope and checks

`Tests/OptimalityPairwiseDual.lean` uses a target with two spilled-variable
copies separated by 16 PUSH0 values. The supplied assignment exchanges
positions 16 and 17. The theorem itself selects DUP at birth 16. The
PUSH0 value occurs 16 times and has zero premium, so it meets the stated
condition.

The tests cover byte-only, gas-only, mixed gas/byte, and unequal DUP/SWAP
scores. They check an empty target, reject a third positive-premium copy,
reject a non-full price vector, and reject a nontight identity assignment.
The byte example has `J=104`; the mixed-weight example has `J=488`.
The new theorem audits use only `propext`, `Classical.choice`, and
`Quot.sound`.

The generic count lemma also explains the reach-one case on paper: every
gap then has `C-a<=1`, even for values with more than two copies. The
repository's trace realizer is fixed at reach 16, so this note does not
claim a new Lean trace theorem at reach one.

For unrestricted targets at reach 16, a positive-reward gap can contain
more than one spare copy. Its full price then charges those extra copies
although its reuse reward pays for only one. The exact defect identity
in [the direct-certificate note](direct-certificate-invariant.md) records
this remaining term. The general constructor and its required runtime
remain open.
