# Optional generation discounts with an initial source

The source generation-discount bridge is proved in Lean. It does not
choose a birth word or an assignment.

Let `s(v)` be the source count of value `v`. At a target position `p`, let
`a(p)` be the number of equal values through that position. The ordinary
gap reward is twice the positive difference between direct generation and
DUP. A source gap receives that reward only when:

- another equal target occurs after `p`; and
- `s(target[p]) ≤ a(p)`.

Earlier gaps connect copies already supplied by the source. They have no
generation reward. `sourceTargetGap` defines this mask. The reuse bit is
one exactly when the source plus birth word has more than `a(p)` equal
copies by absolute birth position `p+16`.

The accounting total `D_source` is the direct-price total of the target
minus that of the source. For a value with no legal direct instruction,
the existing `directPrice` function uses the DUP price. This is an
accounting convention. It does not make a direct instruction legal.
Hard values therefore have zero optional reward.

For every valid source plan, Lean proves:

```
2*D_source ≤ 2*G + sum(reward*reuse).
```

Here `G` is the score of the real birth events. With the cheapest legal
method for each supplied birth, this is an equality. Both statements
allow hard values, empty sources, and plans with no births.

The proof maps each real DUP to the preceding equal target occurrence
by occurrence rank. Different DUPs map to different gaps. Every real
birth follows all source copies, so its preceding rank is at least the
source count. Conversely, an eligible retained gap has a next equal
birth after the initial source. That next birth has a legal DUP at its
absolute height. If the reward is positive, the cheapest method uses it.

The public proof files are:

- `Dual/SourceDiscount/Generation.lean`: the inequality and source accounting;
- `Dual/SourceDiscount/Cheapest.lean`: exact equality for cheapest methods;
- `Dual/SourceDiscount/Trace.lean`: optional-price certificate bounds for
  production traces.

The trace theorem uses the existing `sourceAllowed` edge restrictions.
A valid finite certificate gives a lower bound `L≤2*score(other)` for
every source-to-target trace without POP. If a supplied candidate has
`score(candidate)+B≤L`, it has the factor-two bound above the generation
baseline `B`. This check does not require an optimum assignment.

The existing hard mandatory-quota API remains separate. Its quota theorem
is unchanged. The new optional-gap certificate theorem uses the optional
gap family; it does not itself concatenate that family with an additional
family of mandatory quotas.

`Tests/OptimalitySourceDiscount.lean` checks the source-count mask, a hard
value, the absolute DUP16/DUP17 boundary, a plan with no births, a positive
optional price on a production source trace, and an invalid unmasked
certificate. All audited theorems use only the standard Lean proof axioms.
