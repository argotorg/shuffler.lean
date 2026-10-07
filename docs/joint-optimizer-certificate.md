# The remaining global optimizer certificate

The global empty-source factor-two result now has a Lean reduction theorem.
It is conditional on an optimizer certificate. No algorithm in this module
constructs that certificate for every target.

For a feasible birth plan, let `G` be its weighted introduction score, `E`
its number of moved endpoint tokens, and `s` the weighted price of SWAP.
The exact objective is

```
J = 2*G + s*E.
```

The target generation baseline `B` is constant across all plans. Thus
minimizing `J` is equivalent to minimizing `2*(G-B) + s*E`.
`Plan.GloballyMinimal` states that the supplied plan minimizes `J` over
all feasible plans for the same target and fixed spill set.

`Plan.minimum_surplus_le_twice` proves that the production trace from
such a plan satisfies

```
score(result) - B <= 2 * (score(other) - B)
```

for every empty-source trace to that target without POP. The other trace
can have any birth word, copy assignment, and introduction methods.
`Plan.minimum_score_le_twice` gives the corresponding total-score bound.

The proof has three steps. Every other trace gives a feasible plan with
the same introduction score and at most twice its SWAP count in moved
endpoint tokens. The optimizer certificate bounds `J` by this plan's
objective. The realizer costs at most `G+s*E`, and `B <= G`. These facts
give both bounds without further facts about the stack states.

Only birth-word selection remains in the certificate. For a word that
meets `RawWord.Feasible`, `wordObjective` runs the proved cheapest-method
and minimum-endpoint choices. `Plan.MinimizesWords` compares the proposed
plan against that computed objective for every feasible word.
`Plan.globallyMinimal_iff_minimizesWords` proves that this certificate is
equivalent to the all-plan certificate. This separates the remaining
combinatorial optimizer from the trace proofs.

The present code constructs the fixed-word optimizer and its traces. It
does not construct a minimum word, prove a polynomial joint optimizer, or
extend this certificate theorem to a nonempty source. The original BBU
and the portfolio schedule do not use a global certificate.
