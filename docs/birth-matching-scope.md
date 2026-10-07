# Birth quotas and endpoint identities

The offline birth-job assignment and the endpoint assignment solve different
problems. `optimality-birth-matching.mjs` assigns birth values to time slots.
Its inventory deadlines constrain value counts. Its mismatch objective counts
positions where the assigned value differs from the target value.

`optimality-fixed-word-matching.mjs` takes an already supplied birth word.
It assigns individual copies to equal-valued output positions. Its objective
counts copies whose endpoint differs from their birth position. The Hall
slack test makes this objective exact for a fixed word. The script uses a
reservation sweep; the separate Lean implementation uses an earliest feasible
reservation scan. Lean proves that the latter has minimum moved-token count.
There is no formal refinement theorem from the JavaScript sweep to Lean.

A value mismatch count can be smaller than the moved-token count. With
reach 2, birth word `b a b a` and target `a a b b` have two value mismatches,
but every valid endpoint assignment moves at least three copies. The copy
of `a` at position 1 must move so that output position 0 meets its deadline.

Do not bind an output occurrence's generation deadline to the endpoint of
that same copy. Consider reach 2, empty source, and target `a b b b a`.
The sequence

```
LOAD a; LOAD b; DUP2; DUP2; DUP1; SWAP2
```

has birth word `a b a b b`, one direct birth per value, and one SWAP.
Its endpoint permutation is `[0,1,4,3,2]`, which moves two copies. A model
that also binds generation-job identity to endpoint identity requires at
least three moved copies. That model excludes this valid trace.

The joint optimizer must therefore keep value-count generation quotas and
endpoint-copy assignments separate. The present fixed-word Lean theorem
does this. It does not optimize birth order. Saved assignment certificates
and small exhaustive checks are offline evidence, not a proof of a joint
optimizer or a global factor-two bound.
