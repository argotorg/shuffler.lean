# Fixed birth words with an initial source

This note gives a paper proof and finite exact checks. The general-source
existence theorem is not yet proved in Lean. The empty-source theorem in
`RawWord/Theorems.lean` remains the proved public result.

Let `R` be both the DUP reach and the maximum SWAP depth. Production uses
`R = 16`. Let the source have length `n <= R + 1`, let `w` be the ordered
birth values, and let `t` be the exact target. There is no POP.

For a stage `k`, define:

```text
b = n + k
P_k = source ++ w.take k
F_k = t.take (b - R).
```

Subtraction stops at zero. The proposed condition is:

1. `source ++ w` and `t` have the same multiset.
2. For every `k` from zero through `w.length`, `F_k` is a submultiset of
   `P_k`.
3. For every next value `v = w[k]`, direct generation is available, or
   `count(v, P_k) > count(v, F_k)`.

These clauses use the initial source, target, and word. They do not
simulate a stack.

## Necessity

At height `b`, before a birth, every target position below `b - R` must
already be correct. After the birth, those positions lie outside SWAP
reach, and future no-POP operations cannot repair them. Their values
must therefore occur in `P_k`, which proves clause 2.

DUP can read exactly the top `R` positions. The lower prefix is `F_k`.
Subtract its value counts from the total counts in `P_k`. A DUP of `v`
requires a positive remaining count. A direct birth requires its direct
instruction to be available. This proves clause 3. The trace's multiset
balance proves clause 1.

At the final height, the quota in clause 2 follows from clause 1, even
though there is no further birth.

## Sufficiency

Keep a correct target prefix and a working suffix of at most `R + 1`
values. Initially the prefix is empty and the normalized source fits in
the suffix.

Before the next birth:

- If the working suffix has at most `R` values, no new position needs to
  be fixed.
- If it has `R + 1` values, its bottom position will become unreachable
  after the birth. Clause 2 supplies the required target value somewhere
  in that suffix. If it is already at the bottom, keep it there.
  Otherwise, SWAP the required value to the top, then SWAP it into the
  bottom position. Each operation is within reach. This uses at most two
  SWAPs and extends the correct prefix by one.

The correct prefix now has length `b - R`, or zero when `b < R`. The
remaining suffix is readable by DUP. Clause 3 supplies the next direct
birth or DUP. Append the value and continue.

After the last birth, clause 1 makes the remaining suffix a permutation
of the remaining target suffix. It has at most `R + 1` positions, so
reachable top SWAPs can sort it. This yields the exact target and keeps
exactly the requested ordered birth values.

## Existing Lean components

`Placement.placeExisting` already builds the two-SWAP boundary repair
as a production trace. Its result has no POP and no additions.
`BirthPlacement.appendBirth` builds a direct or DUP birth from a physical
availability proof. `Placement.buildWorking` with `missing = 0` can sort
the final suffix without births. `Placement.canPlace_perm_append` also
proves existence for that suffix permutation.

A separate computable constructor still needs a source-offset state
invariant, preservation of the quota and availability clauses, and a
necessity proof with that offset. This is not a direct wrapper around
the empty-source `BuildState`. None of these general-source claims have
been added to its API.

## Initially frozen positions

For a source longer than `R + 1`, first require

```text
source.take (n - R - 1) = target.take (n - R - 1).
```

Those positions cannot change in a no-POP trace. Remove this equal
prefix from both lists, then use the normalized condition above. The
finite checker accepts only already normalized inputs.

## Finite check

`scripts/optimality-source-word-feasibility.mjs` compares the condition
with complete reachability over actual value stacks. The search permits
every legal SWAP, matching DUP, and direct birth. It does not use the
quota condition or prune by target prefixes.

The check covered 20,812 endpoint cases, including 14,356 feasible and
6,456 infeasible cases. It used reaches 1, 2, and 3, source lengths up to
`R + 1`, at most three births, and at most six total values. Profiles
include literals, unavailable variables, and spilled variables. Every
accepted case also runs the paper construction through the instruction
replay. Separate tests cover the production SWAP16 boundary.

The recorded counts are in `Bench/evidence-source-word-feasibility.json`.
This evidence supports the paper argument; it does not replace a Lean
proof.
