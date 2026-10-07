# One long gap and two SWAPs

This is a constructive paper proof for one restricted family. The stack
realization in this note is not yet a Lean theorem. It does not prove the
global factor-two claim.

The finite slot-choice part is proved in
`Shuffler/Optimality/Collective/OneGap/Theorems.lean`.
`exists_middle_of_lastRoot` is the pigeonhole lemma, and
`exists_carrierSlots` supplies the one-hop or two-hop positions.
`Family.exists_carrierSlots` applies it to the stated target family.

## Input

Use zero-based positions. Let the DUP reach be `R`, and let SWAP reach one
position farther down the stack. Thus DUP reads at most `R` values and
SWAP can exchange the top with a value at distance at most `R`.

The source is empty. The target ends at position `j`, with:

- `1 ≤ R < j ≤ 2R`.
- The value `a` occurs at positions `0` and `j`, and nowhere between them.
- Every other pair of consecutive equal values has distance at most `R`.
- Every target kind has an available direct instruction.

Retain every repeated kind. The required direct budget is one introduction
per kind. The gap transport count is exactly one: only the gap `0 → j` is
longer than `R`.

We construct a trace that uses one direct introduction per kind and at most
two SWAPs. Every other birth is a DUP. Every operation respects its reach.

## Choose the first carrier position

A position is a root if it is the first occurrence of its value in the
target. Let `p` be the last root position in `1 .. R`.

This set is not empty. Position `1` is a root because its value differs
from `a`. Let `x = target[p]`.

At position `p`, create the second `a` instead of `x`. The first `a` is
still DUP-readable because `p ≤ R`. This second copy is the carrier.
The birth of `x` is delayed. If another `x` is needed before the delayed
birth, that occurrence becomes the direct introduction instead. Equal
copies can serve different target occurrences.

## One hop when possible

If `p ≥ j − R`, emit the target values at all other interior positions.
At position `j`, create the delayed `x`, then use SWAP at distance `j − p`.
This puts `x` at `p` and `a` at `j`.

The SWAP is reachable. Since `p` was a root, removing its original birth
does not remove an older dependency. If an `x` appears between `p` and `j`,
the first such occurrence uses the direct instruction, and all later ones
use DUP. The final birth of `x` is reachable from one of those copies,
because every such position is greater than `p ≥ j − R`. If no `x`
appears there, the final birth is its direct introduction.

## Find an intermediate position

Now suppose `p < j − R`. Consider the interval of positions

```text
I = [j − R, p + R].
```

It contains at least `p + 1` positions because `j ≤ 2R`. At least one
position `k` in `I` has one of these properties:

1. `k` is a root.
2. The previous equal occurrence of `target[k]` is at least `j − R`.

To prove this, suppose neither property holds anywhere in `I`. No two
positions in `I` can have the same value: the later one would have an
equal predecessor in `I`, which gives property 2. Each value in `I` has
an earlier occurrence before `j − R ≤ R`. Its root is therefore in
`1 .. p`, by the definition of `p`. Thus at least `p + 1` distinct values
would have roots in only `p` positions. This is impossible.

## Two hops

Let `y = target[k]`. The birth word agrees with the target except at
three positions:

```text
birth[p] = a
birth[k] = x
birth[j] = y
```

Immediately after the birth at `k`, use SWAP at distance `k − p`.
Immediately after the birth at `j`, use SWAP at distance `j − k`.
The carrier moves along `p → k → j`. Both distances are positive and
at most `R`. The first SWAP fixes position `p`; the second fixes `k`.

The delayed `x` is valid by the root argument used for the one-hop case.
After it moves down to `p`, later `x` births are also valid. If another
`x` already exists, its unchanged target position supplies the usual
short-gap DUP. Otherwise, the next `x`, if any, is within distance `R`
of `p` by the input assumption.

If `k` is a root, the same root argument applies to delayed `y`. Otherwise
there is a copy of `y` at a position `u ≥ j − R` before `k`. That copy
remains in place and is DUP-readable through position `j`. It replaces
any dependence on the omitted birth at `k`.

This also covers `x = y`. In that case, `k` is not a root, and its copy
at `u ≥ j − R > p` is distinct from the displaced root at `p`. The
SWAPs do not remove the copy at `u`.

Every other kind keeps its ordinary birth positions. Its consecutive
gaps remain at most `R`. This proves the claimed introduction budget
and the two-SWAP bound.

## Status and next limit

The exact finite tests cover 870 plans with reaches 1 through 4. Every
plan has a realization with at most two SWAPs. All 200 returned witnesses
that use two SWAPs have the carrier form above. The finite carrier
constructor also succeeds on the checked larger collision family through
reach 16.

This proof uses one carrier and an empty source. Several long intervals
can displace each other's roots and retained copies. A global proof must
account for those interactions and for mandatory old copies. The present
argument does not yet supply that account.

## A limit of the single-carrier invariant

The checkpoint `target.take p ++ [a]` is too restrictive for a general
factor-two proof. Consider a middle word that cycles through `R − 1`
distinct background kinds. Retain all intervals. The active inventory
is exactly `R`: the carrier `a` and the `R − 1` background kinds.

For `R ≥ 3`, a non-root position `p` has its previous equal occurrence
at `p − (R − 1)`. If its birth is delayed, a carrier hop must finish by
`p + 1`, or the background value loses DUP reach. Initial roots can hop
as far as `p + R`. Thus the first reachable carrier frontier is `2R − 1`,
and each later hop extends it by only one position.

For example, with `R = 4` and target `a (b c d)^4 a`, the final position
is `j = 13`. The gap transport count is three, but this checkpoint form
needs seven SWAPs, which is greater than twice that count. With `R = 5`
and `a (b c d e)^3 a`, the count is two and the form needs five SWAPs.

These examples first refute the restricted carrier form as a global
proof method. Exact search then checks unrestricted traces for these
small reaches. For reach four, the minimum is six SWAPs. For reach five,
the minimum is five SWAPs, which exceeds twice the gap count. Three
independent search formulations agree on the reach-five result. The
evidence is in `Bench/evidence-carrier-cycle-obstruction.json`.

Thus twice the independent gap count is not a valid realization bound
for every reach. This finite result does not settle the claim for the
production reach of sixteen. A general lower bound must also account
for movement forced by the short-gap values that share the available
positions with a retained long-gap value.
