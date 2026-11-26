import Skel.Lean.Refute

/-! The fit of a result term on the runs of a loop (task DISC-RESULT): the dynamic pass for the result. A result term `out` of
a loop head is the value that the exit of the loop gives, as a function of the state at the head. On a run from an admitted
head state, the result at each visit of the head is the expected result of the whole run. `fits` checks this at each visit,
as Daikon checks an invariant at each visit. The refuter and the closer check the term again; a fit is only a filter. -/

namespace Skel.Refute
open Lift.Sem Coordinator.Dst

/-- `out g x` is `expected` at the state `x` and at each later visit of `head`, at most `k` visits, and the return of the run
is `expected`. -/
def fitsFrom {L σ γ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat) (out : γ → σ → R) (g : γ)
    (expected : R) : Nat → σ → Bool
  | 0, _ => true
  | k + 1, x => out g x == expected && match stepTo b head fuel head x with
    | .head y => fitsFrom b head fuel out g expected k y
    | .ret r => r == expected
    | .fail _ => true

/-- The number of the admitted samples `0, 2, 4, …` (the indices of `sampleAtG`) below `2 * runs` on whose runs `out` fits.
An index with no admitted input (`AdmitFn.admit` gives none) does not fit. -/
def fitCount {L σ γ R : Type} {α : Type} [AdmitFn α γ σ R] [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (out : γ → σ → R) (admitted : α) (seed runs : Nat) : Nat :=
  ((List.range runs).filter fun i =>
    match AdmitFn.admit admitted (Rng.stream (Rng.ofSeed seed) (2 * i)) with
    | some (g, x, e) => fitsFrom b head fuel out g e 4096 x
    | none => false).length

/-- The number of the free samples `1, 3, 5, …` below `2 * runs` on which one step from the head keeps `out`: the next visit
has the same result, or the return gives it. A free state need not satisfy the invariant, so a right result term can fail on
some; the count ranks the terms that fit each admitted run (a term that is the constant result of the input fits each
admitted run and fails on most free states). A step that fails counts as kept. -/
def freeFitCount {L σ γ R β : Type} [FreeFn β γ σ] [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (out : γ → σ → R) (free : β) (seed runs : Nat) : Nat :=
  ((List.range runs).filter fun i =>
    match FreeFn.draw free (Rng.stream (Rng.ofSeed seed) (2 * i + 1)) with
    | none => false
    | some (g, x) =>
      match stepTo b head fuel head x with
      | .head y => out g y == out g x
      | .ret r => r == out g x
      | .fail _ => true).length

end Skel.Refute
