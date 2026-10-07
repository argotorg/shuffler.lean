import Shuffler.Optimality.BirthPlacement.Word.Backward

namespace Tests.OptimalityBackwardPins

open Shuffler.Optimality.BirthPlacement

private def target : Fin 4 → Nat := fun index => [0, 0, 1, 2][index]
private def witness : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 3
private def births : Fin 4 → Nat := fun index => target (witness index)
private theorem balanced : Word.Balanced births target :=
  Word.balanced_of_matching witness (fun _ => rfl)
private theorem feasible : Word.Feasible 2 births target :=
  Word.feasible_of_matching witness (fun _ => rfl) (by decide)
private def canonical := Word.cachedOptimal 2 births target balanced

private theorem canonical_moved : canonical 1 ≠ 1 := by
  have hforce : ∀ index : Fin 4,
      births 3 = target index → 3 ≤ index.val + 2 → index = 1 := by decide
  have hvalues : births 3 = target (canonical 3) := by
    rw [canonical, Word.cachedOptimal_eq]
    exact Word.optimal_compatible balanced 3
  have hreach : 3 ≤ (canonical 3).val + 2 := by
    rw [canonical, Word.cachedOptimal_eq]
    exact Word.optimal_deadline balanced feasible 3
  have he := hforce (canonical 3) hvalues hreach
  have hn := canonical.injective.ne (show (1 : Fin 4) ≠ 3 by decide)
  simpa only [he] using hn

#guard List.ofFn births = [2, 0, 1, 0]
#guard List.ofFn (fun index => (canonical index).val) = [3, 0, 2, 1]

-- Row 1 has the right value, but retaining its endpoint identity would
-- leave the only later copy too late for target row 0.
example : (canonical 1).val < 1 ∧ 1 < (canonical.symm 1).val :=
  Word.cachedOptimal_backward balanced feasible 1 (by decide) canonical_moved

example : (canonical 1).val + 2 < (canonical.symm 1).val := by
  apply Word.minimum_support_no_shortcut
      (matching := canonical) (births := births) (target := target)
  · intro index
    rw [canonical, Word.cachedOptimal_eq]
    exact Word.optimal_compatible balanced index
  · intro index
    rw [canonical, Word.cachedOptimal_eq]
    exact Word.optimal_deadline balanced feasible index
  · intro other hvalues hreach
    rw [canonical, Word.cachedOptimal_eq]
    exact Word.support_card_le balanced other hvalues hreach
  · decide
  · exact canonical_moved

-- At reach 3 that shortcut is legal, and the production routine fixes row 1.
#guard Word.cachedOptimal 3 births target balanced 1 = 1

-- Value compatibility and lag alone do not imply the direction claim.
-- This same-value swap is feasible but does not minimize moved count.
private def avoidable : Equiv.Perm (Fin 2) := Equiv.swap 0 1
example : ∀ index : Fin 2, index.val ≤ (avoidable index).val + 1 := by decide
example : ¬ (avoidable 0).val < 0 := by decide

end Tests.OptimalityBackwardPins
