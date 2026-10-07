import Shuffler.Optimality.BirthPlacement.Word.Theorems
import Shuffler.Optimality.BirthPlacement.Word.Cached

namespace Shuffler.Optimality.BirthPlacement.Word

variable {α : Type*} [DecidableEq α] {size reach : Nat}
variable {births target : Fin size → α} {matching : Equiv.Perm (Fin size)}

-- Removing a moved, value-correct row fixes it and joins its two incident edges.
-- Minimum moved count therefore requires that the joined edge miss the deadline.
omit [DecidableEq α] in
theorem minimum_support_no_shortcut
    (hcompatible : ∀ index, births index = target (matching index))
    (hdeadline : ∀ index, index.val ≤ (matching index).val + reach)
    (hminimum : ∀ other : Equiv.Perm (Fin size),
      (∀ index, births index = target (other index)) →
      (∀ index, index.val ≤ (other index).val + reach) →
      matching.support.card ≤ other.support.card)
    (position : Fin size) (hsame : births position = target position)
    (hmoved : matching position ≠ position) :
    (matching position).val + reach < (matching.symm position).val := by
  by_contra hnot
  have hshortcut : (matching.symm position).val ≤ (matching position).val + reach := by omega
  let other := Equiv.swap position (matching position) * matching
  have hvalues : target position = target (matching position) :=
    hsame.symm.trans (hcompatible position)
  have hoCompatible : ∀ index, births index = target (other index) := by
    intro index
    simpa only [other, Equiv.Perm.mul_apply, Equiv.apply_swap_eq_self hvalues] using
      hcompatible index
  have hoDeadline : ∀ index, index.val ≤ (other index).val + reach := by
    intro index
    by_cases hi : index = position
    · subst index
      simp [other]
    · by_cases he : matching index = position
      · have hi' : index = matching.symm position :=
          (matching.eq_symm_apply).mpr he
        change index.val ≤ (Equiv.swap position (matching position) (matching index)).val + reach
        rw [he, Equiv.swap_apply_left, hi']
        exact hshortcut
      · have he' : matching index ≠ matching position := matching.injective.ne hi
        simpa only [other, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne he he'] using hdeadline index
  have hle := hminimum other hoCompatible hoDeadline
  have hlt := Equiv.Perm.card_support_swap_mul hmoved
  change other.support.card < matching.support.card at hlt
  omega

omit [DecidableEq α] in
theorem minimum_support_backward
    (hcompatible : ∀ index, births index = target (matching index))
    (hdeadline : ∀ index, index.val ≤ (matching index).val + reach)
    (hminimum : ∀ other : Equiv.Perm (Fin size),
      (∀ index, births index = target (other index)) →
      (∀ index, index.val ≤ (other index).val + reach) →
      matching.support.card ≤ other.support.card)
    (position : Fin size) (hsame : births position = target position)
    (hmoved : matching position ≠ position) :
    (matching position).val < position.val ∧ position.val < (matching.symm position).val := by
  have hskip := minimum_support_no_shortcut hcompatible hdeadline hminimum position hsame hmoved
  have hleft := hdeadline position
  have hright := hdeadline (matching.symm position)
  rw [matching.apply_symm_apply] at hright
  omega

theorem optimal_backward (hcount : Balanced births target)
    (hbase : Feasible reach births target) (position : Fin size)
    (hsame : births position = target position)
    (hmoved : optimal reach births target hcount position ≠ position) :
    (optimal reach births target hcount position).val < position.val ∧
      position.val < ((optimal reach births target hcount).symm position).val :=
  minimum_support_backward (optimal_compatible hcount) (optimal_deadline hcount hbase)
    (fun other hc hd => support_card_le hcount other hc hd) position hsame hmoved

theorem cachedOptimal_backward (hcount : Balanced births target)
    (hbase : Feasible reach births target) (position : Fin size)
    (hsame : births position = target position)
    (hmoved : cachedOptimal reach births target hcount position ≠ position) :
    (cachedOptimal reach births target hcount position).val < position.val ∧
      position.val < ((cachedOptimal reach births target hcount).symm position).val := by
  rw [cachedOptimal_eq] at hmoved ⊢
  exact optimal_backward hcount hbase position hsame hmoved

end Shuffler.Optimality.BirthPlacement.Word
