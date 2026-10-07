import Shuffler.Optimality.BirthPlacement.Dual.Plan

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {target : Stack}

theorem birthWord_count (assignment : Equiv.Perm (Fin target.length)) (value : Value) :
    (birthWord target assignment).count value = target.count value := by
  rw [← RawWord.positions_card, ← RawWord.positions_card, birthWord, RawWord.positions_ofFn]
  exact Word.balanced_of_matching assignment (fun _ => rfl) value

theorem target_prefix_le_birth_prefix (assignment : Equiv.Perm (Fin target.length))
    (hdeadline : BirthDeadlines reach assignment) (position : Nat) :
    (target.take (position + 1) : Multiset Value) ≤
      ((birthWord target assignment).take (position + reach + 1) : Multiset Value) := by
  apply Multiset.le_iff_count.mpr
  intro value
  simp only [Multiset.coe_count]
  have hh := Word.feasible_of_matching
    (births := fun index => target[assignment index])
    (target := fun index => target[index]) assignment (fun _ => rfl) hdeadline value
  change Hall.Condition reach
    (Word.positions (fun index => target[assignment index]) value)
    (RawWord.positions target value) at hh
  rw [← RawWord.positions_ofFn] at hh
  have hc := hh (position + reach)
  rw [RawWord.due_card, RawWord.born_card] at hc
  simpa only [birthWord, show position + reach + 1 - reach = position + 1 by omega] using hc

theorem birth_prefix_surplus_le (assignment : Equiv.Perm (Fin target.length))
    (hdeadline : BirthDeadlines reach assignment) (position : Fin target.length) (value : Value) :
    ((birthWord target assignment).take (position.val + reach + 1)).count value -
        (target.take (position.val + 1)).count value ≤
      min reach (target.count value - (target.take (position.val + 1)).count value) := by
  have hle := target_prefix_le_birth_prefix assignment hdeadline position.val
  have hcount := Multiset.count_le_card value
    (((birthWord target assignment).take (position.val + reach + 1) : Multiset Value) -
      (target.take (position.val + 1) : Multiset Value))
  rw [Multiset.count_sub, Multiset.card_sub hle] at hcount
  simp only [Multiset.coe_count, Multiset.coe_card, List.length_take,
    birthWord, List.length_ofFn] at hcount
  have htotal := (List.take_sublist (position.val + reach + 1)
    (birthWord target assignment)).count_le value
  rw [birthWord_count] at htotal
  apply Nat.le_min.mpr
  constructor
  · have hp := position.isLt
    change ((List.ofFn fun index => target[assignment index]).take
      (position.val + reach + 1)).count value - _ ≤ _
    omega
  · omega

theorem targetGap_surplus_le (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) (index : Fin target.length) :
    prefixCount target (targetGap costs weights spills target index) plan.assignment -
        (targetGap costs weights spills target index).required ≤
      min 16 (target.count target[index] - (target.take (index.val + 1)).count target[index]) := by
  rw [prefixCount_eq_count]
  exact birth_prefix_surplus_le plan.assignment plan.deadlines index target[index]

end Shuffler.Optimality.BirthPlacement.Dual
