import Shuffler.Optimality.BirthPlacement.Dual

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {target : Stack} {gaps : Fin gapCount → Gap}

theorem prefix_weight_sum (target : Stack) (gap : Gap)
    (assignment : Equiv.Perm (Fin target.length)) (weight : Int) :
    (∑ birth, if covers target gap birth (assignment birth) then weight else 0) =
      weight * prefixCount target gap assignment := by
  rw [← Finset.sum_filter]
  simp [prefixCount, mul_comm]

theorem fixed_weight_sum (assignment : Equiv.Perm (Fin size)) (weight : Int) :
    (∑ birth, if birth = assignment birth then weight else 0) =
      weight * (Word.fixed assignment).card := by
  rw [← Finset.sum_filter]
  simp [Word.fixed, eq_comm, mul_comm]

theorem Certificate.reward_le (cert : Certificate target.length gapCount)
    (hvalid : cert.Valid gaps swap)
    (assignment : Equiv.Perm (Fin target.length)) (hdeadline : BirthDeadlines 16 assignment)
    (reuse : Fin gapCount → Nat) (hcap : ∀ gap, reuse gap ≤ 1)
    (hquota : ∀ gap, (gaps gap).required + reuse gap ≤ prefixCount target (gaps gap) assignment) :
    cert.scale * (swap * (Word.fixed assignment).card +
      ∑ gap, (gaps gap).reward * reuse gap : Nat) ≤ cert.rewardUpper gaps := by
  have hedge := Finset.sum_le_sum (fun birth (_ : birth ∈ Finset.univ) =>
    hvalid.2.1 birth (assignment birth) (hdeadline birth))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Equiv.sum_comp assignment cert.column, fixed_weight_sum] at hedge
  rw [Finset.sum_comm] at hedge
  simp_rw [prefix_weight_sum] at hedge
  have hgap (gap : Fin gapCount) :
      (cert.scale * (gaps gap).reward * reuse gap +
        cert.quotaWeight gap * (gaps gap).required : Nat) ≤
          cert.quotaWeight gap * prefixCount target (gaps gap) assignment + cert.capWeight gap := by
    have h₁ := Nat.mul_le_mul_right (reuse gap) (hvalid.2.2 gap)
    have h₂ := Nat.mul_le_mul_left (cert.quotaWeight gap) (hquota gap)
    have h₃ := Nat.mul_le_mul_left (cert.capWeight gap) (hcap gap)
    nlinarith
  have hsum := Finset.sum_le_sum (fun gap (_ : gap ∈ Finset.univ) => hgap gap)
  have hsumInt :
      (∑ gap, ((cert.scale : Int) * (gaps gap).reward * reuse gap +
        (cert.quotaWeight gap : Int) * (gaps gap).required)) ≤
      ∑ gap, ((cert.quotaWeight gap : Int) * prefixCount target (gaps gap) assignment +
        (cert.capWeight gap : Int)) := by exact_mod_cast hsum
  simp only [Finset.sum_add_distrib] at hsumInt
  simp only [Certificate.rewardUpper, Nat.cast_mul, Nat.cast_add, Nat.cast_sum]
  rw [mul_add, Finset.mul_sum]
  simp_rw [← mul_assoc]
  have hcomm : (∑ gap, (gaps gap).required * (cert.quotaWeight gap : Int)) =
      ∑ gap, (cert.quotaWeight gap : Int) * (gaps gap).required := by
    apply Finset.sum_congr rfl
    intro gap _
    exact mul_comm _ _
  rw [hcomm]
  push_cast at hedge
  linarith

theorem Certificate.lower_le (cert : Certificate target.length gapCount)
    (hvalid : cert.Valid gaps swap)
    (assignment : Equiv.Perm (Fin target.length)) (hdeadline : BirthDeadlines 16 assignment)
    (reuse : Fin gapCount → Nat) (hcap : ∀ gap, reuse gap ≤ 1)
    (hquota : ∀ gap, (gaps gap).required + reuse gap ≤ prefixCount target (gaps gap) assignment)
    (hcost : 2 * direct ≤ 2 * generation + ∑ gap, (gaps gap).reward * reuse gap) :
    cert.lowerNumerator gaps direct swap ≤
      cert.scale * (2 * generation + swap * assignment.support.card : Nat) := by
  have hrewards := cert.reward_le hvalid assignment hdeadline reuse hcap hquota
  have hfixed := Word.fixed_add_support assignment
  have hcostInt : (2 * direct : Int) ≤ 2 * generation + ∑ gap, ((gaps gap).reward * reuse gap : Nat) := by
    exact_mod_cast hcost
  have hcostScaled := mul_le_mul_of_nonneg_left hcostInt (Int.natCast_nonneg cert.scale)
  have hfixedInt : ((Word.fixed assignment).card : Int) + assignment.support.card = target.length := by
    exact_mod_cast hfixed
  have hfixedScaled := congrArg (fun count : Int => (cert.scale : Int) * swap * count) hfixedInt
  unfold Certificate.lowerNumerator
  push_cast at hrewards ⊢
  push_cast at hcostScaled
  nlinarith

end Shuffler.Optimality.BirthPlacement.Dual
