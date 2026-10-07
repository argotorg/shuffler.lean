import Shuffler.Optimality.BirthPlacement.Dual.Cheapest

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {target : Stack} {gaps : Fin gapCount → Gap}

def Certificate.FullPrices (cert : Certificate size gapCount) (gaps : Fin gapCount → Gap) : Prop :=
  (∀ gap, cert.quotaWeight gap = cert.scale * (gaps gap).reward) ∧
  (∀ gap, cert.capWeight gap = 0)

def Certificate.TightFor (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap) (swap : Nat)
    (assignment : Equiv.Perm (Fin target.length)) : Prop :=
  ∀ birth,
    (if birth = assignment birth then (↑(cert.scale * swap) : Int) else 0) +
      (∑ gap, if covers target (gaps gap) birth (assignment birth)
        then (cert.quotaWeight gap : Int) else 0) =
      cert.row birth + cert.column (assignment birth)

instance (cert : Certificate size gapCount) (gaps : Fin gapCount → Gap) :
    Decidable (cert.FullPrices gaps) := by unfold Certificate.FullPrices; infer_instance

instance (cert : Certificate target.length gapCount) (gaps : Fin gapCount → Gap)
    (swap : Nat) (assignment : Equiv.Perm (Fin target.length)) :
    Decidable (cert.TightFor gaps swap assignment) := by unfold Certificate.TightFor; infer_instance

theorem Certificate.rewardUpper_eq_of_fullPrices (cert : Certificate target.length gapCount)
    (hfull : cert.FullPrices gaps)
    (assignment : Equiv.Perm (Fin target.length))
    (htight : cert.TightFor gaps swap assignment) (reuse : Fin gapCount → Nat)
    (hcounts : ∀ gap, (gaps gap).reward * prefixCount target (gaps gap) assignment =
      (gaps gap).reward * ((gaps gap).required + reuse gap)) :
    cert.rewardUpper gaps =
      cert.scale * (swap * (Word.fixed assignment).card +
        ∑ gap, (gaps gap).reward * reuse gap : Nat) := by
  have hedge := Finset.sum_congr rfl (fun birth (_ : birth ∈ Finset.univ) => htight birth)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Equiv.sum_comp assignment cert.column, fixed_weight_sum] at hedge
  rw [Finset.sum_comm] at hedge
  simp_rw [prefix_weight_sum] at hedge
  have hgap (gap : Fin gapCount) :
      (cert.quotaWeight gap : Int) * prefixCount target (gaps gap) assignment =
      (gaps gap).required * (cert.quotaWeight gap : Int) +
        cert.scale * ((gaps gap).reward * reuse gap : Nat) := by
    calc
      (cert.quotaWeight gap : Int) * prefixCount target (gaps gap) assignment =
          (cert.scale : Int) * ((gaps gap).reward * prefixCount target (gaps gap) assignment : Nat) := by
            rw [hfull.1 gap]
            push_cast
            ring
      _ = _ := by
        rw [hcounts gap, hfull.1 gap]
        push_cast
        ring
  simp_rw [hgap] at hedge
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hedge
  have hcap : (∑ gap, (cert.capWeight gap : Int)) = 0 := by simp [hfull.2]
  unfold Certificate.rewardUpper
  rw [hcap]
  push_cast at hedge ⊢
  nlinarith

theorem Certificate.lower_eq_of_fullPrices (cert : Certificate target.length gapCount)
    (hfull : cert.FullPrices gaps)
    (assignment : Equiv.Perm (Fin target.length))
    (htight : cert.TightFor gaps swap assignment) (reuse : Fin gapCount → Nat)
    (hcounts : ∀ gap, (gaps gap).reward * prefixCount target (gaps gap) assignment =
      (gaps gap).reward * ((gaps gap).required + reuse gap))
    (hcost : 2 * direct = 2 * generation + ∑ gap, (gaps gap).reward * reuse gap) :
    cert.lowerNumerator gaps direct swap =
      cert.scale * (2 * generation + swap * assignment.support.card : Nat) := by
  have hr := cert.rewardUpper_eq_of_fullPrices hfull assignment htight reuse hcounts
  have hf := Word.fixed_add_support assignment
  have hcostInt : (2 * direct : Int) = 2 * generation +
      ∑ gap, ((gaps gap).reward * reuse gap : Nat) := by exact_mod_cast hcost
  have hfixedInt : ((Word.fixed assignment).card : Int) + assignment.support.card = target.length := by
    exact_mod_cast hf
  unfold Certificate.lowerNumerator
  rw [hr]
  push_cast at hcostInt ⊢
  have hh := congrArg (fun score : Int => (cert.scale : Int) * score) hcostInt
  have hhf := congrArg (fun count : Int => (cert.scale : Int) * swap * count) hfixedInt
  nlinarith

end Shuffler.Optimality.BirthPlacement.Dual
