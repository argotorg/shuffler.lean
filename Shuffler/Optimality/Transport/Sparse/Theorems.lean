import Shuffler.Optimality.Transport.Sparse
import Shuffler.Optimality.Transport.Theorems

namespace Shuffler.Optimality.Transport

theorem sparsePotential_swap_le (residue : Fin 16) (stack target : Stack) (lower : Nat)
    (hlower : lower < stack.length - 1) (hdepth : stack.length - 1 - lower ≤ 16) (value : Value) :
    sparsePotential residue value target stack ≤
      sparsePotential residue value target (stack.swap (stack.length - 1) lower) +
        if stack[lower]'(by omega) = value then 1 else 0 := by
  have hs := Finset.sum_le_sum (s := Finset.range target.length) (fun cut _ => show
      (if cut % 16 = residue.val then surplus value target stack cut else 0) ≤
      (if cut % 16 = residue.val then
        surplus value target (stack.swap (stack.length - 1) lower) cut else 0) +
      if cut % 16 = residue.val ∧ lower ≤ cut ∧ cut < stack.length - 1 ∧
        stack[lower]'(by omega) = value then 1 else 0 from by
    by_cases hr : cut % 16 = residue.val
    · simpa only [hr, ite_true, true_and] using surplus_swap_le stack target lower hlower value cut
    · simp only [hr, ite_false, false_and, Nat.zero_add, le_refl])
  rw [Finset.sum_add_distrib] at hs
  change sparsePotential residue value target stack ≤
    sparsePotential residue value target (stack.swap (stack.length - 1) lower) +
      (Finset.range target.length).sum (fun cut =>
        if cut % 16 = residue.val ∧ lower ≤ cut ∧ cut < stack.length - 1 ∧
          stack[lower]'(by omega) = value then 1 else 0) at hs
  apply hs.trans
  apply Nat.add_le_add_left
  by_cases hv : stack[lower]'(by omega) = value
  · simp only [hv, and_true, ite_true]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    apply Finset.card_le_one.mpr
    intro left hl right hr
    have hp := (Finset.mem_filter.mp hl).2
    have hq := (Finset.mem_filter.mp hr).2
    omega
  · simp only [hv, and_false, ite_false, Finset.sum_const_zero, le_refl]

theorem sparsePotential_append_le (residue : Fin 16) (value : Value)
    (target stack : Stack) (added : Value) :
    sparsePotential residue value target stack ≤
      sparsePotential residue value target (stack ++ [added]) := by
  apply Finset.sum_le_sum
  intro cut _
  split_ifs
  · unfold surplus
    simp only [List.take_append, List.count_append]
    omega
  · exact Nat.le_refl _

@[simp] theorem sparsePotential_self (residue : Fin 16) (value : Value) (target : Stack) :
    sparsePotential residue value target target = 0 := by
  simp [sparsePotential, surplus]

theorem sparsePotential_source_le (residue : Fin 16) (value : Value) (target : Stack)
    (trace : Trace spills source current) (hpop : trace.noPop) :
    sparsePotential residue value target source ≤ sparsePotential residue value target current +
      Lineage.upwardCount value trace := by
  induction trace with
  | Lit => simp [Lineage.upwardCount]
  | @Swap previous depth hlen hlo hhi trace ih =>
      have hlower : previous.length - 1 - depth < previous.length - 1 := by omega
      have hd : previous.length - 1 - (previous.length - 1 - depth) ≤ 16 := by
        unfold MAX_SWAP_DEPTH at hhi
        omega
      have hs := sparsePotential_swap_le residue previous target _ hlower hd value
      have hp := ih hpop
      simp only [Lineage.upwardCount]
      omega
  | @Dup previous depth hlen hlo hhi trace ih =>
      have hs := sparsePotential_append_le residue value target previous previous[previous.length - depth]
      have hp := ih hpop
      simp only [Lineage.upwardCount]
      omega
  | @Push previous added hfree trace ih =>
      have hs := sparsePotential_append_le residue value target previous added
      have hp := ih hpop
      simp only [Lineage.upwardCount]
      omega
  | @Load previous id hspill trace ih =>
      have hs := sparsePotential_append_le residue value target previous (.Var id)
      have hp := ih hpop
      simp only [Lineage.upwardCount]
      omega
  | Pop _ _ => exact False.elim hpop

theorem sparsePotential_le_upwardCount (residue : Fin 16) (value : Value)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    sparsePotential residue value target source ≤ Lineage.upwardCount value trace := by
  simpa only [sparsePotential_self, Nat.zero_add] using
    sparsePotential_source_le residue value target trace hpop

theorem sparseRequiredSwaps_le_upwardCount (value : Value)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    sparseRequiredSwaps value source target ≤ Lineage.upwardCount value trace := by
  apply Finset.sup_le
  intro residue _
  exact sparsePotential_le_upwardCount residue value trace hpop

end Shuffler.Optimality.Transport
