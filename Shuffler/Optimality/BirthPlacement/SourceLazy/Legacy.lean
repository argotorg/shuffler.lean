import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightBound
import Shuffler.Optimality.BirthPlacement.SourcePotential

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation Equiv.Perm

variable {size reach height : Nat}

theorem Forced.prefix_nonempty (assignment cycle : Equiv.Perm (Fin size))
    (hc : cycle ∈ assignment.cycleFactorsFinset) (hf : Forced reach height cycle)
    (hdeadline : BirthDeadlines reach assignment) (hh : height ≤ size)
    (top : Fin size) (htop : top.val + 1 = height) :
    (SourcePrefix.cyclesIn (SourcePrefix.permutation assignment height) cycle top).Nonempty := by
  obtain ⟨before, hb, hbefore, hfar⟩ := hf.2
  let least := cycle.support.min' (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
  have hl : least ∈ cycle.support := Finset.min'_mem _ _
  have hlb : least ≤ before := Finset.min'_le _ _ hb
  let previous := assignment⁻¹ least
  have he : assignment previous = least := assignment.apply_symm_apply least
  have hp : previous ∈ cycle.support := (mem_cycleFactorsFinset_support hc previous).mp (by rwa [he])
  have hpl : least ≤ previous := Finset.min'_le _ _ hp
  have hne : previous ≠ least := by
    intro hh
    exact (mem_support.mp (mem_cycleFactorsFinset_support_le hc hl)) (by rwa [hh] at he)
  have hprev : previous.val < height := by
    by_contra hn
    have hd := hdeadline previous
    rw [he] at hd
    have hfut := hfar previous hp (by omega)
    change least.val ≤ before.val at hlb
    omega
  have hmoved : SourcePrefix.permutation assignment height previous ≠ previous := by
    intro hfix
    have hr := SourcePrefix.run_spec assignment height hh
    have hv := hr.1 previous hprev
    rw [← hr.2.2.2.1] at hv
    simp only [mul_apply, hfix, he] at hv
    exact hne (le_antisymm hv hpl)
  let child := (SourcePrefix.permutation assignment height).cycleOf previous
  have hd : child ∈ (SourcePrefix.permutation assignment height).cycleFactorsFinset :=
    cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hmoved)
  have hs : child.support ⊆ cycle.support := by
    intro index hi
    have hsame := (mem_support_cycleOf_iff.mp hi).1
    exact (SourcePrefix.component_sameCycle hc hp).mpr
      (SourcePrefix.prefix_sameCycle assignment height hsame)
  have ht : child top = top := by
    apply notMem_support.mp
    intro hi
    exact hf.1 top (hs hi) htop
  exact ⟨child, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hd, ht⟩, hs⟩⟩

theorem forcedCycles_card_le_prefix (assignment : Equiv.Perm (Fin size))
    (hdeadline : BirthDeadlines reach assignment) (hh : height ≤ size)
    (top : Fin size) (htop : top.val + 1 = height) :
    (forcedCycles reach height assignment).card ≤
      (cyclesAwayFromTop (SourcePrefix.permutation assignment height) top).card := by
  rw [(SourcePrefix.permutation_within assignment height).cyclesIn_card]
  have he : (forcedCycles reach height assignment).card =
      ∑ cycle ∈ assignment.cycleFactorsFinset, if Forced reach height cycle then 1 else 0 := by
    simp only [forcedCycles, Finset.card_filter]
  rw [he]
  apply Finset.sum_le_sum
  intro cycle hc
  by_cases hf : Forced reach height cycle
  · simp only [hf, ite_true]
    exact (Forced.prefix_nonempty assignment cycle hc hf hdeadline hh top htop).card_pos
  · simp [hf]

theorem swapBound_le_sourcePotential (assignment : Equiv.Perm (Fin size))
    (hdeadline : BirthDeadlines reach assignment) (height : Nat) (hh : height ≤ size) :
    swapBound reach height assignment ≤ sourcePotential assignment height hh := by
  by_cases hz : height = 0
  · subst height
    have he : forcedCycles reach 0 assignment = ∅ := by
      ext cycle
      simp [forcedCycles, Forced]
    simp [swapBound, he, sourcePotential]
  · let top : Fin size := ⟨height - 1, by omega⟩
    have ht : top.val + 1 = height := by dsimp [top]; omega
    have hc := forcedCycles_card_le_prefix assignment hdeadline hh top ht
    simp only [swapBound, sourcePotential, dite_eq_right hz]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hc) _

end Shuffler.Optimality.BirthPlacement.SourceLazy
