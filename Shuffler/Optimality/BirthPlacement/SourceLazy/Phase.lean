import Shuffler.Optimality.BirthPlacement.SourceLazy.State
import Shuffler.Optimality.BirthPlacement.SourceLazy.Prefix
import Shuffler.Optimality.BirthPlacement.SourceLazy.Count
import Shuffler.Optimality.BirthPlacement.SourceLazy.EraseCycles

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation Shuffler.Placement

variable {spills : SpillSet} {source target : Stack}
  {plan : SourcePlan spills source target}

structure Phase (top : Fin target.length) (state : State plan (top.val + 1)) where
  before : State plan top.val
  built : BuiltTrace spills
    (prefixValues target (plan.assignment * before.remaining⁻¹) (top.val + 1)) state.values 0
  count : built.trace.swapCount + swapBound 16 source.length before.remaining =
    swapBound 16 source.length state.remaining

def phaseOfMovement (top : Fin target.length) (state : State plan (top.val + 1))
    (hsource : source.length ≤ top.val)
    (movement : Equiv.Perm (Fin target.length))
    (hfixed : ∀ index, top.val < index.val → movement index = index)
    (hreach : ∀ index ∈ movement.support, top.val ≤ index.val + 16)
    (habove : ∀ index : Fin target.length, top.val ≤ index.val →
      (movement⁻¹ * state.remaining) index = index)
    (hdeadline : BirthDeadlines 16 (movement⁻¹ * state.remaining))
    (hcount : swapCount movement top + swapBound 16 source.length (movement⁻¹ * state.remaining) =
      swapBound 16 source.length state.remaining) : Phase top state := by
  let before := state.rewind top hsource movement hreach habove hdeadline
  let values := prefixValues target (plan.assignment * before.remaining⁻¹) (top.val + 1)
  have hlen : values.length = top.val + 1 := by
    simp only [values, prefixValues_length]
    omega
  let result := permutePrefix spills target values (plan.assignment * before.remaining⁻¹) movement
    (by rw [hlen]; omega) (by rw [hlen])
    (by intro index hi; apply hfixed; rw [hlen] at hi; omega)
    (by intro index hi; rw [hlen]; have := hreach index hi; omega)
    (by rw [hlen]; omega)
  have he : plan.assignment * before.remaining⁻¹ * movement⁻¹ =
      plan.assignment * state.remaining⁻¹ := by
    simp [before, State.rewind, cachedPermutation_eq, mul_inv_rev, mul_assoc]
  have hend : prefixValues target (plan.assignment * before.remaining⁻¹ * movement⁻¹) values.length =
      state.values := by rw [he, hlen]
  refine ⟨before, result.val.cast rfl hend rfl, ?_⟩
  rw [built_cast_swapCount, result.property]
  have ht : (⟨values.length - 1, by rw [hlen]; omega⟩ : Fin target.length) = top := by
    apply Fin.ext
    simp only [hlen, Nat.add_sub_cancel]
  rw [ht]
  simpa only [before, State.rewind, cachedPermutation_eq] using hcount

def phase (top : Fin target.length) (state : State plan (top.val + 1))
    (hsource : source.length ≤ top.val) : Phase top state :=
  if he : state.remaining top = top then
    phaseOfMovement top state hsource 1 (by simp) (by simp)
      (by
        intro index hi
        simp only [inv_one, one_mul]
        by_cases ht : index = top
        · subst index; exact he
        · exact state.above index (by have := Fin.val_ne_of_ne ht; omega))
      (by simpa using state.deadlines) (by simp)
  else if hr : Ready 16 source.length state.remaining top then
    phaseOfMovement top state hsource (state.remaining.cycleOf top)
      (by
        intro index hi
        apply Equiv.Perm.notMem_support.mp
        intro hm
        have hs := Equiv.Perm.support_cycleOf_le state.remaining top hm
        exact (Equiv.Perm.mem_support.mp hs) (state.above index (by omega)))
      hr.2
      (by
        intro index hi
        change eraseCycle state.remaining top index = index
        by_cases ht : index = top
        · subst index
          apply eraseCycle_fixes
          exact Equiv.Perm.mem_support_cycleOf_iff.mpr
            ⟨Equiv.Perm.SameCycle.refl _ _, Equiv.Perm.mem_support.mpr he⟩
        · exact eraseCycle_fixed state.remaining top index
            (state.above index (by have := Fin.val_ne_of_ne ht; omega)))
      (eraseCycle_deadlines state.remaining top state.deadlines)
      (by
        change swapCount (state.remaining.cycleOf top) top +
          swapBound 16 source.length (eraseCycle state.remaining top) = _
        rw [swapCount_cycleOf, swapBound, forcedCycles_eraseCycle state.remaining top hsource hr]
        have hk := eraseCycle_rank state.remaining top
        unfold swapBound
        omega)
  else
    phaseOfMovement top state hsource (Equiv.swap top (state.remaining top))
      (by
        intro index hi
        apply Equiv.swap_apply_of_ne_of_ne
        · intro hh; subst index; omega
        · intro hh
          have hf := state.above index (by omega)
          have ht := state.remaining.injective (hf.trans hh)
          have := congrArg Fin.val ht
          omega)
      (by
        intro index hi
        rw [Equiv.Perm.support_swap (Ne.symm he)] at hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · omega
        · exact state.deadlines top)
      (by
        simpa only [Equiv.swap_inv, eraseTop] using eraseTop_fixed state.remaining top
          (fun index hi => state.above index (by omega)))
      (by
        simpa only [Equiv.swap_inv, eraseTop] using eraseTop_deadlines state.remaining top state.deadlines
          (fun index hi => state.above index (by omega)))
      (by
        simp only [Equiv.swap_inv]
        change swapCount (Equiv.swap top (state.remaining top)) top +
          swapBound 16 source.length (eraseTop state.remaining top) = _
        rw [swapCount_swap top _ (Ne.symm he), swapBound,
          forcedCycles_eraseTop_card state.remaining top hsource
            (fun index hi => state.above index (by omega)) state.deadlines he hr]
        have hk := eraseTop_rank state.remaining top he
        unfold swapBound
        omega)

end Shuffler.Optimality.BirthPlacement.SourceLazy
