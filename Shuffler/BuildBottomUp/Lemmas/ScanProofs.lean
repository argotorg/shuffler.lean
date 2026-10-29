module

public import Shuffler.Emission.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Std.WP.Triple.SpecLemmas

@[expose] public section

open Std.WP

set_option experimental.vcgen true

namespace Shuffler.Emission

theorem range_offset_lt
    (h : List.range' start (stop - start) = pref ++ offset :: suff) : offset < stop := by
  have hmem : offset ∈ List.range' start (stop - start) := by rw [h]; simp
  have := List.mem_range'.mp hmem
  omega

theorem copy_offset_lt
    (h : (List.range size).reverse.take depth = pref ++ offset :: suff) : offset < size := by
  have hmem : offset ∈ (List.range size).reverse.take depth := by rw [h]; simp
  exact List.mem_range.mp (List.mem_reverse.mp (List.mem_of_mem_take hmem))

def UrgentChoice (state : State source target spills) (choice : Option ℕ) : Prop :=
  ∀ offset, choice = some offset → ∃ h : offset < target.length, state.mapping.positionOf ⟨offset, h⟩ = none

@[spec] theorem urgentScan_triple (cursor : ℕ) (state : State source target spills) :
    ⦃True⦄ (do
      let mut returned : Option (Result source target spills) := none
      let mut urgent := none
      for offset in [cursor : target.length] do
        returned := none
        if (state.mapping.positionOf (← index target.length offset)).isSome then
          continue
        let slot ← slotAt target offset
        if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          continue
        if let some copy := state.stack.shallowestCopyPosition slot then
          if ¬ state.stack.isDupReachable copy then
            returned := some (← state.blockDupUnreachable copy)
            break
          if (state.depthOf copy) = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
            urgent := some offset
      return (returned, urgent) : Except ShuffleErr (Option (Result source target spills) × Option ℕ))
    ⦃fun result => (∀ r, result.1 = some r → r.blocked.isSome = true) ∧ UrgentChoice state result.2; allowedErrors⦄ := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  vcgen invariants
  · fun _ _ result => (∀ r, result.1 = some r → r.blocked.isSome = true) ∧ UrgentChoice state result.2
  all_goals try simp_all [UrgentChoice]
  all_goals try subst_vars
  all_goals try simp_all
  all_goals first
    | exact range_offset_lt (by assumption)

def Chosen (state : State source target spills) (copy : Fin state.stack.length) (offset : ℕ) : Prop :=
  ∃ pos : Fin state.stack.length, pos.val = offset ∧
    state.stack[pos] = state.stack[copy] ∧ ¬ state.isFinal pos

@[spec] theorem copyScan_triple (state : State source target spills) (copy : Fin state.stack.length)
    (initial : ℕ) (hinit : Chosen state copy initial) :
    ⦃True⦄ (do
      let mut pos := initial
      for candidate in (List.range state.stack.length).reverse.take (state.depthOf copy) do
        if (← slotAt state.stack candidate) = (← slotAt state.stack copy) ∧ ¬ state.isFinal (← index state.stack.length candidate) then
          pos := candidate
          break
      return pos : Except ShuffleErr ℕ)
    ⦃fun pos => Chosen state copy pos; allowedErrors⦄ := by
  vcgen invariants
  · fun _ _ pos => Chosen state copy pos
  all_goals try simp_all
  all_goals first
    | exact copy_offset_lt (by assumption)
    | exact ⟨⟨_, copy_offset_lt (by assumption)⟩, rfl, (by symm; assumption), (by subst_vars; tauto)⟩

end Shuffler.Emission
