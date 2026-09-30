import Shuffler.BuildBottomUp.Contracts

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

private theorem range_offset_lt
    (h : List.range' start (stop - start) = pref ++ offset :: suff) : offset < stop := by
  have hmem : offset ∈ List.range' start (stop - start) := by rw [h]; simp
  have := List.mem_range'.mp hmem
  omega

private theorem copy_offset_lt
    (h : (List.range size).reverse.take depth = pref ++ offset :: suff) : offset < size := by
  have hmem : offset ∈ (List.range size).reverse.take depth := by rw [h]; simp
  exact List.mem_range.mp (List.mem_reverse.mp (List.mem_of_mem_take hmem))

def UrgentChoice (state : State source target spills) (choice : Option ℕ) : Prop :=
  ∀ offset, choice = some offset → offset < target.length ∧ state.positionOf offset = none

@[spec] theorem urgentScan_triple (cursor : ℕ) (state : State source target spills) :
    ⦃fun s => s = state⦄ (do
      let mut urgent := none
      for offset in [cursor : target.length] do
        if (state.positionOf offset).isSome then
          continue
        let slot ← slotAt target offset
        if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          continue
        if let some copy := state.stack.shallowestCopyPosition slot then
          if ¬ state.stack.isDupReachable copy then
            throw (.blocked ((← state.depthOf copy) - MAX_DUP_DEPTH))
          if (← state.depthOf copy) = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
            urgent := some offset
      return urgent : Action source target spills (Option ℕ))
    ⦃fun urgent next => UrgentChoice state urgent ∧ next = state; allowedErrors⦄ := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  vcgen invariants
  · fun _ _ urgent next => UrgentChoice state urgent ∧ next = state
  all_goals try simp_all [allowedErrors, UrgentChoice]
  all_goals exact range_offset_lt (by assumption)

def Chosen (state : State source target spills) (copy : Fin state.stack.length) (offset : ℕ) : Prop :=
  ∃ pos : Fin state.stack.length, pos.val = offset ∧
    state.stack[pos] = state.stack[copy] ∧ ¬ state.isFinal pos.val

@[spec] theorem copyScan_triple (state : State source target spills) (copy : Fin state.stack.length)
    (initial : ℕ) (hinit : Chosen state copy initial) :
    ⦃fun s => s = state⦄ (do
      let mut pos := initial
      for candidate in (List.range state.stack.length).reverse.take (state.stack.offsetToDepth copy) do
        if (← slotAt state.stack candidate) = (← slotAt state.stack copy) ∧ ¬ state.isFinal candidate then
          pos := candidate
          break
      return pos : Action source target spills ℕ)
    ⦃fun pos next => Chosen state copy pos ∧ next = state; allowedErrors⦄ := by
  vcgen invariants
  · fun _ _ pos next => Chosen state copy pos ∧ next = state
  all_goals try simp_all
  all_goals first
    | exact copy_offset_lt (by assumption)
    | exact ⟨⟨_, copy_offset_lt (by assumption)⟩, rfl, (by symm; assumption), (by tauto)⟩

end Shuffler.BuildBottomUp
