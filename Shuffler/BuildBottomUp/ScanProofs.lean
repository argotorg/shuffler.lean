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
    ⦃True⦄ (
      forIn (m := Except Error) [cursor : target.length] none fun offset urgent => do
        if (state.positionOf offset).isSome then
          return .yield urgent
        let slot ← slotAt target offset
        if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          return .yield urgent
        if let some copy := state.stack.shallowestCopyPosition slot then
          if ¬ state.stack.isDupReachable copy then
            throw (.blocked ((← state.depthOf copy) - MAX_DUP_DEPTH))
          if (← state.depthOf copy) = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
            return .yield (some offset)
        return .yield urgent) ⦃UrgentChoice state; allowedErrors⦄ := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  vcgen invariants
  · fun _ _ urgent => UrgentChoice state urgent
  all_goals try simp_all [allowedErrors, UrgentChoice]
  all_goals exact range_offset_lt (by assumption)

def Chosen (state : State source target spills) (copy : Fin state.stack.length) (offset : ℕ) : Prop :=
  ∃ pos : Fin state.stack.length, pos.val = offset ∧
    state.stack[pos] = state.stack[copy] ∧ ¬ state.isFinal pos.val

@[spec] theorem copyScan_triple (state : State source target spills) (copy : Fin state.stack.length)
    (initial : ℕ) (hinit : Chosen state copy initial) :
    ⦃True⦄ (
      forIn ((List.range state.stack.length).reverse.take (state.stack.offsetToDepth copy)) initial fun candidate pos => do
        if (← slotAt state.stack candidate) = (← slotAt state.stack copy) ∧ ¬ state.isFinal candidate then
          return .done candidate
        return .yield pos) ⦃Chosen state copy; allowedErrors⦄ := by
  vcgen invariants
  · fun _ _ pos => Chosen state copy pos
  all_goals try simp_all
  all_goals first
    | exact copy_offset_lt (by assumption)
    | exact ⟨⟨_, copy_offset_lt (by assumption)⟩, rfl, (by symm; assumption), (by tauto)⟩

end Shuffler.BuildBottomUp
