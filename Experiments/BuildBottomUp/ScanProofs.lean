import Experiments.BuildBottomUp.Contracts

namespace BuildBottomUpExperiments.Checked

theorem forIn'_spec (xs : List α) (initial : β) (inv : β → Prop)
    (body : (a : α) → a ∈ xs → β → M (ForInStep β))
    (hinit : inv initial)
    (step : ∀ a ha b, inv b → Spec (body a ha b)
      (fun | .done out => inv out | .yield out => inv out)) :
    Spec (forIn' xs initial body) inv := by
  induction xs generalizing initial with
  | nil => exact hinit
  | cons a xs ih =>
    rw [List.forIn'_cons]
    apply (step a (by simp) initial hinit).bind
    intro out hout
    cases out with
    | done out => exact hout
    | yield out =>
      apply ih out _ hout
      intro a ha b hb
      exact step a (by simp [ha]) b hb

theorem forIn_spec (xs : List α) (initial : β) (inv : β → Prop)
    (body : α → β → M (ForInStep β)) (hinit : inv initial)
    (step : ∀ a ∈ xs, ∀ b, inv b → Spec (body a b)
      (fun | .done out => inv out | .yield out => inv out)) :
    Spec (forIn xs initial body) inv :=
  forIn'_spec xs initial inv (fun a _ b => body a b) hinit step

def UrgentChoice (state : State source target spills) (choice : Option ℕ) : Prop :=
  ∀ offset, choice = some offset → offset < target.length ∧ positionOf state offset = none

theorem urgentScan_spec (cursor : ℕ) (state : State source target spills) :
    Spec (
      forIn [cursor : target.length] none fun offset urgent => do
        if (positionOf state offset).isSome then
          return .yield urgent
        let slot ← slotAt target offset
        if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          return .yield urgent
        if let some copy := state.stack.shallowestCopyPosition slot then
          if ¬ state.stack.isDupReachable copy then
            throw (.blocked (depthOf state copy - MAX_DUP_DEPTH))
          if depthOf state copy = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
            return .yield (some offset)
        return .yield urgent) (UrgentChoice state) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply forIn_spec
  · intro offset h
    contradiction
  · intro offset hmem urgent hchoice
    have hm : offset ∈ ([cursor : target.length] : Std.Legacy.Range) :=
      Std.Legacy.Range.mem_of_mem_range' hmem
    have hlt := hm.upper
    by_cases hb : (positionOf state offset).isSome
    · simp only [hb, ↓reduceIte]
      exact hchoice
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rw [slotAt_index target ⟨offset, hlt⟩]
      simp only [bind, Except.bind]
      split
      · exact hchoice
      · split
        · split
          · exact True.intro
          · split
            · intro selected heq
              cases heq
              exact ⟨hlt, by simpa using hb⟩
            · exact hchoice
        · exact hchoice

def Chosen (state : State source target spills) (copy : Fin state.stack.length) (offset : ℕ) : Prop :=
  ∃ pos : Fin state.stack.length, pos.val = offset ∧
    state.stack[pos] = state.stack[copy] ∧ ¬ state.isFinal pos.val

theorem copyScan_spec (state : State source target spills) (copy : Fin state.stack.length)
    (initial : ℕ) (hinit : Chosen state copy initial) :
    Spec (
      forIn ((List.range state.stack.length).reverse.take (depthOf state copy.val)) initial fun candidate pos => do
        if (← slotAt state.stack candidate) = (← slotAt state.stack copy.val) ∧ ¬ state.isFinal candidate then
          return .done candidate
        return .yield pos) (Chosen state copy) := by
  apply forIn_spec _ _ _ _ hinit
  intro candidate hmem pos hpos
  have hlt : candidate < state.stack.length :=
    List.mem_range.mp (List.mem_reverse.mp (List.mem_of_mem_take hmem))
  rw [slotAt_index state.stack ⟨candidate, hlt⟩, slotAt_index state.stack copy]
  simp only [bind, Except.bind]
  split
  · rename_i h
    exact ⟨⟨candidate, hlt⟩, rfl, h⟩
  · exact hpos

end BuildBottomUpExperiments.Checked
