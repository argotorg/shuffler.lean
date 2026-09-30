import Experiments.BuildBottomUp.HelperEquivalence

namespace BuildBottomUpExperiments.Checked
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- The two searches use the same order. Erase only the old proof fields.
def liftMap (f : α → β) (r : Except ShuffleErr α) : M β := (liftResult r).map f

def mapStep (f : α → β) : ForInStep α → ForInStep β
  | .done a => .done (f a)
  | .yield a => .yield (f a)

@[simp] theorem liftMap_ok (f : α → β) (a : α) : liftMap f (.ok a) = .ok (f a) := rfl
@[simp] theorem liftMap_error (f : α → β) (e : ℕ) :
    liftMap f (.error (.Blocked e)) = .error (.blocked e) := rfl

theorem forIn_as_forIn' (xs : List α) (init : β) (f : α → β → M (ForInStep β)) :
    forIn xs init f = forIn' xs init (fun a _ b => f a b) := rfl

-- A relational rule for finite loops, including early break and errors.
theorem forIn'_liftMap (xs : List α) (initial : β) (erase : β → γ)
    (old : (a : α) → a ∈ xs → β → Except ShuffleErr (ForInStep β))
    (new : (a : α) → a ∈ xs → γ → M (ForInStep γ))
    (step : ∀ a ha b, new a ha (erase b) = liftMap (mapStep erase) (old a ha b)) :
    forIn' xs (erase initial) new = liftMap erase (forIn' xs initial old) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a xs ih =>
    rw [List.forIn'_cons, List.forIn'_cons, step]
    cases h : old a (by simp) initial with
    | error err => cases err; rfl
    | ok r =>
      cases r with
      | done b => rfl
      | yield b =>
        change forIn' xs (erase b) _ = liftMap erase (forIn' xs b _)
        apply ih
        intro a ha b
        exact step a (by simp [ha]) b

abbrev Urgent (state : State source target spills) :=
  {i : Fin target.length // state.mapping.symm i = none}

def oldUrgent (cursor : ℕ) (state : State source target spills) :
    Except ShuffleErr (Option (Urgent state)) :=
  forIn' [cursor : target.length] none fun offset hmem urgent => do
    if hbound : (state.mapping.symm ⟨offset, hmem.upper⟩).isSome then
      return .yield urgent
    else
      let slot := target[offset]'hmem.upper
      if hfree : slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
        return .yield urgent
      if let some copy := state.stack.shallowest_copy_position slot then
        if ¬ state.stack.is_dup_reachable copy then
          throw (.Blocked (state.stack.depth_of copy - MAX_DUP_DEPTH))
        if state.stack.depth_of copy = MAX_DUP_DEPTH ∧ copy.val != cursor ∧ urgent.isNone then
          return .yield (some ⟨⟨offset, hmem.upper⟩, by simpa using hbound⟩)
      return .yield urgent

def newUrgent (cursor : ℕ) (state : State source target spills) : M (Option ℕ) :=
  forIn [cursor : target.length] none fun offset urgent => do
    if (positionOf state offset).isSome then
      return .yield urgent
    let slot ← slotAt target offset
    if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
      return .yield urgent
    if let some copy := state.stack.shallowest_copy_position slot then
      if ¬ state.stack.is_dup_reachable copy then
        throw (.blocked (depthOf state copy - MAX_DUP_DEPTH))
      if depthOf state copy = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
        return .yield (some offset)
    return .yield urgent

@[simp] theorem slotAt_eq (stack : Stack) (i : Fin stack.length) :
    slotAt stack i.val = .ok stack[i] := by
  simp [slotAt, index, i.isLt, bind, Except.bind, pure, Except.pure]

theorem urgent_eq (cursor : ℕ) (state : State source target spills) :
    newUrgent cursor state = liftMap (Option.map (fun i : Urgent state => i.val.val)) (oldUrgent cursor state) := by
  unfold newUrgent oldUrgent
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  rw [forIn_as_forIn']
  apply forIn'_liftMap (initial := (none : Option (Urgent state)))
    (erase := Option.map (fun i : Urgent state => i.val.val))
  intro offset hmem urgent
  have hm : offset ∈ ([cursor : target.length] : Std.Legacy.Range) :=
    Std.Legacy.Range.mem_of_mem_range' hmem
  have hlt : offset < target.length := hm.upper
  simp only [positionOf, hlt, ↓reduceDIte, Option.isSome_map]
  rw [show slotAt target offset = .ok target[offset] from slotAt_eq target ⟨offset, hlt⟩]
  simp only [bind, Except.bind]
  split
  · simp_all [liftMap, liftResult, Except.map, Except.mapError, mapStep, pure, Except.pure]
  · split
    · simp_all [liftMap, liftResult, Except.map, Except.mapError, mapStep, pure, Except.pure]
    · split
      · split
        · simp_all [liftMap, liftResult, Except.map, Except.mapError, mapStep, depthOf,
            Stack.depth_of, throw, throwThe]
          rfl
        · simp only [bne_iff_ne, Option.isNone_map, depthOf, Stack.depth_of]
          split <;> simp_all [liftMap, liftResult, Except.map, Except.mapError, mapStep,
            pure, Except.pure]
          split_ifs <;> simp_all
      · simp_all [liftMap, liftResult, Except.map, Except.mapError, mapStep, pure, Except.pure]

def oldCopy (state : State source target spills) (copy : Fin state.stack.length)
    (initial : state.MovableCopy copy) : Except ShuffleErr (state.MovableCopy copy) :=
  forIn ((List.finRange state.stack.length).reverse.take (state.stack.depth_of copy).val)
    initial fun candidate pos =>
      if h : state.stack[candidate] = state.stack[copy] ∧ ¬ state.is_final candidate.val then
        pure (.done ⟨candidate, h.1, h.2⟩)
      else pure (.yield pos)

def newCopy (state : State source target spills) (copy initial : ℕ) : M ℕ :=
  forIn ((List.range state.stack.length).reverse.take (depthOf state copy)) initial fun candidate pos => do
    if (← slotAt state.stack candidate) = (← slotAt state.stack copy) ∧ ¬ state.is_final candidate then
      return .done candidate
    return .yield pos

theorem copy_eq (state : State source target spills) (copy : Fin state.stack.length)
    (initial : state.MovableCopy copy) :
    newCopy state copy.val initial.val = liftMap (fun p : state.MovableCopy copy => p.val)
      (oldCopy state copy initial) := by
  have hlist : ((List.finRange state.stack.length).reverse.take (state.stack.depth_of copy).val).map Fin.val =
      (List.range state.stack.length).reverse.take (depthOf state copy) := by
    have hvals : (List.finRange state.stack.length).map Fin.val = List.range state.stack.length := by
      apply List.ext_getElem <;> simp
    simp [List.map_take, List.map_reverse, hvals, depthOf, Stack.depth_of]
  unfold newCopy oldCopy
  rw [← hlist, List.forIn_map, forIn_as_forIn']
  apply forIn'_liftMap (initial := initial) (erase := fun p : state.MovableCopy copy => p.val)
  intro candidate hmem pos
  simp only [slotAt_eq, bind, Except.bind]
  split <;> simp_all [liftMap, liftResult, Except.map, Except.mapError, mapStep, pure, Except.pure]

end BuildBottomUpExperiments.Checked
