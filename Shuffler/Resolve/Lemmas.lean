import Shuffler.Resolve.Defs
import Std.Tactic.Do

open Std.Do
set_option mvcgen.warning false

namespace Shuffler.Planner

variable {source target : Stack}

-- Inverse bindings give a bound source position.
theorem retained_of_positionOf {mapping : Mapping n m} {destination : Fin m} {offset : Fin n}
    (h : mapping.positionOf destination = some offset) :
    (mapping.destinationOf offset).isSome := by
  have hb : mapping offset = some destination := mapping.eq_some_iff.mp h
  simp [Mapping.destinationOf, hb]

-- A bound source position can always be classified.
@[local spec] theorem classify_spec (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (offset : Fin source.length) :
    ⦃⌜(mapping.destinationOf offset).isSome = true⌝⦄ classify state mapping droppedNow offset
    ⦃⇓ cls => ⌜classify state mapping droppedNow offset = .ok cls⌝⦄ := by
  change (mapping.destinationOf offset).isSome = true → _
  intro h
  simp only [classify, requires_of_true _ h, except_ok_bind]
  split_ifs <;> rfl

-- Class four is only used for a variable that has not already been spilled.
theorem classify_four (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (offset : Fin source.length)
    (h : classify state mapping droppedNow offset = .ok (some 4)) :
    ∃ id, source[offset] = .Var id ∧ id ∉ state.spills := by
  simp only [classify, requires, pure, Except.pure, bind, Except.bind] at h
  split_ifs at h <;> simp_all only [Except.ok.injEq, reduceCtorEq]
  all_goals cases hs : source[offset] <;> simp_all [Value.isVariable, SpillSet.is_spilled]
  all_goals split_ifs at h <;> simp_all

-- A fresh variable can be inserted without an assertion error.
@[local spec] theorem spill_add_spec (spills : SpillSet) (slot : Value) :
    ⦃⌜∃ id, slot = .Var id ∧ id ∉ spills⌝⦄ spills.add slot
    ⦃⇓ added => ⌜∃ id, slot = .Var id ∧ added = insert id spills⌝⦄ := by
  change (∃ id, slot = .Var id ∧ id ∉ spills) → _
  intro h
  obtain ⟨id, rfl, hfresh⟩ := h
  simp only [SpillSet.add, requires_of_true _ hfresh, except_ok_bind]
  exact ⟨id, rfl, rfl⟩

-- Each candidate came from a retained source slot.
def RetainedCandidates (mapping : Mapping n m) (candidates : List (Fin n)) : Prop :=
  ∀ offset ∈ candidates, (mapping.destinationOf offset).isSome

-- The selected slot has not yet been dropped, and its class is the recorded class.
def Selected (state : State source target) (mapping : Mapping source.length target.length)
    (droppedNow : Vector Byte source.length) (candidates : List (Fin source.length))
    (found : Option (Fin source.length) × ℕ) : Prop :=
  ∀ offset, found.1 = some offset → offset ∈ candidates ∧ droppedNow[offset] = 0 ∧
    classify state mapping droppedNow offset = .ok (some found.2)

theorem RetainedCandidates.start (mapping : Mapping n m) :
    RetainedCandidates mapping [] := by simp [RetainedCandidates]

theorem RetainedCandidates.append {mapping : Mapping n m} {candidates : List (Fin n)}
    (h : RetainedCandidates mapping candidates) {destination : Fin m} {offset : Fin n}
    (hpos : mapping.positionOf destination = some offset) :
    RetainedCandidates mapping (candidates ++ [offset]) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact h i hi
  · simpa using List.mem_singleton.mp hi ▸ retained_of_positionOf hpos

theorem RetainedCandidates.current {mapping : Mapping n m}
    {pref suff : List (Fin n)} {offset : Fin n}
    (h : RetainedCandidates mapping (pref ++ offset :: suff)) :
    (mapping.destinationOf offset).isSome := h offset (by simp)

theorem Selected.start (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (candidates : List (Fin source.length)) :
    Selected state mapping droppedNow candidates (none, 0) := by simp [Selected]

theorem Selected.select (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (candidates : List (Fin source.length)) (offset : Fin source.length) {cls : Option ℕ}
    (hmem : offset ∈ candidates) (hdrop : droppedNow[offset] = 0)
    (hcls : classify state mapping droppedNow offset = .ok cls) (hsome : cls.isSome) :
    Selected state mapping droppedNow candidates (some offset, cls.get hsome) := by
  intro i hi
  have heq : offset = i := Option.some.inj hi
  subst i
  exact ⟨hmem, hdrop, hcls.trans (congrArg Except.ok (Option.some_get hsome).symm)⟩

theorem Selected.get {state : State source target}
    {mapping : Mapping source.length target.length} {droppedNow : Vector Byte source.length}
    {candidates : List (Fin source.length)} {found : Option (Fin source.length) × ℕ}
    (h : Selected state mapping droppedNow candidates found) (hsome : found.1.isSome) :
    found.1.get hsome ∈ candidates ∧ droppedNow[found.1.get hsome] = 0 ∧
      classify state mapping droppedNow (found.1.get hsome) = .ok (some found.2) :=
  h _ (Option.some_get hsome).symm

theorem Selected.four {state : State source target}
    {mapping : Mapping source.length target.length} {droppedNow : Vector Byte source.length}
    {candidates : List (Fin source.length)} {found : Option (Fin source.length) × ℕ}
    (h : Selected state mapping droppedNow candidates found) (hsome : found.1.isSome)
    (hfour : found.2 = 4) :
    ∃ id, source[found.1.get hsome] = .Var id ∧ id ∉ state.spills :=
  classify_four state mapping droppedNow _ (by simpa only [hfour] using (h.get hsome).2.2)

@[local spec] theorem resolve_requires_spec (condition : Prop) [Decidable condition] (reason : String) :
    ⦃⌜condition⌝⦄ requires condition reason ⦃⇓ _ => ⌜True⌝⦄ := by
  change condition → _
  intro h
  rw [requires_of_true _ h]
  trivial

-- Keep the first loop proof shared so later proofs reuse Lean's generated matcher lemmas.
theorem resolve_success_triple (init : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) :
    ⦃⌜True⌝⦄ resolve init mapping blocked current ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen [resolve]
  case inv1 => exact PostCond.noThrow (fun (_, candidates) => ⌜RetainedCandidates mapping candidates⌝)
  case inv2 => exact PostCond.noThrow (fun _ => ⌜True⌝)
  case inv3 =>
    rename_i candidates _ _ _ _ _ _ _ state droppedNow _ _
    exact PostCond.noThrow (fun (_, found) => ⌜Selected state mapping droppedNow candidates found⌝)
  all_goals try simp_all only [not_not]
  all_goals try first
    | trivial
    | assumption
    | exact RetainedCandidates.start _
    | exact RetainedCandidates.append (by assumption) (by assumption)
    | exact Selected.start _ _ _ _
    | exact RetainedCandidates.current (by assumption)
    | exact Selected.select _ _ _ _ _ (by simp) (by assumption) (by assumption) _
    | exact Selected.four (by assumption) _ (by assumption)

end Shuffler.Planner
