import Shuffler.BuildMapping.Defs

namespace Shuffler.BuildMapping

variable {source target : Stack}

--- Contracts --------------------------------------------------------------------------------------

-- The result is `.ok` and satisfies `post`. Unlike BuildBottomUp's `Spec`, no error is allowed:
-- buildMapping never blocks.
def Succeeds (result : Except Error α) (post : α → Prop) : Prop :=
  match result with
  | .ok value => post value
  | .error _ => False

@[simp] theorem succeeds_ok (value : α) (post : α → Prop) :
    Succeeds (.ok value) post ↔ post value := Iff.rfl

@[simp] theorem succeeds_pure (value : α) (post : α → Prop) :
    Succeeds (pure value : Except Error α) post ↔ post value := Iff.rfl

theorem Succeeds.exists {result : Except Error α} {post : α → Prop} (h : Succeeds result post) :
    ∃ value, result = .ok value ∧ post value := by
  cases result with
  | ok value => exact ⟨value, rfl, h⟩
  | error _ => exact h.elim

theorem Succeeds.bind {result : Except Error α} {pre : α → Prop} {next : α → Except Error β}
    {post : β → Prop} (h : Succeeds result pre) (step : ∀ value, pre value → Succeeds (next value) post) :
    Succeeds (result >>= next) post := by
  cases result with
  | ok value => exact step value h
  | error _ => exact h.elim

theorem Succeeds.mono {result : Except Error α} {pre post : α → Prop}
    (h : Succeeds result pre) (step : ∀ value, pre value → post value) : Succeeds result post := by
  cases result with
  | ok value => exact step value h
  | error _ => exact h.elim

-- A `for` loop succeeds if every iteration succeeds and preserves the invariant.
theorem Succeeds.forIn (inv : β → Prop) (l : List α) (init : β) (f : α → β → Except Error (ForInStep β))
    (h : inv init) (step : ∀ a b, inv b → Succeeds (f a b) fun r => inv r.value) :
    Succeeds (forIn l init f) inv := by
  induction l generalizing init with
  | nil => exact h
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (step a init h).bind fun r hr => ?_
    cases r with
    | done b => exact hr
    | yield b => exact ih b hr

--- map --------------------------------------------------------------------------------------------

namespace MappingBuilder

-- `mappable` as a proposition, without the bound check: `dropped[s]?` is `none` out of bounds.
def IsMappable (self : MappingBuilder source target) (s : Fin source.length) : Prop :=
  self.dropped[s.val]? = some 0 ∧ self.mapping s = none

instance (self : MappingBuilder source target) (s : Fin source.length) :
    Decidable (self.IsMappable s) := by
  unfold IsMappable; infer_instance

-- With one dropped entry per source slot, `mappable` succeeds and decides `IsMappable`.
theorem mappable_ok (self : MappingBuilder source target) (s : Fin source.length)
    (h : self.dropped.length = source.length) : self.mappable s = .ok (decide (self.IsMappable s)) := by
  have hlt : s.val < self.dropped.length := by rw [h]; exact s.isLt
  simp only [mappable, requires_of_true _ hlt, except_ok_bind, IsMappable,
    List.getElem?_eq_getElem hlt, Option.some.injEq]
  rfl

-- `mappable` returns `true` on a mappable slot; its bound check holds since `dropped[s]?` is `some`.
theorem mappable_of_isMappable (self : MappingBuilder source target) (s : Fin source.length)
    (hs : self.IsMappable s) : self.mappable s = .ok true := by
  obtain ⟨hlt, h0⟩ := List.getElem?_eq_some_iff.mp hs.1
  simp only [mappable, requires_of_true _ hlt, except_ok_bind, h0, hs.2]
  rfl

theorem map_ok (self : MappingBuilder source target) (s : Fin source.length) (t : Fin target.length)
    (hs : self.IsMappable s) (ht : self.mapping.symm t = none) :
    self.map s t = .ok { self with mapping := self.mapping.bind s t hs.2 ht } := by
  simp only [map, mappable_of_isMappable self s hs, except_ok_bind, requires_of_true _ rfl,
    requires_of_true _ hs.2, requires_of_true _ ht]
  rfl

theorem symm_eq_none_of_not_hasSourceAssigned (self : MappingBuilder source target) (t : Fin target.length)
    (h : ¬ self.hasSourceAssigned t) : self.mapping.symm t = none := by
  simpa [hasSourceAssigned] using h

-- closestCopy succeeds and only returns mappable copies.
theorem closestCopy_succeeds (self : MappingBuilder source target) (targetOffset : Fin target.length)
    (location : CopyLocation) (h : self.dropped.length = source.length) :
    Succeeds (self.closestCopy targetOffset location) fun r => ∀ c, r = some c → self.IsMappable c := by
  unfold closestCopy
  -- Invariant: the best copy found so far is mappable.
  refine (Succeeds.forIn _ _ _ _ (by simp) fun i best hinv => ?_).bind fun r hr => hr
  simp only [mappable_ok self i h, except_ok_bind]
  split
  · next hcond =>
    have hi : self.IsMappable i := of_decide_eq_true hcond.2.1
    split
    · simp [hi]
    · split <;> simp_all
  · exact hinv

-- closestSurplus succeeds and only returns mappable slots.
theorem closestSurplus_succeeds (self : MappingBuilder source target) (targetOffset : Fin target.length)
    (h : self.dropped.length = source.length) :
    Succeeds (self.closestSurplus targetOffset) fun r => ∀ c, r = some c → self.IsMappable c := by
  unfold closestSurplus
  -- Invariant: the best slot found so far is mappable.
  refine (Succeeds.forIn _ _ _ _ (by simp) fun o best hinv => ?_).bind fun r hr => hr
  simp only [mappable_ok self o h, except_ok_bind]
  split
  · next hcond =>
    have ho : self.IsMappable o := of_decide_eq_true hcond
    split
    · simp [ho]
    · split <;> simp_all
  · exact hinv

end MappingBuilder

open MappingBuilder


--- Diagonal mappings ------------------------------------------------------------------------------

-- Every binding maps a source slot to the target slot with the same offset.
def Diagonal {a b : ℕ} (m : Mapping a b) : Prop :=
  ∀ s t, m s = some t → s.val = t.val

theorem diagonal_bot {a b : ℕ} : Diagonal (⊥ : Mapping a b) := by
  intro s t h
  simp at h

-- In a diagonal mapping, a target is free when the source at the same offset is unbound.
theorem diagonal_symm_eq_none {a b : ℕ} (m : Mapping a b) (hdiag : Diagonal m)
    (s : Fin a) (t : Fin b) (hst : s.val = t.val) (hs : m s = none) : m.symm t = none := by
  cases h : m.symm t with
  | none => rfl
  | some s' =>
    have hs't : m s' = some t := m.eq_some_iff.mp h
    have : s' = s := Fin.ext ((hdiag s' t hs't).trans hst.symm)
    subst this
    simp [hs] at hs't

-- Binding a slot to the target at the same offset keeps a mapping diagonal.
theorem diagonal_bind {a b : ℕ} (m : Mapping a b) (hdiag : Diagonal m)
    (s : Fin a) (t : Fin b) (hst : s.val = t.val) (hs : m s = none) (ht : m.symm t = none) :
    Diagonal (m.bind s t hs ht) := by
  intro i k h
  by_cases hi : i = s
  · subst hi
    simp at h
    subst h
    exact hst
  · rw [Mapping.bind_apply_of_ne m s t hs ht i hi] at h
    exact hdiag i k h


--- buildMapping -----------------------------------------------------------------------------------

-- Each loop of buildMapping is proved with `Succeeds.forIn`. No loop changes `dropped`, so
-- `dropped.length = source.length` is part of every loop invariant. Every `map` call is on a free
-- target and a mappable source, so none of its `requires` fails.
theorem buildMapping_succeeds (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) (hsizes : dropped.length = source.length) :
    Succeeds (buildMapping source target dropped strategy) fun _ => True := by
  unfold buildMapping
  rw [requires_of_true _ hsizes, except_ok_bind]
  dsimp only

  -- slots already in place: the loop only binds a slot to the target at the same offset, so the
  -- target is still free when the source is, and the mapping stays diagonal.
  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    Diagonal mb.mapping ∧ mb.dropped.length = source.length) _ _ _ ⟨diagonal_bot, hsizes⟩ ?_).bind
    fun mb ⟨_, h⟩ => ?_
  · intro j mb ⟨hdiag, h⟩
    simp only [mappable_ok mb _ h, except_ok_bind]
    split
    · next hcond =>
      have hs : mb.IsMappable (Fin.castLE (min_le_left _ _) j) := of_decide_eq_true hcond.2
      have ht := diagonal_symm_eq_none mb.mapping hdiag (Fin.castLE (min_le_left _ _) j)
        (Fin.castLE (min_le_right _ _) j) rfl hs.2
      rw [map_ok mb _ _ hs ht]
      exact ⟨diagonal_bind _ hdiag _ _ rfl hs.2 ht, h⟩
    · exact ⟨hdiag, h⟩

  -- the closest unused copy outside wildcard slots
  refine (Succeeds.forIn (fun mb : MappingBuilder source target => mb.dropped.length = source.length)
    _ _ _ h ?_).bind fun mb h => ?_
  · intro t mb h
    split
    · exact h
    · next hfree =>
      refine (closestCopy_succeeds mb t _ h).bind fun r hr => ?_
      split
      · next copy =>
        rw [map_ok mb _ _ (hr copy rfl) (symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1)]
        exact h
      · exact h

  -- copies in wildcard slots
  refine (Succeeds.forIn (fun mb : MappingBuilder source target => mb.dropped.length = source.length)
    _ _ _ h ?_).bind fun mb h => ?_
  · intro t mb h
    split
    · exact h
    · next hfree =>
      refine (closestCopy_succeeds mb t _ h).bind fun r hr => ?_
      split
      · next copy =>
        rw [map_ok mb _ _ (hr copy rfl) (symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1)]
        split
        · exact h
        · split
          · exact h
          · exact h
      · exact h

  -- wildcards keep whatever sits there
  refine (Succeeds.forIn (fun mb : MappingBuilder source target => mb.dropped.length = source.length)
    _ _ _ h ?_).bind fun mb h => ?_
  · intro j mb h
    simp only [mappable_ok mb _ h, except_ok_bind]
    split
    · next hcond =>
      rw [map_ok mb _ _ (of_decide_eq_true hcond.2.2)
        (symm_eq_none_of_not_hasSourceAssigned mb _ hcond.2.1)]
      exact h
    · exact h

  -- the remaining wildcards absorb the closest surplus slot
  refine (Succeeds.forIn (fun mb : MappingBuilder source target => mb.dropped.length = source.length)
    _ _ _ h ?_).bind fun _ _ => trivial
  · intro t mb h
    split
    · exact h
    · next hfree =>
      refine (closestSurplus_succeeds mb t h).bind fun r hr => ?_
      split
      · next best =>
        rw [map_ok mb _ _ (hr best rfl) (symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1)]
        exact h
      · exact h

end Shuffler.BuildMapping
