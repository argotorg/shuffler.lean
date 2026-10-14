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

-- A fold succeeds if every step succeeds and preserves the invariant.
theorem Succeeds.foldlM (inv : β → Prop) (f : β → α → Except Error β) (l : List α) (init : β)
    (h : inv init) (step : ∀ b a, inv b → Succeeds (f b a) inv) : Succeeds (l.foldlM f init) inv := by
  induction l generalizing init with
  | nil => exact h
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact (step init a h).bind fun b hb => ih b hb


--- map --------------------------------------------------------------------------------------------

namespace MappingBuilder

theorem map_ok (self : MappingBuilder source target) (s : Fin source.length) (t : Fin target.length)
    (hs : self.mappable s) (ht : self.mapping.symm t = none) :
    self.map s t = .ok { self with mapping := self.mapping.bind s t hs.2 ht } := by
  simp only [map, requires_of_true _ hs, requires_of_true _ ht, except_ok_bind]
  rfl

theorem symm_eq_none_of_not_hasSourceAssigned (self : MappingBuilder source target) (t : Fin target.length)
    (h : ¬ self.hasSourceAssigned t) : self.mapping.symm t = none := by
  simpa [hasSourceAssigned] using h

-- closestCopy only returns mappable copies.
theorem closestCopy_mappable (self : MappingBuilder source target) (targetOffset : Fin target.length)
    (location : CopyLocation) (copy : Fin source.length)
    (h : self.closestCopy targetOffset location = some copy) : self.mappable copy := by
  unfold closestCopy at h
  revert h
  generalize List.finRange source.length = l
  generalize hacc : (none : Option (Fin source.length)) = acc
  -- Invariant: the best copy found so far is mappable.
  have hinv : ∀ c, acc = some c → self.mappable c := by
    rintro c rfl
    cases hacc
  clear hacc
  induction l generalizing acc with
  | nil => exact hinv copy
  | cons i l ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    intro c hc
    split at hc
    · split at hc
      · simp_all
      · split at hc <;> simp_all
    · exact hinv c hc

-- closestSurplus only returns mappable slots.
theorem closestSurplus_mappable (self : MappingBuilder source target) (targetOffset : Fin target.length)
    (surplus : Fin source.length)
    (h : self.closestSurplus targetOffset = some surplus) : self.mappable surplus := by
  unfold closestSurplus at h
  revert h
  generalize List.finRange source.length = l
  generalize hacc : (none : Option (Fin source.length)) = acc
  -- Invariant: the best slot found so far is mappable.
  have hinv : ∀ c, acc = some c → self.mappable c := by
    rintro c rfl
    cases hacc
  clear hacc
  induction l generalizing acc with
  | nil => exact hinv surplus
  | cons i l ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    intro c hc
    split at hc
    · split at hc
      · simp_all
      · split at hc <;> simp_all
    · exact hinv c hc

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


--- Passes -----------------------------------------------------------------------------------------

-- mapInPlace only binds a slot to the target at the same offset, so the target is still free when
-- the source is: the mapping stays diagonal.
theorem mapInPlace_succeeds (mb : MappingBuilder source target) (hdiag : Diagonal mb.mapping) :
    Succeeds (mapInPlace mb) fun mb' => Diagonal mb'.mapping := by
  unfold mapInPlace
  refine Succeeds.foldlM _ _ _ _ hdiag fun mb j hdiag => ?_
  dsimp only
  split
  · next h =>
    have ht := diagonal_symm_eq_none mb.mapping hdiag (Fin.castLE (min_le_left _ _) j)
      (Fin.castLE (min_le_right _ _) j) rfl h.2.2
    rw [map_ok mb _ _ h.2 ht]
    exact diagonal_bind _ hdiag _ _ rfl h.2.2 ht
  · exact hdiag

-- The remaining passes check that the target is free and pick a mappable source.

theorem mapCopies_succeeds (mb : MappingBuilder source target) :
    Succeeds (mapCopies mb) fun _ => True := by
  unfold mapCopies
  refine Succeeds.foldlM _ _ _ _ trivial fun mb t _ => ?_
  split
  · trivial
  · next hfree =>
    split
    · next copy hcopy =>
      rw [map_ok mb _ _ (closestCopy_mappable mb t _ copy hcopy)
        (symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1)]
      trivial
    · trivial

theorem mapWildcardCopies_succeeds (strategy : WildcardSlotsStrategy) (mb : MappingBuilder source target) :
    Succeeds (mapWildcardCopies strategy mb) fun _ => True := by
  unfold mapWildcardCopies
  refine Succeeds.foldlM _ _ _ _ trivial fun mb t _ => ?_
  split
  · trivial
  · next hfree =>
    split
    · next copy hcopy =>
      rw [map_ok mb _ _ (closestCopy_mappable mb t _ copy hcopy)
        (symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1)]
      split
      · trivial
      · split <;> trivial
    · trivial

theorem keepWildcards_succeeds (mb : MappingBuilder source target) :
    Succeeds (keepWildcards mb) fun _ => True := by
  unfold keepWildcards
  refine Succeeds.foldlM _ _ _ _ trivial fun mb j _ => ?_
  dsimp only
  split
  · next h =>
    rw [map_ok mb _ _ h.2.2 (symm_eq_none_of_not_hasSourceAssigned mb _ h.2.1)]
    trivial
  · trivial

theorem absorbSurplus_succeeds (mb : MappingBuilder source target) :
    Succeeds (absorbSurplus mb) fun _ => True := by
  unfold absorbSurplus
  refine Succeeds.foldlM _ _ _ _ trivial fun mb t _ => ?_
  split
  · trivial
  · next hfree =>
    split
    · next best hbest =>
      rw [map_ok mb _ _ (closestSurplus_mappable mb t best hbest)
        (symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1)]
      trivial
    · trivial

theorem buildMapping_succeeds (source target : Stack) (dropped : List (Fin (2 ^ 8)))
    (strategy : WildcardSlotsStrategy) (hsizes : dropped.length = source.length) :
    Succeeds (buildMapping source target dropped strategy) fun _ => True := by
  unfold buildMapping
  rw [requires_of_true _ hsizes, except_ok_bind]
  refine (mapInPlace_succeeds _ diagonal_bot).bind fun mb _ => ?_
  refine (mapCopies_succeeds mb).bind fun mb _ => ?_
  refine (mapWildcardCopies_succeeds strategy mb).bind fun mb _ => ?_
  refine (keepWildcards_succeeds mb).bind fun mb _ => ?_
  exact absorbSurplus_succeeds mb

end Shuffler.BuildMapping
