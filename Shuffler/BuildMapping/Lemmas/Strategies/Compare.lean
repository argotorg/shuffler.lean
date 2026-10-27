import Shuffler.BuildMapping.Lemmas.Basic

namespace Shuffler.BuildMapping.Strategies

variable {source target : Stack}

-- Both calls succeed and their results satisfy the relation.
def Both (left : Except Error α) (right : Except Error β) (post : α → β → Prop) : Prop :=
  Succeeds left fun a => Succeeds right (post a)

theorem Both.bind {left : Except Error α} {right : Except Error β} {pre : α → β → Prop}
    {nextLeft : α → Except Error γ} {nextRight : β → Except Error δ} {post : γ → δ → Prop}
    (h : Both left right pre)
    (step : ∀ a b, pre a b → Both (nextLeft a) (nextRight b) post) :
    Both (left >>= nextLeft) (right >>= nextRight) post := by
  obtain ⟨a, ha, hb⟩ := h.exists
  obtain ⟨b, hb, hab⟩ := hb.exists
  simp only [ha, hb, except_ok_bind]
  exact step a b hab

theorem Both.forIn (inv : β → γ → Prop) (l : List α) (left : β) (right : γ)
    (f : α → β → Except Error (ForInStep β)) (g : α → γ → Except Error (ForInStep γ))
    (h : inv left right)
    (step : ∀ a b c, inv b c → Both (f a b) (g a c) fun x y =>
      x = .yield x.value ∧ y = .yield y.value ∧ inv x.value y.value) :
    Both (forIn l left f) (forIn l right g) inv := by
  induction l generalizing left right with
  | nil => exact h
  | cons a l ih =>
    obtain ⟨x, hx, hy⟩ := (step a left right h).exists
    obtain ⟨y, hy, hxy⟩ := hy.exists
    cases x with
    | done b => cases hxy.1
    | yield b =>
      cases y with
      | done c => cases hxy.2.1
      | yield c =>
        simp only [List.forIn_cons, hx, hy, except_ok_bind]
        exact ih b c hxy.2.2

-- A witness records a target that Leave keeps free and Take binds.
def Different (left right : MappingBuilder source target) : Prop :=
  ∃ t s, ¬ target[t].is_junk ∧ ¬ target[t].isFunctionReturnLabel ∧
    left.mapping.symm t = none ∧ right.mapping.symm t = some s

-- Before the first choice the states agree. After it, both flags and a witness persist.
def Compared (left right : MappingBuilder source target) : Prop :=
  left.dropped.length = source.length ∧ right.dropped.length = source.length ∧
    ((left = right ∧ left.sawWildcardCopy = false) ∨
      (left.sawWildcardCopy = true ∧ right.sawWildcardCopy = true ∧ Different left right))

private theorem bind_keeps_inverse (mb : MappingBuilder source target)
    (s : Fin source.length) (t : Fin target.length)
    (hs : mb.mapping s = none) (ht : mb.mapping.symm t = none)
    (u : Fin target.length) (v : Fin source.length) (hbound : mb.mapping.symm u = some v) :
    (mb.mapping.bind s t hs ht).symm u = some v := by
  have hne : u ≠ t := by
    intro heq
    subst u
    rw [ht] at hbound
    cases hbound
  exact (Mapping.bind_symm_apply_of_ne mb.mapping s t hs ht u hne).trans hbound

open MappingBuilder

-- Each step preserves existing bindings; Leave also preserves every target that is not a return label.
theorem copyStep_preserves (strategy : WildcardSlotsStrategy) (t : Fin target.length)
    (mb : MappingBuilder source target) (hsize : mb.dropped.length = source.length) :
    Succeeds (copyStep strategy t mb) fun r =>
      r = .yield r.value ∧ r.value.dropped.length = source.length ∧
      (mb.sawWildcardCopy = true → r.value.sawWildcardCopy = true) ∧
      (∀ u v, mb.mapping.symm u = some v → r.value.mapping.symm u = some v) ∧
      (strategy = .Leave → ∀ u, ¬ target[u].isFunctionReturnLabel →
        r.value.mapping.symm u = mb.mapping.symm u) := by
  unfold copyStep
  dsimp only
  split
  · exact ⟨rfl, hsize, id, fun _ _ h => h, fun _ _ _ => rfl⟩
  · next hfree =>
    refine (closestCopy_succeeds mb t _ hsize).bind fun r hr => ?_
    split
    · next copy =>
      have hs := hr copy rfl
      have ht := symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1
      rw [map_ok mb _ _ hs ht]
      split
      · next hlabel =>
        refine ⟨rfl, hsize, id, bind_keeps_inverse mb copy t hs.2 ht, ?_⟩
        intro _ u hu
        have hne : u ≠ t := by intro heq; subst u; exact hu hlabel
        exact Mapping.bind_symm_apply_of_ne mb.mapping copy t hs.2 ht u hne
      · split
        · next htake =>
          refine ⟨rfl, hsize, fun _ => rfl, bind_keeps_inverse mb copy t hs.2 ht, ?_⟩
          intro hleave
          subst strategy
          cases hleave
        · exact ⟨rfl, hsize, fun _ => rfl, fun _ _ h => h, fun _ _ _ => rfl⟩
    · exact ⟨rfl, hsize, id, fun _ _ h => h, fun _ _ _ => rfl⟩

-- The first optional copy sets both flags and supplies a witness of different bindings.
theorem copyStep_same (t : Fin target.length) (mb : MappingBuilder source target)
    (hsize : mb.dropped.length = source.length) (hflag : mb.sawWildcardCopy = false) :
    Both (copyStep .Leave t mb) (copyStep .Take t mb) fun left right =>
      left = .yield left.value ∧ right = .yield right.value ∧ Compared left.value right.value := by
  unfold Both copyStep
  dsimp only
  by_cases hfree : mb.hasSourceAssigned t ∨ mb.isWildcardTarget t
  · simp only [ite_eq_left hfree]
    exact ⟨rfl, rfl, hsize, hsize, Or.inl ⟨rfl, hflag⟩⟩
  · simp only [ite_eq_right hfree]
    obtain ⟨r, hr, hcopy⟩ := (closestCopy_succeeds mb t .InWildcardSlots hsize).exists
    rw [hr]
    simp only [except_ok_bind]
    cases r with
    | none => exact ⟨rfl, rfl, hsize, hsize, Or.inl ⟨rfl, hflag⟩⟩
    | some copy =>
      dsimp only
      have hs := hcopy copy rfl
      have ht := symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1
      rw [map_ok mb _ _ hs ht]
      by_cases hlabel : target[t].isFunctionReturnLabel
      · simp only [ite_eq_left hlabel, except_ok_bind]
        exact ⟨rfl, rfl, hsize, hsize, Or.inl ⟨rfl, hflag⟩⟩
      · simp only [ite_eq_right hlabel, reduceCtorEq, ite_false, ite_true, except_ok_bind]
        refine ⟨rfl, rfl, hsize, hsize, Or.inr ⟨rfl, rfl, t, copy, ?_, hlabel, ht, ?_⟩⟩
        · intro hwild
          exact (not_or.mp hfree).2 (by simpa only [isWildcardTarget, decide_eq_true_eq] using hwild)
        · exact Mapping.bind_symm_apply mb.mapping copy t hs.2 ht

theorem copyStep_compared (t : Fin target.length) (left right : MappingBuilder source target)
    (h : Compared left right) :
    Both (copyStep .Leave t left) (copyStep .Take t right) fun l r =>
      l = .yield l.value ∧ r = .yield r.value ∧ Compared l.value r.value := by
  obtain ⟨hleft, hright, hsame | hdiff⟩ := h
  · obtain ⟨rfl, hflag⟩ := hsame
    exact copyStep_same t left hleft hflag
  · obtain ⟨hlflag, hrflag, u, v, hwild, hlabel, hlbound, hrbound⟩ := hdiff
    obtain ⟨l, hl, hpl⟩ := (copyStep_preserves .Leave t left hleft).exists
    obtain ⟨r, hr, hpr⟩ := (copyStep_preserves .Take t right hright).exists
    simp only [Both, hl, hr, succeeds_ok]
    exact ⟨hpl.1, hpr.1, hpl.2.1, hpr.2.1,
      Or.inr ⟨hpl.2.2.1 hlflag, hpr.2.2.1 hrflag, u, v, hwild, hlabel,
        (hpl.2.2.2.2 rfl u hlabel).trans hlbound, hpr.2.2.2.1 u v hrbound⟩⟩

theorem copyPass_compared (left right : MappingBuilder source target) (h : Compared left right) :
    Both (copyPass .Leave left) (copyPass .Take right) Compared :=
  Both.forIn Compared _ left right _ _ h copyStep_compared

end Shuffler.BuildMapping.Strategies
