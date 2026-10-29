import Shuffler.BuildMapping.Lemmas.Basic

namespace Shuffler.BuildMapping

-- Adding a binding at a free source keeps every existing binding.
private theorem bind_preserves {a b : ℕ} (mapping : Mapping a b) (p : Fin a) (q : Fin b)
    (hp : mapping p = none) (hq : mapping.symm q = none)
    (s : Fin a) (t : Fin b) (hbound : mapping s = some t) :
    mapping.bind p q hp hq s = some t := by
  have hne : s ≠ p := by
    intro heq
    subst s
    rw [hp] at hbound
    cases hbound
  exact (Mapping.bind_apply_of_ne mapping p q hp hq s hne).trans hbound

-- A loop establishes `post` when it visits `wanted` and keeps it in later iterations.
private theorem succeeds_forIn_at (inv post : β → Prop) (wanted : α) (l : List α) (init : β)
    (f : α → β → Except ShuffleErr (ForInStep β)) (hinv : inv init) (hmem : wanted ∈ l)
    (step : ∀ a b, inv b → Succeeds (f a b) fun r =>
      r = .yield r.value ∧ inv r.value ∧ (post b → post r.value) ∧
        (a = wanted → post r.value)) :
    Succeeds (forIn l init f) fun b => inv b ∧ post b := by
  induction l generalizing init with
  | nil => simp at hmem
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (step a init hinv).bind fun r hr => ?_
    cases r with
    | done b => cases hr.1
    | yield b =>
      rcases List.mem_cons.mp hmem with heq | hmem
      · have hp : post b := hr.2.2.2 heq.symm
        exact Succeeds.forIn (fun b => inv b ∧ post b) l b f ⟨hr.2.1, hp⟩
          fun a b hb => (step a b hb.1).mono fun r hr => ⟨hr.2.1, hr.2.2.1 hb.2⟩
      · exact ih b hr.2.1 hmem

open MappingBuilder

-- Equal values at the same offset are bound in the first pass and keep that binding.
theorem buildMapping_succeeds_in_place (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) (hsizes : dropped.length = source.length)
    (s : Fin source.length) (t : Fin target.length) (hpos : s.val = t.val)
    (hvalue : source[s] = target[t]) (hdrop : dropped[s.val]? = some 0) :
    Succeeds (buildMapping source target dropped strategy) fun result =>
      result.mapping s = some t := by
  rw [Strategies.buildMapping_eq_phases]
  unfold Strategies.initialPasses Strategies.copyPass Strategies.suffix
    Strategies.copyStep Strategies.keepStep Strategies.surplusStep
  simp only [bind_assoc, pure_bind]
  rw [requires_of_true _ hsizes, except_ok_bind]
  let j : Fin (min source.length target.length) :=
    ⟨s.val, Nat.lt_min.mpr ⟨s.isLt, by rw [hpos]; exact t.isLt⟩⟩
  have hjs : Fin.castLE (min_le_left source.length target.length) j = s := Fin.ext rfl
  have hjt : Fin.castLE (min_le_right source.length target.length) j = t := Fin.ext hpos
  refine (succeeds_forIn_at
    (fun mb : MappingBuilder source target => Diagonal mb.mapping ∧ mb.dropped = dropped)
    (fun mb => mb.mapping s = some t) j _ _ _ ⟨diagonal_bot, rfl⟩
    (List.mem_finRange j) ?_).bind fun mb ⟨⟨_, hdropped⟩, hbound⟩ => ?_
  · intro i mb ⟨hdiag, hdropped⟩
    have hsize : mb.dropped.length = source.length := hdropped ▸ hsizes
    simp only [mappable_ok mb _ hsize, except_ok_bind]
    split
    · next hcond =>
      have hs : mb.IsMappable (Fin.castLE (min_le_left _ _) i) := of_decide_eq_true hcond.2
      have ht := diagonal_symm_eq_none mb.mapping hdiag (Fin.castLE (min_le_left _ _) i)
        (Fin.castLE (min_le_right _ _) i) rfl hs.2
      rw [map_ok mb _ _ hs ht]
      refine ⟨rfl, ⟨diagonal_bind _ hdiag _ _ rfl hs.2 ht, hdropped⟩,
        fun hbound => bind_preserves _ _ _ hs.2 ht _ _ hbound, ?_⟩
      intro hi
      subst i
      simpa only [ForInStep.value, hjs, hjt] using Mapping.bind_apply mb.mapping _ _ hs.2 ht
    · next hcond =>
      refine ⟨rfl, ⟨hdiag, hdropped⟩, id, ?_⟩
      intro hi
      subst i
      simp only [hjs, hjt, hvalue, true_and] at hcond
      have hnot : ¬ mb.IsMappable s := of_decide_eq_false (Bool.eq_false_of_not_eq_true hcond)
      cases hbound : mb.mapping s with
      | none => exact (hnot ⟨hdropped ▸ hdrop, hbound⟩).elim
      | some u =>
        have hut : u = t := Fin.ext ((hdiag s u hbound).symm.trans hpos)
        simpa only [ForInStep.value, hut] using hbound
  have hsize : mb.dropped.length = source.length := hdropped ▸ hsizes

  -- All remaining passes add bindings and keep each previous binding.
  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    mb.dropped.length = source.length ∧ mb.mapping s = some t) _ _ _ ⟨hsize, hbound⟩ ?_).bind
    fun mb ⟨hsize, hbound⟩ => ?_
  · intro u mb ⟨hsize, hbound⟩
    split
    · exact ⟨hsize, hbound⟩
    · next hfree =>
      refine (closestCopy_succeeds mb u _ hsize).bind fun r hr => ?_
      split
      · next copy =>
        have hs := hr copy rfl
        have ht := symm_eq_none_of_not_hasSourceAssigned mb u (not_or.mp hfree).1
        rw [map_ok mb _ _ hs ht]
        exact ⟨hsize, bind_preserves _ _ _ hs.2 ht _ _ hbound⟩
      · exact ⟨hsize, hbound⟩

  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    mb.dropped.length = source.length ∧ mb.mapping s = some t) _ _ _ ⟨hsize, hbound⟩ ?_).bind
    fun mb ⟨hsize, hbound⟩ => ?_
  · intro u mb ⟨hsize, hbound⟩
    split
    · exact ⟨hsize, hbound⟩
    · next hfree =>
      refine (closestCopy_succeeds mb u _ hsize).bind fun r hr => ?_
      split
      · next copy =>
        have hs := hr copy rfl
        have ht := symm_eq_none_of_not_hasSourceAssigned mb u (not_or.mp hfree).1
        rw [map_ok mb _ _ hs ht]
        have hbound' := bind_preserves _ _ _ hs.2 ht _ _ hbound
        split
        · exact ⟨hsize, hbound'⟩
        · split
          · exact ⟨hsize, hbound'⟩
          · exact ⟨hsize, hbound⟩
      · exact ⟨hsize, hbound⟩

  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    mb.dropped.length = source.length ∧ mb.mapping s = some t) _ _ _ ⟨hsize, hbound⟩ ?_).bind
    fun mb ⟨hsize, hbound⟩ => ?_
  · intro i mb ⟨hsize, hbound⟩
    simp only [mappable_ok mb _ hsize, except_ok_bind]
    split
    · next hcond =>
      have hs := of_decide_eq_true hcond.2.2
      have ht := symm_eq_none_of_not_hasSourceAssigned mb _ hcond.2.1
      rw [map_ok mb _ _ hs ht]
      exact ⟨hsize, bind_preserves _ _ _ hs.2 ht _ _ hbound⟩
    · exact ⟨hsize, hbound⟩

  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    mb.dropped.length = source.length ∧ mb.mapping s = some t) _ _ _ ⟨hsize, hbound⟩ ?_).bind
    fun _ ⟨_, hbound⟩ => hbound
  · intro u mb ⟨hsize, hbound⟩
    split
    · exact ⟨hsize, hbound⟩
    · next hfree =>
      refine (closestSurplus_succeeds mb u hsize).bind fun r hr => ?_
      split
      · next best =>
        have hs := hr best rfl
        have ht := symm_eq_none_of_not_hasSourceAssigned mb u (not_or.mp hfree).1
        rw [map_ok mb _ _ hs ht]
        exact ⟨hsize, bind_preserves _ _ _ hs.2 ht _ _ hbound⟩
      · exact ⟨hsize, hbound⟩

end Shuffler.BuildMapping
