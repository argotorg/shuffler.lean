module

public import Shuffler.BuildMapping.Lemmas.Basic

@[expose] public section

namespace Shuffler.BuildMapping

variable {source target : Stack}

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

private theorem closestCopy_complete (mb : MappingBuilder source target)
    (t : Fin target.length) (location : CopyLocation)
    (hsize : mb.dropped.length = source.length) (s : Fin source.length)
    (hs : mb.IsMappable s) (hvalue : source[s] = target[t])
    (hloc : mb.inWildcardSlot s = decide (location = .InWildcardSlots)) :
    Succeeds (mb.closestCopy t location) fun r => r.isSome := by
  unfold closestCopy
  refine (succeeds_forIn_at (fun _ => True) (fun r : Option (Fin source.length) => r.isSome)
    s _ _ _ trivial (List.mem_finRange s) ?_).bind fun _ h => h.2
  intro i best _
  simp only [mappable_ok mb i hsize, except_ok_bind]
  split
  · split
    · exact ⟨rfl, trivial, fun _ => rfl, fun _ => rfl⟩
    · next hnot =>
      have hb : best.isSome = true := by
        by_cases h : best.isSome = true
        · exact h
        · exact (hnot (Or.inl h)).elim
      exact ⟨rfl, trivial, fun _ => hb, fun _ => hb⟩
  · next hnot =>
    refine ⟨rfl, trivial, id, ?_⟩
    intro hi
    subst i
    exact (hnot ⟨hvalue, decide_eq_true hs, hloc⟩).elim

private def HasCopy (mb : MappingBuilder source target) (value : Value) : Prop :=
  ∃ s t, mb.mapping s = some t ∧ source[s] = value

private theorem hasCopy_of_bound (mb : MappingBuilder source target) (s : Fin source.length)
    (value : Value) (hvalue : source[s] = value) (hbound : mb.mapping s ≠ none) :
    HasCopy mb value := by
  cases h : mb.mapping s with
  | none => exact (hbound h).elim
  | some t => exact ⟨s, t, h, hvalue⟩

private theorem hasCopy_bind (mb : MappingBuilder source target) (s : Fin source.length)
    (t : Fin target.length) (hs : mb.mapping s = none) (ht : mb.mapping.symm t = none)
    (value : Value) (h : HasCopy mb value) :
    HasCopy { mb with mapping := mb.mapping.bind s t hs ht } value := by
  obtain ⟨i, j, hij, hv⟩ := h
  have hi : i ≠ s := by intro heq; subst i; rw [hs] at hij; cases hij
  exact ⟨i, j, (Mapping.bind_apply_of_ne mb.mapping s t hs ht i hi).trans hij, hv⟩

private theorem hasCopy_of_assigned (mb : MappingBuilder source target) (hv : mb.BindingsValid)
    (j : Fin target.length) (hj : ¬ target[j].is_junk) (h : mb.hasSourceAssigned j) :
    HasCopy mb target[j] := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
  have hbound := mb.mapping.eq_some_iff.mp hs
  exact ⟨s, j, hbound, (hv s j hbound).2.resolve_left hj⟩

private def Extends (before after : MappingBuilder source target) : Prop :=
  ∀ s t, before.mapping s = some t → after.mapping s = some t

private theorem extends_refl (mb : MappingBuilder source target) : Extends mb mb := by
  intro _ _ h; exact h

private theorem extends_bind (mb : MappingBuilder source target) (s : Fin source.length)
    (t : Fin target.length) (hs : mb.mapping s = none) (ht : mb.mapping.symm t = none) :
    Extends mb { mb with mapping := mb.mapping.bind s t hs ht } := by
  intro i j hij
  have hi : i ≠ s := by intro heq; subst i; rw [hs] at hij; cases hij
  exact (Mapping.bind_apply_of_ne mb.mapping s t hs ht i hi).trans hij

private theorem extends_hasCopy {before after : MappingBuilder source target}
    (h : Extends before after) {v : Value} (hv : HasCopy before v) : HasCopy after v := by
  obtain ⟨s, t, hbound, hvalue⟩ := hv
  exact ⟨s, t, h s t hbound, hvalue⟩

private def NonwildExtension (before after : MappingBuilder source target) : Prop :=
  after.dropped = before.dropped ∧ after.BindingsValid ∧ Extends before after ∧
    ∀ t, target[t].is_junk → after.mapping.symm t = before.mapping.symm t

private theorem nonwildExtension_refl (mb : MappingBuilder source target) (hv : mb.BindingsValid) :
    NonwildExtension mb mb := ⟨rfl, hv, extends_refl mb, fun _ _ => rfl⟩

private theorem nonwildExtension_bind (mb : MappingBuilder source target) (hv : mb.BindingsValid)
    (s : Fin source.length) (t : Fin target.length) (hs : mb.IsMappable s)
    (ht : mb.mapping.symm t = none) (hvalue : source[s] = target[t]) (hwild : ¬ target[t].is_junk) :
    NonwildExtension mb { mb with mapping := mb.mapping.bind s t hs.2 ht } := by
  refine ⟨rfl, bindingsValid_bind mb hv s t hs ht (Or.inr hvalue),
    extends_bind mb s t hs.2 ht, ?_⟩
  intro u hu
  have hne : u ≠ t := by intro heq; subst u; exact hwild hu
  exact Mapping.bind_symm_apply_of_ne mb.mapping s t hs.2 ht u hne

private def outsideStep (t : Fin target.length) (mb : MappingBuilder source target) :
    Except ShuffleErr (ForInStep (MappingBuilder source target)) := do
  if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then return .yield mb
  match ← mb.closestCopy t .OutsideWildcardSlots with
  | some copy => return .yield (← mb.map copy t)
  | none => return .yield mb

private theorem outsideStep_spec (t : Fin target.length) (mb : MappingBuilder source target)
    (hsize : mb.dropped.length = source.length) (hv : mb.BindingsValid) :
    Succeeds (outsideStep t mb) fun r =>
      r = .yield r.value ∧ NonwildExtension mb r.value := by
  unfold outsideStep
  split
  · exact ⟨rfl, nonwildExtension_refl mb hv⟩
  · next hfree =>
    refine (closestCopy_succeeds_matches mb t _ hsize).bind fun r hr => ?_
    split
    · next copy =>
      have hs := (hr copy rfl).1
      have ht := symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1
      rw [map_ok mb _ _ hs ht]
      exact ⟨rfl, nonwildExtension_bind mb hv copy t hs ht (hr copy rfl).2
        (by simpa [isWildcardTarget] using (not_or.mp hfree).2)⟩
    · exact ⟨rfl, nonwildExtension_refl mb hv⟩

private theorem copyStep_spec (strategy : WildcardSlotsStrategy) (t : Fin target.length)
    (mb : MappingBuilder source target) (hsize : mb.dropped.length = source.length)
    (hv : mb.BindingsValid) :
    Succeeds (Strategies.copyStep strategy t mb) fun r =>
      r = .yield r.value ∧ NonwildExtension mb r.value := by
  simp only [Strategies.copyStep]
  split
  · exact ⟨rfl, nonwildExtension_refl mb hv⟩
  · next hfree =>
    refine (closestCopy_succeeds_matches mb t _ hsize).bind fun r hr => ?_
    split
    · next copy =>
      have hs := (hr copy rfl).1
      have ht := symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1
      rw [map_ok mb _ _ hs ht]
      have h := nonwildExtension_bind mb hv copy t hs ht (hr copy rfl).2
        (by simpa [isWildcardTarget] using (not_or.mp hfree).2)
      split
      · exact ⟨rfl, h⟩
      · split
        · exact ⟨rfl, h⟩
        · exact ⟨rfl, nonwildExtension_refl mb hv⟩
    · exact ⟨rfl, nonwildExtension_refl mb hv⟩

private theorem outsideStep_at (mb : MappingBuilder source target) (hv : mb.BindingsValid)
    (hsize : mb.dropped.length = source.length) (s : Fin source.length) (j : Fin target.length)
    (hdrop : mb.dropped[s.val]? = some 0) (hvalue : source[s] = target[j])
    (hj : ¬ target[j].is_junk) :
    Succeeds (outsideStep j mb) fun r =>
      HasCopy r.value target[j] ∨ mb.inWildcardSlot s = true := by
  by_cases hc : HasCopy mb target[j]
  · exact (outsideStep_spec j mb hsize hv).mono fun r hr =>
      Or.inl (extends_hasCopy hr.2.2.2.1 hc)
  by_cases hl : mb.inWildcardSlot s = true
  · exact (outsideStep_spec j mb hsize hv).mono fun _ _ => Or.inr hl
  have hsfree : mb.mapping s = none := by
    by_contra h
    exact hc (hasCopy_of_bound mb s _ hvalue h)
  have hs : mb.IsMappable s := ⟨hdrop, hsfree⟩
  have hloc : mb.inWildcardSlot s = decide (CopyLocation.OutsideWildcardSlots = .InWildcardSlots) :=
    Bool.eq_false_of_not_eq_true hl
  unfold outsideStep
  split
  · next hcond =>
    have ha : mb.hasSourceAssigned j := hcond.resolve_right (by simpa [isWildcardTarget] using hj)
    exact (hc (hasCopy_of_assigned mb hv j hj ha)).elim
  · next hfree =>
    obtain ⟨r, hrun, hsome⟩ := (closestCopy_complete mb j .OutsideWildcardSlots hsize s hs hvalue hloc).exists
    obtain ⟨copy, rfl⟩ := Option.isSome_iff_exists.mp hsome
    have hmatch := closestCopy_succeeds_matches mb j .OutsideWildcardSlots hsize
    rw [hrun] at hmatch
    have hcopy := hmatch copy rfl
    simp only [hrun, except_ok_bind]
    have ht := symm_eq_none_of_not_hasSourceAssigned mb j (not_or.mp hfree).1
    rw [map_ok mb _ _ hcopy.1 ht]
    exact Or.inl ⟨copy, j, Mapping.bind_apply mb.mapping copy j hcopy.1.2 ht, hcopy.2⟩

private theorem Succeeds.and {result : Except ShuffleErr α} {p q : α → Prop}
    (hp : Succeeds result p) (hq : Succeeds result q) : Succeeds result fun r => p r ∧ q r := by
  cases result with
  | ok r => exact ⟨hp, hq⟩
  | error e => exact hp.elim

private def Seed (dropped : List Byte) (s : Fin source.length) (v : Value)
    (mb : MappingBuilder source target) : Prop :=
  mb.dropped = dropped ∧ mb.BindingsValid ∧
    ∀ t : Fin target.length, t.val = s.val → target[t].is_junk →
      HasCopy mb v ∨ mb.mapping.symm t = none

private theorem seed_nonwild (dropped : List Byte) (s : Fin source.length) (v : Value)
    {before after : MappingBuilder source target} (hseed : Seed dropped s v before)
    (h : NonwildExtension before after) : Seed dropped s v after := by
  refine ⟨h.1.trans hseed.1, h.2.1, ?_⟩
  intro t hpos hwild
  rcases hseed.2.2 t hpos hwild with hc | hfree
  · exact Or.inl (extends_hasCopy h.2.2.1 hc)
  · exact Or.inr ((h.2.2.2 t hwild).trans hfree)

private theorem seed_diagonal_bind (dropped : List Byte) (s : Fin source.length) (v : Value)
    (mb : MappingBuilder source target) (hseed : Seed dropped s v mb) (hvalue : source[s] = v)
    (i : Fin source.length) (t : Fin target.length) (hpos : i.val = t.val)
    (hs : mb.IsMappable i) (ht : mb.mapping.symm t = none) (hmatches : SlotMatches source[i] target[t]) :
    Seed dropped s v { mb with mapping := mb.mapping.bind i t hs.2 ht } := by
  refine ⟨hseed.1, bindingsValid_bind mb hseed.2.1 i t hs ht hmatches, ?_⟩
  intro u hus huwild
  by_cases hut : u = t
  · subst u
    have his : i = s := Fin.ext (hpos.trans hus)
    subst i
    exact Or.inl ⟨s, t, Mapping.bind_apply mb.mapping s t hs.2 ht, hvalue⟩
  · rcases hseed.2.2 u hus huwild with hc | hfree
    · exact Or.inl (hasCopy_bind mb i t hs.2 ht v hc)
    · exact Or.inr ((Mapping.bind_symm_apply_of_ne mb.mapping i t hs.2 ht u hut).trans hfree)

-- A demanded value from an undropped source remains in the emitted source mapping.
theorem buildMapping_succeeds_available (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) (hsizes : dropped.length = source.length)
    (s : Fin source.length) (j : Fin target.length)
    (hdrop : dropped[s.val]? = some 0) (hvalue : source[s] = target[j])
    (hj : ¬ target[j].is_junk) :
    Succeeds (buildMapping source target dropped strategy) fun result =>
      ∃ i dest, result.mapping i = some dest ∧ source[i] = target[j] := by
  rw [Strategies.buildMapping_eq_phases]
  unfold Strategies.initialPasses Strategies.copyPass Strategies.suffix
  simp only [bind_assoc, pure_bind]
  rw [requires_of_true _ hsizes, except_ok_bind]

  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    Diagonal mb.mapping ∧ mb.dropped = dropped ∧ mb.BindingsValid) _ _ _
    ⟨diagonal_bot, rfl, bindingsValid_bot dropped⟩ ?_).bind fun mb ⟨hdiag, hd, hv⟩ => ?_
  · intro u mb ⟨hdiag, hd, hv⟩
    have hsize : mb.dropped.length = source.length := hd ▸ hsizes
    simp only [mappable_ok mb _ hsize, except_ok_bind]
    split
    · next hcond =>
      have hs := of_decide_eq_true hcond.2
      have ht := diagonal_symm_eq_none mb.mapping hdiag (Fin.castLE (min_le_left _ _) u)
        (Fin.castLE (min_le_right _ _) u) rfl hs.2
      rw [map_ok mb _ _ hs ht]
      exact ⟨diagonal_bind _ hdiag _ _ rfl hs.2 ht, hd,
        bindingsValid_bind mb hv _ _ hs ht (Or.inr hcond.1)⟩
    · exact ⟨hdiag, hd, hv⟩
  have hseed : Seed dropped s target[j] mb := by
    refine ⟨hd, hv, ?_⟩
    intro t hts _
    cases hbound : mb.mapping.symm t with
    | none => exact Or.inr rfl
    | some i =>
      have hib := mb.mapping.eq_some_iff.mp hbound
      have his : i = s := Fin.ext ((hdiag i t hib).trans hts)
      subst i
      exact Or.inl ⟨s, t, hib, hvalue⟩

  change Succeeds ((forIn (List.finRange target.length) mb outsideStep) >>= _) _
  refine (succeeds_forIn_at (Seed dropped s target[j])
    (fun mb => HasCopy mb target[j] ∨ mb.inWildcardSlot s = true)
    j _ mb outsideStep hseed (List.mem_finRange j) ?_).bind fun mb ⟨hseed, hcopy⟩ => ?_
  · intro t mb hseed
    have hsize : mb.dropped.length = source.length := hseed.1 ▸ hsizes
    refine ((outsideStep_spec t mb hsize hseed.2.1).and
      (show Succeeds (outsideStep t mb) fun r =>
        t = j → HasCopy r.value target[j] ∨ r.value.inWildcardSlot s = true from ?_)).mono
      fun r ⟨hr, hat⟩ => ⟨hr.1, seed_nonwild dropped s _ hseed hr.2, ?_, hat⟩
    · by_cases ht : t = j
      · subst t
        exact (outsideStep_at mb hseed.2.1 hsize s j (hseed.1 ▸ hdrop) hvalue hj).mono
          fun _ h _ => h
      · exact (outsideStep_spec t mb hsize hseed.2.1).mono fun _ _ h => (ht h).elim

    · intro hp
      rcases hp with hc | hl
      · exact Or.inl (extends_hasCopy hr.2.2.2.1 hc)
      · exact Or.inr hl

  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    Seed dropped s target[j] mb ∧ (HasCopy mb target[j] ∨ mb.inWildcardSlot s = true))
    _ _ _ ⟨hseed, hcopy⟩ ?_).bind fun mb ⟨hseed, hcopy⟩ => ?_
  · intro t mb ⟨hseed, hcopy⟩
    have hsize : mb.dropped.length = source.length := hseed.1 ▸ hsizes
    exact (copyStep_spec strategy t mb hsize hseed.2.1).mono fun r hr =>
      ⟨seed_nonwild dropped s _ hseed hr.2, hcopy.elim
        (fun hc => Or.inl (extends_hasCopy hr.2.2.2.1 hc)) Or.inr⟩

  have hkeep : Succeeds (forIn (List.finRange (min source.length target.length)) mb Strategies.keepStep)
      fun mb => Seed dropped s target[j] mb ∧ HasCopy mb target[j] := by
    have hstep : ∀ (i : Fin (min source.length target.length)) (mb : MappingBuilder source target), Seed dropped s target[j] mb →
        Succeeds (Strategies.keepStep i mb) fun r =>
          r = .yield r.value ∧ Seed dropped s target[j] r.value ∧
            (HasCopy mb target[j] → HasCopy r.value target[j]) := by
      intro i mb hseed
      have hsize : mb.dropped.length = source.length := hseed.1 ▸ hsizes
      simp only [Strategies.keepStep, mappable_ok mb _ hsize, except_ok_bind]
      split
      · next hcond =>
        have hs := of_decide_eq_true hcond.2.2
        have ht := symm_eq_none_of_not_hasSourceAssigned mb _ hcond.2.1
        rw [map_ok mb _ _ hs ht]
        exact ⟨rfl, seed_diagonal_bind dropped s _ mb hseed hvalue _ _ rfl hs ht
          (Or.inl (of_decide_eq_true hcond.1)), hasCopy_bind mb _ _ hs.2 ht _⟩
      · exact ⟨rfl, hseed, id⟩
    rcases hcopy with hc | hl
    · exact Succeeds.forIn (fun mb => Seed dropped s target[j] mb ∧ HasCopy mb target[j])
        _ mb _ ⟨hseed, hc⟩ fun i mb hi => (hstep i mb hi.1).mono fun _ hr =>
          ⟨hr.2.1, hr.2.2 hi.2⟩
    · have hlt : s.val < target.length := by
        by_contra h
        simp [inWildcardSlot, Nat.not_lt.mp h] at hl
      let wanted : Fin (min source.length target.length) := ⟨s.val, Nat.lt_min.mpr ⟨s.isLt, hlt⟩⟩
      have hws : Fin.castLE (min_le_left source.length target.length) wanted = s := Fin.ext rfl
      let tw : Fin target.length := Fin.castLE (min_le_right source.length target.length) wanted
      have hwt : target[tw].is_junk := by
        simpa [inWildcardSlot, hlt, isWildcardTarget, tw, wanted] using hl
      exact (succeeds_forIn_at (Seed dropped s target[j]) (fun mb => HasCopy mb target[j])
        wanted _ mb Strategies.keepStep hseed (List.mem_finRange wanted) fun i mb hi =>
        ((hstep i mb hi).and (show Succeeds (Strategies.keepStep i mb) fun r =>
          i = wanted → HasCopy r.value target[j] from by
          by_cases heq : i = wanted
          · subst i
            by_cases hc : HasCopy mb target[j]
            · exact (hstep wanted mb hi).mono fun _ hr _ => hr.2.2 hc
            have hfree : mb.mapping s = none := by
              by_contra h; exact hc (hasCopy_of_bound mb s _ hvalue h)
            have hs : mb.IsMappable s := ⟨hi.1 ▸ hdrop, hfree⟩
            have ht : mb.mapping.symm tw = none := (hi.2.2 tw rfl hwt).resolve_left hc
            have hnotassigned : ¬ mb.hasSourceAssigned tw := by simp [hasSourceAssigned, ht]
            simp only [Strategies.keepStep, hws, mappable_of_isMappable mb s hs, except_ok_bind]
            have hwild : mb.isWildcardTarget tw := by simpa [isWildcardTarget] using hwt
            simp only [show mb.isWildcardTarget (Fin.castLE (min_le_right _ _) wanted) = true from hwild,
              show ¬ mb.hasSourceAssigned (Fin.castLE (min_le_right _ _) wanted) from hnotassigned,
              and_true]
            rw [map_ok mb _ _ hs ht]
            exact fun _ => ⟨s, tw, Mapping.bind_apply mb.mapping s tw hs.2 ht, hvalue⟩
          · exact (hstep i mb hi).mono fun _ _ h => (heq h).elim)).mono
            fun r ⟨hr, hat⟩ => ⟨hr.1, hr.2.1, hr.2.2, hat⟩)
  refine hkeep.bind fun mb ⟨hseed, hc⟩ => ?_
  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    mb.dropped.length = source.length ∧ HasCopy mb target[j]) _ _ _
    ⟨hseed.1 ▸ hsizes, hc⟩ ?_).bind fun _ h => h.2
  intro t mb ⟨hsize, hc⟩
  simp only [Strategies.surplusStep]
  split
  · exact ⟨hsize, hc⟩
  · next hfree =>
    refine (closestSurplus_succeeds mb t hsize).bind fun r hr => ?_
    split
    · next best =>
      have hs := hr best rfl
      have ht := symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1
      rw [map_ok mb _ _ hs ht]
      exact ⟨hsize, hasCopy_bind mb best t hs.2 ht _ hc⟩
    · exact ⟨hsize, hc⟩

theorem buildMapping_available_of_ok (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) {result : BuildMappingResult source target}
    (hrun : buildMapping source target dropped strategy = .ok result)
    (s : Fin source.length) (j : Fin target.length)
    (hdrop : dropped[s.val]? = some 0) (hvalue : source[s] = target[j])
    (hj : ¬ target[j].is_junk) :
    ∃ i dest, result.mapping i = some dest ∧ source[i] = target[j] := by
  have hsizes : dropped.length = source.length := by
    by_contra h
    simp only [buildMapping, requires, dite_eq_right h] at hrun
    cases hrun
  have h := buildMapping_succeeds_available source target dropped strategy hsizes s j hdrop hvalue hj
  simpa only [hrun, succeeds_ok] using h

end Shuffler.BuildMapping
