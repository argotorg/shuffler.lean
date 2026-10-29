module

public import Shuffler.BuildMapping.Lemmas.Basic
import all Shuffler.BuildMapping.Lemmas.Availability
import Shuffler.BuildMapping.Lemmas.Strategies.Suffix
import Mathlib.Data.Fintype.Fin
import all Batteries.Tactic.PrintOpaques

@[expose] public section

namespace Shuffler.BuildMapping

open MappingBuilder

variable {source target : Stack}

private def ExactBindings (mb : MappingBuilder source target) : Prop :=
  ∀ s t, mb.mapping s = some t → source[s] = target[t]

private theorem exact_bind (mb : MappingBuilder source target) (hexact : ExactBindings mb)
    (s : Fin source.length) (t : Fin target.length) (hs : mb.IsMappable s)
    (ht : mb.mapping.symm t = none) (hv : source[s] = target[t]) :
    ExactBindings { mb with mapping := mb.mapping.bind s t hs.2 ht } := by
  intro i j hij
  by_cases hi : i = s
  · subst i
    simp only [Mapping.bind_apply, Option.some.injEq] at hij
    subst j
    exact hv
  · exact hexact i j ((Mapping.bind_apply_of_ne mb.mapping s t hs.2 ht i hi).symm.trans hij)

private theorem exact_nonwild {before after : MappingBuilder source target}
    (hexact : ExactBindings before) (hext : NonwildExtension before after) : ExactBindings after := by
  intro s t hb
  by_cases hw : target[t].is_junk
  · have hs := after.mapping.eq_some_iff.mpr hb
    rw [hext.2.2.2 t hw] at hs
    exact hexact s t (before.mapping.eq_some_iff.mp hs)
  · exact (hext.2.1 s t hb).2.resolve_left hw

private theorem label_card (stack : Stack) :
    (Finset.univ.filter (fun i : Fin stack.length => stack[i] = .FunctionReturnLabel)).card =
      stack.count .FunctionReturnLabel := by
  exact Fin.card_filter_univ_eq_vector_get_eq_count Value.FunctionReturnLabel
    (⟨stack, rfl⟩ : List.Vector Value stack.length)

private theorem free_label_exists (mb : MappingBuilder source target)
    (hexact : ExactBindings mb)
    (hcount : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel)
    (hdrop : ∀ s : Fin source.length, source[s] = .FunctionReturnLabel → mb.dropped[s.val]? = some 0)
    (j : Fin target.length) (hj : target[j] = .FunctionReturnLabel)
    (hfree : mb.mapping.symm j = none) :
    ∃ s : Fin source.length, source[s] = .FunctionReturnLabel ∧ mb.IsMappable s := by
  by_contra h
  have hbound : ∀ s : Fin source.length, source[s] = .FunctionReturnLabel → (mb.mapping s).isSome := by
    intro s hs
    apply Option.isSome_iff_ne_none.mpr
    intro hm
    exact h ⟨s, hs, hdrop s hs, hm⟩
  let f : Fin source.length → Fin target.length := fun s =>
    if hs : source[s] = .FunctionReturnLabel then (mb.mapping s).get (hbound s hs) else j
  have hcard := Finset.card_le_card_of_injOn f
    (s := Finset.univ.filter (fun s : Fin source.length => source[s] = .FunctionReturnLabel))
    (t := (Finset.univ.filter (fun t : Fin target.length => target[t] = .FunctionReturnLabel)).erase j)
    (by
      intro s hs
      have hs' := (Finset.mem_filter.mp hs).2
      have hb : mb.mapping s = some (f s) := by
        simpa only [f, dite_eq_left hs'] using (Option.some_get (hbound s hs')).symm
      have hne : f s ≠ j := by
        intro heq
        have hi := mb.mapping.eq_some_iff.mpr hb
        rw [heq, hfree] at hi
        cases hi
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hexact s (f s) hb).symm.trans hs'⟩⟩)
    (by
      intro a ha b hb heq
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hma : mb.mapping a = some (f a) := by
        simpa only [f, dite_eq_left ha'] using (Option.some_get (hbound a ha')).symm
      have hmb : mb.mapping b = some (f b) := by
        simpa only [f, dite_eq_left hb'] using (Option.some_get (hbound b hb')).symm
      have hai := mb.mapping.eq_some_iff.mpr hma
      have hbi := mb.mapping.eq_some_iff.mpr hmb
      rw [heq] at hai
      exact Option.some.inj (hai.symm.trans hbi))
  rw [Finset.card_erase_of_mem (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and]
    using hj), label_card, label_card] at hcard
  have htpositive : 0 < target.count .FunctionReturnLabel := by
    exact List.count_pos_iff.mpr (hj ▸ List.getElem_mem j.isLt)
  omega

private def OutsideReady (mb : MappingBuilder source target) (j : Fin target.length) : Prop :=
  (mb.mapping.symm j).isSome ∨ ∀ s, source[s] = target[j] → mb.IsMappable s → mb.inWildcardSlot s = true

private theorem outsideReady_extends {before after : MappingBuilder source target}
    (hext : NonwildExtension before after) (j : Fin target.length)
    (h : OutsideReady before j) : OutsideReady after j := by
  rcases h with hb | h
  · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hb
    exact Or.inl (Option.isSome_iff_exists.mpr ⟨s,
      after.mapping.eq_some_iff.mpr (hext.2.2.1 s j (before.mapping.eq_some_iff.mp hs))⟩)
  · refine Or.inr fun s hv hs => h s hv ⟨?_, ?_⟩
    · simpa [← hext.1] using hs.1
    · by_contra hb
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists.mp hb
      have ha := hext.2.2.1 s t ht.symm
      rw [hs.2] at ha
      cases ha

private theorem outsideStep_ready (mb : MappingBuilder source target) (j : Fin target.length)
    (hsize : mb.dropped.length = source.length) (hj : ¬target[j].is_junk) :
    Succeeds (outsideStep j mb) fun r => OutsideReady r.value j := by
  unfold outsideStep
  split
  · next hcond =>
    exact Or.inl (hcond.resolve_right (by simpa [isWildcardTarget] using hj))
  · next hfree =>
    obtain ⟨r, hrun, hr⟩ := (closestCopy_succeeds_matches mb j .OutsideWildcardSlots hsize).exists
    rw [hrun, except_ok_bind]
    cases r with
    | some copy =>
      dsimp only
      have hs := (hr copy rfl).1
      have ht := symm_eq_none_of_not_hasSourceAssigned mb j (not_or.mp hfree).1
      rw [map_ok mb copy j hs ht]
      exact Or.inl (by simp)
    | none =>
      refine Or.inr fun s hv hs => ?_
      by_contra hl
      have hloc : mb.inWildcardSlot s = decide (CopyLocation.OutsideWildcardSlots = .InWildcardSlots) :=
        Bool.eq_false_of_not_eq_true hl
      have hc := closestCopy_complete mb j .OutsideWildcardSlots hsize s hs hv hloc
      rw [hrun] at hc
      cases hc

private def Good (dropped : List Byte) (mb : MappingBuilder source target) : Prop :=
  mb.dropped = dropped ∧ mb.BindingsValid ∧ ExactBindings mb

private theorem good_nonwild {dropped : List Byte} {before after : MappingBuilder source target}
    (hgood : Good dropped before) (hext : NonwildExtension before after) : Good dropped after :=
  ⟨hext.1.trans hgood.1, hext.2.1, exact_nonwild hgood.2.2 hext⟩

private theorem outsidePass_ready (mb : MappingBuilder source target) (dropped : List Byte)
    (hsize : dropped.length = source.length) (hgood : Good dropped mb)
    (j : Fin target.length) (hj : ¬target[j].is_junk) :
    Succeeds (forIn (List.finRange target.length) mb outsideStep) fun result =>
      Good dropped result ∧ OutsideReady result j := by
  apply succeeds_forIn_at (Good dropped) (fun mb => OutsideReady mb j) j _ _ _ hgood (List.mem_finRange j)
  intro t mb hgood
  have hsz : mb.dropped.length = source.length := hgood.1 ▸ hsize
  refine ((outsideStep_spec t mb hsz hgood.2.1).and
    (show Succeeds (outsideStep t mb) fun r => t = j → OutsideReady r.value j from ?_)).mono
      fun r ⟨hr, hat⟩ => ⟨hr.1, good_nonwild hgood hr.2,
        outsideReady_extends hr.2 j, hat⟩
  by_cases ht : t = j
  · subst t
    exact (outsideStep_ready mb j hsz hj).mono fun _ h _ => h
  · exact (outsideStep_spec t mb hsz hgood.2.1).mono fun _ _ h => (ht h).elim

private theorem label_eq (value : Value) (h : value.isFunctionReturnLabel) :
    value = .FunctionReturnLabel := by
  cases value <;> simp_all [Value.isFunctionReturnLabel]

private theorem label_not_junk (value : Value) (h : value.isFunctionReturnLabel) :
    ¬value.is_junk := by
  rw [label_eq value h]
  simp [Value.is_junk]

private theorem copyStep_label (strategy : WildcardSlotsStrategy)
    (mb : MappingBuilder source target) (dropped : List Byte)
    (hsize : dropped.length = source.length) (hgood : Good dropped mb)
    (hcount : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel)
    (hdrop : ∀ s : Fin source.length, source[s].isFunctionReturnLabel → dropped[s.val]? = some 0)
    (j : Fin target.length) (hj : target[j].isFunctionReturnLabel)
    (hready : OutsideReady mb j) :
    Succeeds (Strategies.copyStep strategy j mb) fun r => (r.value.mapping.symm j).isSome := by
  have hsz : mb.dropped.length = source.length := hgood.1 ▸ hsize
  by_cases hb : (mb.mapping.symm j).isSome
  · exact (copyStep_spec strategy j mb hsz hgood.2.1).mono fun r hr => by
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hb
      exact Option.isSome_iff_exists.mpr ⟨s,
        r.value.mapping.eq_some_iff.mpr (hr.2.2.2.1 s j (mb.mapping.eq_some_iff.mp hs))⟩
  have hready := hready.resolve_left hb
  have hfree : mb.mapping.symm j = none := Option.not_isSome_iff_eq_none.mp hb
  obtain ⟨s, hslabel, hs⟩ := free_label_exists mb hgood.2.2 hcount
    (fun s hs => hgood.1 ▸ hdrop s (by rw [hs]; simp [Value.isFunctionReturnLabel]))
    j (label_eq _ hj) hfree
  have hv : source[s] = target[j] := hslabel.trans (label_eq _ hj).symm
  have hloc := hready s hv hs
  obtain ⟨r, hrun, hsome⟩ := (closestCopy_complete mb j .InWildcardSlots hsz s hs hv
    (by simpa using hloc)).exists
  obtain ⟨copy, rfl⟩ := Option.isSome_iff_exists.mp hsome
  have hmatches := closestCopy_succeeds_matches mb j .InWildcardSlots hsz
  rw [hrun] at hmatches
  have hcopy := (hmatches copy rfl).1
  simp only [Strategies.copyStep, hasSourceAssigned, isWildcardTarget, Fin.castLE_refl,
    hfree, Option.isSome_none, Bool.false_eq_true, label_not_junk _ hj, ↓reduceIte,
    hrun, except_ok_bind, hj]
  rw [map_ok mb copy j hcopy hfree]
  exact (by simp)

private theorem bound_extends {before after : MappingBuilder source target}
    (hext : NonwildExtension before after) (j : Fin target.length)
    (h : (before.mapping.symm j).isSome) : (after.mapping.symm j).isSome := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
  exact Option.isSome_iff_exists.mpr ⟨s,
    after.mapping.eq_some_iff.mpr (hext.2.2.1 s j (before.mapping.eq_some_iff.mp hs))⟩

private theorem copyPass_label (strategy : WildcardSlotsStrategy)
    (mb : MappingBuilder source target) (dropped : List Byte)
    (hsize : dropped.length = source.length) (hgood : Good dropped mb)
    (hcount : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel)
    (hdrop : ∀ s : Fin source.length, source[s].isFunctionReturnLabel → dropped[s.val]? = some 0)
    (j : Fin target.length) (hj : target[j].isFunctionReturnLabel)
    (hready : OutsideReady mb j) :
    Succeeds (Strategies.copyPass strategy mb) fun result => (result.mapping.symm j).isSome := by
  unfold Strategies.copyPass
  refine (succeeds_forIn_at (fun mb => Good dropped mb ∧ OutsideReady mb j)
    (fun mb => (mb.mapping.symm j).isSome) j _ _ _ ⟨hgood, hready⟩ (List.mem_finRange j) ?_).mono
    fun _ hr => hr.2
  intro t mb ⟨hgood, hready⟩
  have hsz : mb.dropped.length = source.length := hgood.1 ▸ hsize
  refine ((copyStep_spec strategy t mb hsz hgood.2.1).and
    (show Succeeds (Strategies.copyStep strategy t mb) fun r =>
      t = j → (r.value.mapping.symm j).isSome from ?_)).mono
      fun r ⟨hr, hat⟩ => ⟨hr.1, ⟨good_nonwild hgood hr.2, outsideReady_extends hr.2 j hready⟩,
        bound_extends hr.2 j, hat⟩
  by_cases ht : t = j
  · subst t
    exact (copyStep_label strategy mb dropped hsize hgood hcount hdrop j hj hready).mono
      fun _ h _ => h
  · exact (copyStep_spec strategy t mb hsz hgood.2.1).mono fun _ _ h => (ht h).elim

theorem buildMapping_succeeds_labels_bound (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) (hsize : dropped.length = source.length)
    (hcount : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel)
    (hdrop : ∀ s : Fin source.length, source[s].isFunctionReturnLabel → dropped[s.val]? = some 0) :
    Succeeds (buildMapping source target dropped strategy) fun result =>
      ∀ j : Fin target.length, target[j].isFunctionReturnLabel → (result.mapping.symm j).isSome := by
  rw [Strategies.buildMapping_eq_phases]
  unfold Strategies.initialPasses
  simp only [bind_assoc, pure_bind]
  rw [requires_of_true _ hsize, except_ok_bind]
  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    Diagonal mb.mapping ∧ Good dropped mb) _ _ _
    ⟨diagonal_bot, rfl, bindingsValid_bot dropped, fun _ _ h => by simp at h⟩ ?_).bind
      fun mb ⟨_, hgood⟩ => ?_
  · intro j mb ⟨hdiag, hgood⟩
    have hsz : mb.dropped.length = source.length := hgood.1 ▸ hsize
    simp only [mappable_ok mb _ hsz, except_ok_bind]
    split
    · next hcond =>
      have hs := of_decide_eq_true hcond.2
      have ht := diagonal_symm_eq_none mb.mapping hdiag (Fin.castLE (min_le_left _ _) j)
        (Fin.castLE (min_le_right _ _) j) rfl hs.2
      rw [map_ok mb _ _ hs ht]
      exact ⟨diagonal_bind _ hdiag _ _ rfl hs.2 ht, hgood.1,
        bindingsValid_bind mb hgood.2.1 _ _ hs ht (Or.inr hcond.1),
        exact_bind mb hgood.2.2 _ _ hs ht hcond.1⟩
    · exact ⟨hdiag, hgood⟩
  change Succeeds ((forIn (List.finRange target.length) mb outsideStep) >>= _) _
  obtain ⟨outside, houtside, hgoodOutside⟩ := (Succeeds.forIn (Good dropped) _ mb outsideStep hgood
    (fun t mb hg => (outsideStep_spec t mb (hg.1 ▸ hsize) hg.2.1).mono
      fun _ hr => good_nonwild hg hr.2)).exists
  have hready : ∀ j : Fin target.length, target[j].isFunctionReturnLabel → OutsideReady outside j := by
    intro j hj
    have hs := outsidePass_ready mb dropped hsize hgood j (label_not_junk _ hj)
    rw [houtside] at hs
    exact hs.2
  rw [houtside, except_ok_bind]
  obtain ⟨copied, hcopied, hgoodCopied⟩ := (Succeeds.forIn (Good dropped) _ outside
    (Strategies.copyStep strategy) hgoodOutside
    (fun t mb hg => (copyStep_spec strategy t mb (hg.1 ▸ hsize) hg.2.1).mono
      fun _ hr => good_nonwild hg hr.2)).exists
  have hlabels : ∀ j : Fin target.length, target[j].isFunctionReturnLabel → (copied.mapping.symm j).isSome := by
    intro j hj
    have hs := copyPass_label strategy outside dropped hsize hgoodOutside hcount hdrop j hj (hready j hj)
    change Succeeds (forIn _ _ _) _ at hs
    rw [hcopied] at hs
    exact hs
  change Succeeds (Strategies.copyPass strategy outside >>= _) _
  rw [show Strategies.copyPass strategy outside = .ok copied from hcopied, except_ok_bind]
  refine (Strategies.suffix_succeeds copied (hgoodCopied.1 ▸ hsize)).bind fun result hr => ?_
  intro j hj
  rw [hr.2.2 j (label_not_junk _ hj)]
  exact hlabels j hj

theorem buildMapping_labels_bound_of_ok (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) {result : BuildMappingResult source target}
    (hrun : buildMapping source target dropped strategy = .ok result)
    (hcount : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel)
    (hdrop : ∀ s : Fin source.length, source[s].isFunctionReturnLabel → dropped[s.val]? = some 0) :
    ∀ j : Fin target.length, target[j].isFunctionReturnLabel → (result.mapping.symm j).isSome := by
  have hsize : dropped.length = source.length := by
    by_contra h
    simp only [buildMapping, requires, dite_eq_right h] at hrun
    cases hrun
  have hs := buildMapping_succeeds_labels_bound source target dropped strategy hsize hcount hdrop
  simpa only [hrun, succeeds_ok] using hs

/-- info: 'Shuffler.BuildMapping.buildMapping_labels_bound_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping_labels_bound_of_ok

/-- info: 'Shuffler.BuildMapping.buildMapping_labels_bound_of_ok' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques buildMapping_labels_bound_of_ok

end Shuffler.BuildMapping
