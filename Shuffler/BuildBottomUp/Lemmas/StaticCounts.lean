import Shuffler.BuildBottomUp.Lemmas.StaticPermutation

namespace Shuffler.BuildBottomUp.Static

theorem generatedBefore_le (initial : State source target spills) (cursor : Nat) :
    generatedBefore initial cursor ≤ initial.mapping.unmapped_target_slots :=
  Finset.card_filter_le _ _

theorem prefixLength_le (initial : State source target spills) (h : initial.Valid) (cursor : Nat) :
    prefixLength initial cursor ≤ target.length := by
  have := generatedBefore_le initial cursor
  have := h.size
  have := h.pending
  unfold prefixLength
  omega

theorem generatedBefore_succ_of_bound (initial : State source target spills)
    (cursor : Nat) (hc : cursor < target.length)
    (hb : (initial.mapping.symm ⟨cursor, hc⟩).isSome) :
    generatedBefore initial (cursor + 1) = generatedBefore initial cursor := by
  unfold generatedBefore
  congr 1
  ext j
  simp only [Finset.mem_filter, mem_holes]
  constructor
  · rintro ⟨hj, hlt⟩
    refine ⟨hj, ?_⟩
    by_contra hn
    have heq : j = ⟨cursor, hc⟩ := Fin.ext (show j.val = cursor by omega)
    subst j
    simp [hj] at hb
  · rintro ⟨hj, hlt⟩
    exact ⟨hj, by omega⟩

theorem generatedBefore_succ_of_hole (initial : State source target spills)
    (cursor : Nat) (hc : cursor < target.length)
    (hb : initial.mapping.symm ⟨cursor, hc⟩ = none) :
    generatedBefore initial (cursor + 1) = generatedBefore initial cursor + 1 := by
  have hset : (holes initial).filter (fun j => j.val < cursor + 1) =
      insert ⟨cursor, hc⟩ ((holes initial).filter (fun j => j.val < cursor)) := by
    ext j
    simp only [Finset.mem_filter, mem_holes, Finset.mem_insert, Fin.ext_iff]
    constructor
    · rintro ⟨hj, hlt⟩
      by_cases heq : j.val = cursor
      · exact Or.inl heq
      · exact Or.inr ⟨hj, by omega⟩
    · rintro (heq | ⟨hj, hlt⟩)
      · have he : j = ⟨cursor, hc⟩ := Fin.ext heq
        subst j
        exact ⟨hb, by simp⟩
      · exact ⟨hj, by omega⟩
  unfold generatedBefore
  rw [hset, Finset.card_insert_of_notMem (by simp)]

theorem generationEnd_le (initial : State source target spills) :
    generationEnd initial ≤ target.length := by
  apply Finset.sup_le
  intro j _
  have := j.isLt
  omega

theorem hole_before_generationEnd (initial : State source target spills)
    (j : Fin target.length) (hj : j ∈ holes initial) : j.val < generationEnd initial := by
  have h := Finset.le_sup (s := holes initial) (f := fun j => j.val + 1) hj
  unfold generationEnd
  omega

theorem generatedBefore_generationEnd (initial : State source target spills) :
    generatedBefore initial (generationEnd initial) = initial.mapping.unmapped_target_slots := by
  unfold generatedBefore
  have heq : (holes initial).filter (fun j => j.val < generationEnd initial) = holes initial := by
    apply Finset.filter_eq_self.mpr
    exact fun j hj => hole_before_generationEnd initial j hj
  rw [heq]
  rfl

theorem prefixLength_generationEnd (initial : State source target spills) (h : initial.Valid) :
    prefixLength initial (generationEnd initial) = target.length := by
  rw [prefixLength, generatedBefore_generationEnd, h.pending]
  exact h.size


private theorem card_fin_below {n c : Nat} (hc : c ≤ n) :
    (Finset.univ.filter (fun j : Fin n => j.val < c)).card = c := by
  calc
    _ = (Finset.univ : Finset (Fin c)).card := by
      apply Finset.card_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin c))
      · intro j hj; exact Finset.mem_univ _
      · intro j hj k hk he; exact Fin.ext (congrArg (fun i : Fin c => i.val) he)
      · intro k hk
        refine ⟨⟨k.val, by omega⟩, ?_, ?_⟩
        · simp [k.isLt]
        · rfl
    _ = c := by simp

private theorem rank_sorted {α : Type*} [LinearOrder α] (s : Finset α) (i : Fin s.card) :
    (s.filter (fun j => j < s.orderEmbOfFin rfl i)).card = i.val := by
  let e := s.orderEmbOfFin rfl
  have hm : (Finset.univ.map e.toEmbedding) = s := Finset.map_orderEmbOfFin_univ s rfl
  calc
    (s.filter (fun j => j < e i)).card =
        ((Finset.univ.map e.toEmbedding).filter (fun j => j < e i)).card := by rw [hm]
    _ = (Finset.univ.filter (fun j : Fin s.card => j < i)).card := by
      rw [Finset.filter_map, Finset.card_map]
      congr 1
      ext j
      simp
    _ = i.val := by
      change (Finset.univ.filter (fun j : Fin s.card => j.val < i.val)).card = i.val
      exact card_fin_below (Nat.le_of_lt i.isLt)

-- Counting assigned positions makes the width independent of prior generation.
def boundBefore (initial : State source target spills) (cursor : Nat) : Nat :=
  ((boundTargets initial).filter (fun j => j.val < cursor)).card

theorem generatedBefore_add_boundBefore (initial : State source target spills)
    (cursor : Nat) (hc : cursor ≤ target.length) :
    generatedBefore initial cursor + boundBefore initial cursor = cursor := by
  have he := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun j : Fin target.length => j.val < cursor))
    (fun j => initial.mapping.symm j = none)
  rw [card_fin_below hc] at he
  simpa only [generatedBefore, boundBefore, holes, boundTargets, Finset.filter_filter,
    Option.isSome_iff_ne_none, and_comm] using he

theorem prefixWidth_eq (initial : State source target spills)
    (cursor : Nat) (hc : cursor ≤ target.length) :
    prefixLength initial cursor - cursor = initial.stack.length - boundBefore initial cursor := by
  have := generatedBefore_add_boundBefore initial cursor hc
  unfold prefixLength
  omega

theorem boundary_data (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) :
    ∃ t : Fin target.length, t.val = boundary initial ∧
      t ∈ boundTargets initial ∧ boundBefore initial t.val = initial.stack.length - 17 := by
  let s := boundTargets initial
  have hk : initial.stack.length - 17 < s.card := by
    rw [boundTargets_card initial h]
    omega
  let k : Fin s.card := ⟨initial.stack.length - 17,hk⟩
  let t := s.orderEmbOfFin rfl k
  refine ⟨t, ?_, Finset.orderEmbOfFin_mem s rfl k, ?_⟩
  · have hlist : initial.stack.length - 17 < (boundList initial).length := by
      simpa only [s, boundTargets, boundList, Finset.length_sort] using hk
    simp only [boundary, MAX_SWAP_DEPTH, Nat.reduceAdd, List.getElem?_eq_getElem hlist,
      Option.map_some, Option.getD_some]
    rfl
  · exact rank_sorted s k

theorem boundary_lt (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) : boundary initial < target.length := by
  obtain ⟨t, ht, _, _⟩ := boundary_data initial h hn
  rw [← ht]
  exact t.isLt

theorem boundary_bound (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) :
    (initial.mapping.symm ⟨boundary initial, boundary_lt initial h hn⟩).isSome := by
  obtain ⟨t, ht, hb, _⟩ := boundary_data initial h hn
  have he : (⟨boundary initial, boundary_lt initial h hn⟩ : Fin target.length) = t := Fin.ext ht.symm
  rw [he]
  simpa [boundTargets] using hb

theorem prefixWidth_boundary (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) : prefixLength initial (boundary initial) - boundary initial = 17 := by
  obtain ⟨t, ht, _, hrank⟩ := boundary_data initial h hn
  rw [← ht, prefixWidth_eq initial t.val t.isLt.le, hrank]
  omega

theorem boundBefore_le_boundary (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) (cursor : Nat) (hc : cursor ≤ boundary initial) :
    boundBefore initial cursor ≤ initial.stack.length - 17 := by
  obtain ⟨t, ht, _, hrank⟩ := boundary_data initial h hn
  rw [← hrank]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, by omega⟩

theorem prefixWidth_ge_seventeen (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) (cursor : Nat) (hc : cursor ≤ boundary initial) :
    17 ≤ prefixLength initial cursor - cursor := by
  have hbound := boundBefore_le_boundary initial h hn cursor hc
  have hlt := boundary_lt initial h hn
  rw [prefixWidth_eq initial cursor (by omega)]
  omega

theorem boundBefore_lt_boundary_of_bound (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) (cursor : Fin target.length)
    (hc : cursor.val < boundary initial) (hb : (initial.mapping.symm cursor).isSome) :
    boundBefore initial cursor.val < initial.stack.length - 17 := by
  obtain ⟨t, ht, _, hrank⟩ := boundary_data initial h hn
  have hsub : insert cursor ((boundTargets initial).filter (fun j => j.val < cursor.val)) ⊆
      (boundTargets initial).filter (fun j => j.val < t.val) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_filter] at hj ⊢
    rcases hj with rfl | hj
    · exact ⟨by simpa [boundTargets] using hb, by omega⟩
    · exact ⟨hj.1, by omega⟩
  have he := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp)] at he
  change boundBefore initial cursor.val + 1 ≤ boundBefore initial t.val at he
  omega

theorem prefixWidth_ge_eighteen_of_bound (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) (cursor : Fin target.length)
    (hc : cursor.val < boundary initial) (hb : (initial.mapping.symm cursor).isSome) :
    18 ≤ prefixLength initial cursor.val - cursor.val := by
  have := boundBefore_lt_boundary_of_bound initial h hn cursor hc hb
  rw [prefixWidth_eq initial cursor.val cursor.isLt.le]
  omega

theorem remaining_hole_of_lt_generationEnd (initial : State source target spills)
    (cursor : Nat) (hc : cursor < generationEnd initial) :
    ∃ j ∈ holes initial, cursor ≤ j.val := by
  by_contra hn
  push Not at hn
  have he : generationEnd initial ≤ cursor := by
    apply Finset.sup_le
    intro j hj
    have := hn j hj
    omega
  omega

theorem generatedBefore_lt_pending (initial : State source target spills) (h : initial.Valid)
    (cursor : Nat) (hc : cursor < generationEnd initial) :
    generatedBefore initial cursor < initial.pending_generations := by
  obtain ⟨j, hj, hge⟩ := remaining_hole_of_lt_generationEnd initial cursor hc
  have hproper : (holes initial).filter (fun j => j.val < cursor) ⊂ holes initial := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hm : j ∈ (holes initial).filter (fun j => j.val < cursor) := he.symm ▸ hj
    simp only [Finset.mem_filter] at hm
    omega
  have he := Finset.card_lt_card hproper
  change generatedBefore initial cursor < initial.mapping.unmapped_target_slots at he
  rwa [h.pending] at he


theorem holeList_generatedBefore (initial : State source target spills)
    (j : Fin target.length) (hj : j ∈ holes initial) :
    (holeList initial)[generatedBefore initial j.val]? = some j := by
  let s := holes initial
  let hole : s := ⟨j,hj⟩
  let k : Fin s.card := (s.orderIsoOfFin rfl).symm hole
  have he : s.orderEmbOfFin rfl k = j :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply hole)
  have hr : generatedBefore initial j.val = k.val := by
    change (s.filter (fun i => i < j)).card = k.val
    rw [← he]
    exact rank_sorted s k
  have hk : k.val < (holeList initial).length := by
    simpa only [holeList, Finset.length_sort] using k.isLt
  rw [hr, List.getElem?_eq_getElem hk]
  exact congrArg some he


-- The next appended coordinate has the value of the next original hole.
theorem augmentedStack_get_hole (initial : State source target spills)
    (j : Fin target.length) (hj : j ∈ holes initial) :
    (augmentedStack initial)[initial.stack.length + generatedBefore initial j.val]? = some target[j] := by
  rw [augmentedStack, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_map, holeList_generatedBefore initial j hj]
  rfl

theorem augmentedStack_take_succ_hole (initial : State source target spills)
    (cursor : Nat) (hc : cursor < target.length)
    (hb : initial.mapping.symm ⟨cursor,hc⟩ = none) :
    (augmentedStack initial).take (prefixLength initial (cursor+1)) =
      (augmentedStack initial).take (prefixLength initial cursor) ++ [target[cursor]] := by
  have hlen : prefixLength initial (cursor+1) = prefixLength initial cursor + 1 := by
    simp only [prefixLength, generatedBefore_succ_of_hole initial cursor hc hb]
    omega
  rw [hlen, List.take_add_one]
  have hvalue := augmentedStack_get_hole initial ⟨cursor,hc⟩ ((mem_holes initial _).mpr hb)
  change (augmentedStack initial)[prefixLength initial cursor]? = some target[cursor] at hvalue
  rw [hvalue]
  rfl

end Shuffler.BuildBottomUp.Static
