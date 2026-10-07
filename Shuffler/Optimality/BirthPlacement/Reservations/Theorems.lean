import Shuffler.Optimality.BirthPlacement.Reservations

namespace Shuffler.Optimality.BirthPlacement.Reservations

theorem load_mono (hsub : first ⊆ second) : load reach first cut ≤ load reach second cut :=
  Finset.card_le_card (Finset.filter_subset_filter _ hsub)

theorem load_insert (hnot : start ∉ selected) :
    load reach (insert start selected) cut =
      load reach selected cut + if Covers reach start cut then 1 else 0 := by
  by_cases hc : Covers reach start cut
  · simp [load, Finset.filter_insert, hc, hnot]
  · simp [load, Finset.filter_insert, hc]

theorem feasible_insert_iff (hnot : start ∉ selected) :
    Feasible reach capacity (insert start selected) ↔
      Available reach capacity start ∧ Feasible reach (reserve reach capacity start) selected := by
  constructor
  · intro hf
    constructor
    · intro cut hc
      have hcov : Covers reach start cut := Finset.mem_Ico.mp hc
      have ht := hf cut
      rw [load_insert hnot, ite_eq_left hcov] at ht
      omega
    · intro cut
      have ht := hf cut
      rw [load_insert hnot] at ht
      unfold reserve
      split_ifs at ht ⊢ <;> omega
  · rintro ⟨ha, hf⟩ cut
    have ht := hf cut
    change load reach selected cut ≤ capacity cut - if Covers reach start cut then 1 else 0 at ht
    rw [load_insert hnot]
    by_cases hc : Covers reach start cut
    · have hp := ha cut (Finset.mem_Ico.mpr hc)
      simp only [hc, ite_true] at ht ⊢
      omega
    · simpa only [hc, ite_false, Nat.sub_zero, Nat.add_zero] using ht

theorem feasible_erase (hf : Feasible reach capacity selected) :
    Feasible reach capacity (selected.erase start) := by
  intro cut
  exact (load_mono (Finset.erase_subset _ _)).trans (hf cut)

theorem available_of_mem (hf : Feasible reach capacity selected) (hm : start ∈ selected) :
    Available reach capacity start := by
  rw [← Finset.insert_erase hm] at hf
  exact (feasible_insert_iff (Finset.notMem_erase _ _)).mp hf |>.1

theorem select_subset (reach : Nat) (capacity : Nat → Nat) (candidates : List Nat) :
    select reach capacity candidates ⊆ candidates.toFinset := by
  induction candidates generalizing capacity with
  | nil => simp [select]
  | cons start rest ih =>
      simp only [List.toFinset_cons]
      unfold select
      split_ifs
      · exact Finset.insert_subset_insert _ (ih _)
      · exact (ih _).trans (Finset.subset_insert _ _)

theorem select_feasible (reach : Nat) (capacity : Nat → Nat) (candidates : List Nat)
    (hnodup : candidates.Nodup) : Feasible reach capacity (select reach capacity candidates) := by
  induction candidates generalizing capacity with
  | nil => simp [select, Feasible, load]
  | cons start rest ih =>
      have hn := List.nodup_cons.mp hnodup
      unfold select
      split_ifs with ha
      · apply (feasible_insert_iff ?_).mpr ⟨ha, ih _ hn.2⟩
        intro hm
        exact hn.1 (List.mem_toFinset.mp (select_subset _ _ _ hm))
      · exact ih _ hn.2

-- Replace the earliest chosen interval by an available earlier interval.
-- Before the chosen start, only the earlier interval can contribute. After
-- that start, its end is no later than the end of the replaced interval.
theorem exchange_first (hf : Feasible reach capacity selected)
    (ha : Available reach capacity start) (hm : first ∈ selected)
    (hstart : start ≤ first) (hfirst : ∀ other ∈ selected, first ≤ other)
    (hnot : start ∉ selected) :
    Feasible reach capacity (insert start (selected.erase first)) := by
  have hn : start ∉ selected.erase first := fun h => hnot (Finset.mem_of_mem_erase h)
  intro cut
  rw [load_insert hn]
  by_cases hs : Covers reach start cut
  · rw [ite_eq_left hs]
    by_cases hh : Covers reach first cut
    · have he : load reach selected cut = load reach (selected.erase first) cut + 1 := by
        conv_lhs => rw [← Finset.insert_erase hm]
        rw [load_insert (Finset.notMem_erase _ _), ite_eq_left hh]
      exact he ▸ hf cut
    · have hcut : cut < first := by
        unfold Covers at hs hh
        omega
      have hz : load reach (selected.erase first) cut = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro other ho hc
        have hl := hfirst other (Finset.mem_of_mem_erase ho)
        have hp := hc.1
        omega
      have hp := ha cut (Finset.mem_Ico.mpr hs)
      omega
  · rw [ite_eq_right hs, Nat.add_zero]
    exact feasible_erase hf cut

theorem select_optimal (reach : Nat) (capacity : Nat → Nat) (candidates : List Nat)
    (hsorted : candidates.Pairwise (· < ·)) (selected : Finset Nat)
    (hsub : selected ⊆ candidates.toFinset) (hf : Feasible reach capacity selected) :
    selected.card ≤ (select reach capacity candidates).card := by
  induction candidates generalizing capacity selected with
  | nil =>
      have he : selected = ∅ := Finset.subset_empty.mp hsub
      simp [he, select]
  | cons start rest ih =>
      have hp := List.pairwise_cons.mp hsorted
      have hn : start ∉ rest := by
        intro hm
        exact (Nat.lt_irrefl start) (hp.1 start hm)
      have hselected_not_mem (cap : Nat → Nat) : start ∉ select reach cap rest := by
        intro hm
        exact hn (List.mem_toFinset.mp (select_subset _ _ _ hm))
      unfold select
      split_ifs with ha
      · rw [Finset.card_insert_of_notMem (hselected_not_mem _)]
        by_cases hm : start ∈ selected
        · have hrest : selected.erase start ⊆ rest.toFinset := by
            intro other ho
            have hc := hsub (Finset.mem_of_mem_erase ho)
            simp only [List.toFinset_cons, Finset.mem_insert] at hc
            exact hc.resolve_left (Finset.mem_erase.mp ho).1
          have hfeas : Feasible reach (reserve reach capacity start) (selected.erase start) := by
            have he : Feasible reach capacity (insert start (selected.erase start)) := by
              simpa only [Finset.insert_erase hm] using hf
            exact ((feasible_insert_iff (Finset.notMem_erase _ _)).mp he).2
          have hi := ih (reserve reach capacity start) hp.2 (selected.erase start) hrest hfeas
          have hc := Finset.card_erase_add_one hm
          omega
        · have hrest : selected ⊆ rest.toFinset := by
            intro other ho
            have hc := hsub ho
            simp only [List.toFinset_cons, Finset.mem_insert] at hc
            rcases hc with he | hc
            · exact False.elim (hm (he ▸ ho))
            · exact hc
          by_cases hne : selected.Nonempty
          · let first := selected.min' hne
            have hfirst : first ∈ selected := Finset.min'_mem _ _
            have hstart : start ≤ first := Nat.le_of_lt (hp.1 _ (List.mem_toFinset.mp (hrest hfirst)))
            have hlow : ∀ other ∈ selected, first ≤ other := fun other ho => Finset.min'_le _ _ ho
            have he := exchange_first hf ha hfirst hstart hlow hm
            have hfeas := ((feasible_insert_iff (show start ∉ selected.erase first from
              fun h => hm (Finset.mem_of_mem_erase h))).mp he).2
            have hi := ih (reserve reach capacity start) hp.2 (selected.erase first)
              ((Finset.erase_subset _ _).trans hrest) hfeas
            have hc := Finset.card_erase_add_one hfirst
            omega
          · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
            simp [hz]
      · have hm : start ∉ selected := fun h => ha (available_of_mem hf h)
        have hrest : selected ⊆ rest.toFinset := by
          intro other ho
          have hc := hsub ho
          simp only [List.toFinset_cons, Finset.mem_insert] at hc
          rcases hc with he | hc
          · exact False.elim (hm (he ▸ ho))
          · exact hc
        exact ih capacity hp.2 selected hrest hf

end Shuffler.Optimality.BirthPlacement.Reservations
