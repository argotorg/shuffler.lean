import Shuffler.Optimality.Collective.UnitSchedule
import Mathlib.Data.List.Sort

namespace Shuffler.Optimality.Collective

theorem unitOrder_perm (jobs : List α) (deadline : α → Int) :
    (unitOrder jobs deadline).Perm jobs := List.mergeSort_perm _ _

theorem unitOrder_sorted (jobs : List α) (deadline : α → Int) :
    (unitOrder jobs deadline).Pairwise fun left right => deadline left ≤ deadline right := by
  have ht : ∀ left middle right : α,
      decide (deadline left ≤ deadline middle) = true →
      decide (deadline middle ≤ deadline right) = true →
      decide (deadline left ≤ deadline right) = true := by
    intro left middle right hl hr
    simpa only [decide_eq_true_eq] using (of_decide_eq_true hl).trans (of_decide_eq_true hr)
  have hall : ∀ left right : α,
      (decide (deadline left ≤ deadline right) || decide (deadline right ≤ deadline left)) = true := by
    intro left right
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total _ _
  simpa only [unitOrder, decide_eq_true_eq] using List.pairwise_mergeSort ht hall jobs

theorem UnitCapacity.deadline_pos [DecidableEq α] (hcapacity : UnitCapacity jobs deadline)
    (job : α) (hmem : job ∈ jobs) : 0 < deadline job := by
  by_contra hn
  have hzero := hcapacity 0
  change (jobs.toFinset.filter fun item => deadline item ≤ (0 : Int)).card ≤ 0 at hzero
  have hj : job ∈ jobs.toFinset.filter (fun item => deadline item ≤ (0 : Int)) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, by omega⟩
  have hp := Finset.card_pos.mpr ⟨job, hj⟩
  omega

theorem meetsDeadlines_of_sorted [DecidableEq α] (jobs order : List α)
    (deadline : α → Int) (hperm : order.Perm jobs) (hnodup : jobs.Nodup)
    (hsorted : order.Pairwise fun left right => deadline left ≤ deadline right)
    (hcapacity : UnitCapacity jobs deadline) : MeetsDeadlines deadline order := by
  intro index
  have hmem : order[index] ∈ jobs := hperm.mem_iff.mp (List.getElem_mem index.isLt)
  have hpositive := hcapacity.deadline_pos _ hmem
  have htime : (deadline order[index]).toNat = deadline order[index] := by omega
  let before := (order.take (index.val + 1)).toFinset
  have hsub : before ⊆ jobs.toFinset.filter
      (fun job => deadline job ≤ ((deadline order[index]).toNat : Int)) := by
    intro job hj
    have hm := List.mem_toFinset.mp hj
    obtain ⟨position, hp, he⟩ := List.mem_take_iff_getElem.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr (hperm.mem_iff.mp (List.mem_of_mem_take hm)), ?_⟩
    rw [htime, ← he]
    by_cases hlt : position < index.val
    · exact List.pairwise_iff_getElem.mp hsorted position index.val (by omega) index.isLt hlt
    · have heq : position = index.val := by omega
      subst position
      exact le_refl _
  have hc := (Finset.card_le_card hsub).trans (hcapacity (deadline order[index]).toNat)
  have hb : before.card = index.val + 1 := by
    rw [List.toFinset_card_of_nodup ((hperm.nodup_iff.mpr hnodup).take),
      List.length_take, Nat.min_eq_left (by omega)]
  rw [hb] at hc
  omega

theorem unitOrder_meetsDeadlines [DecidableEq α] (jobs : List α) (deadline : α → Int)
    (hnodup : jobs.Nodup) (hcapacity : UnitCapacity jobs deadline) :
    MeetsDeadlines deadline (unitOrder jobs deadline) :=
  meetsDeadlines_of_sorted jobs _ deadline (unitOrder_perm jobs deadline) hnodup
    (unitOrder_sorted jobs deadline) hcapacity

theorem unitCapacity_of_meetsDeadlines [DecidableEq α] (jobs order : List α)
    (deadline : α → Int) (hperm : order.Perm jobs)
    (hmeets : MeetsDeadlines deadline order) : UnitCapacity jobs deadline := by
  intro time
  have hsub : (jobs.toFinset.filter fun job => deadline job ≤ (time : Int)) ⊆
      (order.take time).toFinset := by
    intro job hj
    have hm : job ∈ order := hperm.mem_iff.mpr
      (List.mem_toFinset.mp (Finset.mem_filter.mp hj).1)
    obtain ⟨position, hp, he⟩ := List.mem_iff_getElem.mp hm
    have hd := hmeets ⟨position, hp⟩
    simp only [Fin.getElem_fin] at hd
    rw [he] at hd
    have hlimit := (Finset.mem_filter.mp hj).2
    apply List.mem_toFinset.mpr
    exact List.mem_take_iff_getElem.mpr ⟨position, by omega, he⟩
  exact (Finset.card_le_card hsub).trans
    ((List.toFinset_card_le _).trans (List.length_take_le _ _))

theorem unitCapacity_iff_exists_order [DecidableEq α] (jobs : List α) (deadline : α → Int)
    (hnodup : jobs.Nodup) :
    UnitCapacity jobs deadline ↔
      ∃ order, order.Perm jobs ∧ MeetsDeadlines deadline order := by
  constructor
  · intro hc
    exact ⟨unitOrder jobs deadline, unitOrder_perm jobs deadline,
      unitOrder_meetsDeadlines jobs deadline hnodup hc⟩
  · rintro ⟨order, hp, hm⟩
    exact unitCapacity_of_meetsDeadlines jobs order deadline hp hm

theorem unitCapacity_iff_jobBounds [DecidableEq α] (jobs : List α) (deadline : α → Int) :
    UnitCapacity jobs deadline ↔ ∀ job ∈ jobs,
      ((jobs.toFinset.filter fun other => deadline other ≤ deadline job).card : Int) ≤
        deadline job := by
  constructor
  · intro hc job hj
    have hp := hc.deadline_pos job hj
    have he : ((deadline job).toNat : Int) = deadline job := by omega
    have hh := hc (deadline job).toNat
    rw [he] at hh
    omega
  · intro hc time
    let due := jobs.toFinset.filter fun job => deadline job ≤ (time : Int)
    by_cases hn : due.Nonempty
    · let deadlines := due.image deadline
      have hne : deadlines.Nonempty := hn.image deadline
      obtain ⟨job, hj, he⟩ := Finset.mem_image.mp (Finset.max'_mem deadlines hne)
      have hm : job ∈ jobs := List.mem_toFinset.mp (Finset.mem_filter.mp hj).1
      have hb := hc job hm
      have ht := (Finset.mem_filter.mp hj).2
      have hs : due ⊆ jobs.toFinset.filter (fun other => deadline other ≤ deadline job) := by
        intro other ho
        apply Finset.mem_filter.mpr
        refine ⟨(Finset.mem_filter.mp ho).1, ?_⟩
        rw [he]
        exact Finset.le_max' deadlines (deadline other) (Finset.mem_image.mpr ⟨other, ho, rfl⟩)
      have hcard := Finset.card_le_card hs
      change due.card ≤ time
      omega
    · have hz : due = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      change due.card ≤ time
      rw [hz, Finset.card_empty]
      exact Nat.zero_le _

end Shuffler.Optimality.Collective
