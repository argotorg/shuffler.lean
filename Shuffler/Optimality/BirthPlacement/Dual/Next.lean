import Shuffler.Optimality.BirthPlacement.Dual.Plan

namespace Shuffler.Optimality.BirthPlacement.Dual.Occurrences

variable {α : Type*} [DecidableEq α] {size : Nat}

def later (word : Fin size → α) (index : Fin size) : Finset (Fin size) :=
  Finset.univ.filter fun other => index < other ∧ word other = word index

def next (word : Fin size → α) (index : Fin size) : Fin size :=
  if h : (later word index).Nonempty then (later word index).min' h else index

theorem next_mem (word : Fin size → α) (index : Fin size)
    (h : (later word index).Nonempty) : next word index ∈ later word index := by
  simpa only [next, dite_eq_left h] using Finset.min'_mem (later word index) h

theorem lt_next (word : Fin size → α) (index : Fin size)
    (h : (later word index).Nonempty) : index < next word index :=
  (Finset.mem_filter.mp (next_mem word index h)).2.1

theorem next_value (word : Fin size → α) (index : Fin size)
    (h : (later word index).Nonempty) : word (next word index) = word index :=
  (Finset.mem_filter.mp (next_mem word index h)).2.2

theorem next_le (word : Fin size → α) (index other : Fin size)
    (h : other ∈ later word index) : next word index ≤ other := by
  have hn : (later word index).Nonempty := ⟨other, h⟩
  simpa only [next, dite_eq_left hn] using Finset.min'_le (later word index) other h

theorem earlier_next (word : Fin size → α) (index : Fin size)
    (h : (later word index).Nonempty) : (earlier word (next word index)).Nonempty := by
  exact ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_next word index h,
    (next_value word index h).symm⟩⟩

theorem previous_next (word : Fin size → α) (index : Fin size)
    (h : (later word index).Nonempty) : previous word (next word index) = index := by
  have he := earlier_next word index h
  apply le_antisymm
  · by_contra hn
    have hm : previous word (next word index) ∈ later word index := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, lt_of_not_ge hn,
        (previous_value word (next word index) he).trans (next_value word index h)⟩
    exact (not_le_of_gt (previous_lt word (next word index) he)) (next_le word index _ hm)
  · apply le_previous
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_next word index h,
      (next_value word index h).symm⟩

end Shuffler.Optimality.BirthPlacement.Dual.Occurrences

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {target : Stack}

def followingBirth (plan : Plan spills target) (index : Fin target.length) : Fin target.length :=
  Occurrences.next (planBirths plan) ((Occurrences.ordered (planBalanced plan)).symm index)

theorem matchedBirth_later (plan : Plan spills target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index]) :
    (Occurrences.later (planBirths plan)
      ((Occurrences.ordered (planBalanced plan)).symm index)).Nonempty := by
  obtain ⟨later, hlt, hv⟩ := hlater
  let matching := Occurrences.ordered (planBalanced plan)
  have hleft : planBirths plan (matching.symm index) = target[index] := by
    simpa only [matching, Equiv.apply_symm_apply] using
      Occurrences.compatible (planBalanced plan) (matching.symm index)
  have hright : planBirths plan (matching.symm later) = target[later] := by
    simpa only [matching, Equiv.apply_symm_apply] using
      Occurrences.compatible (planBalanced plan) (matching.symm later)
  refine ⟨matching.symm later, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
  · apply (Occurrences.ordered_lt_iff (planBalanced plan) _ _ (by rw [hleft, hright, hv])).mp
    simpa only [matching, Equiv.apply_symm_apply] using hlt
  · rw [hleft, hright, hv]

theorem followingBirth_earlier (plan : Plan spills target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index]) :
    (Occurrences.earlier (planBirths plan) (followingBirth plan index)).Nonempty :=
  Occurrences.earlier_next _ _ (matchedBirth_later plan index hlater)

theorem followingBirth_prior (plan : Plan spills target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index]) :
    priorTarget plan (followingBirth plan index) = index := by
  unfold priorTarget followingBirth
  rw [Occurrences.previous_next _ _ (matchedBirth_later plan index hlater)]
  exact Equiv.apply_symm_apply _ _

theorem followingBirth_value (plan : Plan spills target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index]) :
    planBirths plan (followingBirth plan index) = target[index] := by
  rw [followingBirth, Occurrences.next_value _ _ (matchedBirth_later plan index hlater)]
  simpa only [Equiv.apply_symm_apply] using Occurrences.compatible (planBalanced plan)
    ((Occurrences.ordered (planBalanced plan)).symm index)

theorem priorTarget_count_of_earlier (plan : Plan spills target) (index : Fin target.length)
    (h : (Occurrences.earlier (planBirths plan) index).Nonempty) :
    (target.take ((priorTarget plan index).val + 1)).count (planBirths plan index) =
      ((birthWord target plan.assignment).take index.val).count (planBirths plan index) := by
  have he := Occurrences.count_rank_succ_eq (planBalanced plan)
    (Occurrences.previous (planBirths plan) index)
  rw [Occurrences.previous_value (planBirths plan) index h] at he
  rw [Occurrences.count_previous (planBirths plan) index h] at he
  have ht : (List.ofFn fun index : Fin target.length => target[index]) = target := by simp
  rw [ht, show List.ofFn (planBirths plan) = birthWord target plan.assignment from rfl] at he
  exact he.symm

theorem followingBirth_available (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) (index : Fin target.length)
    (hlater : ∃ later : Fin target.length, index < later ∧ target[later] = target[index])
    (hreuse : planReuse costs weights plan index = 1) :
    BirthAvailable spills target (birthWord target plan.assignment) (followingBirth plan index).val
      (planBirths plan (followingBirth plan index)) .dup := by
  have he := followingBirth_earlier plan index hlater
  have hc := priorTarget_count_of_earlier plan (followingBirth plan index) he
  rw [followingBirth_prior plan index hlater, followingBirth_value plan index hlater] at hc
  have hquota : (target.take (index.val + 1)).count target[index] <
      ((birthWord target plan.assignment).take (index.val + 16 + 1)).count target[index] := by
    unfold planReuse at hreuse
    split_ifs at hreuse with h
    · simpa only [prefixCount_eq_count, targetGap] using h
  have hd : (followingBirth plan index).val ≤ index.val + 16 := by
    by_contra hn
    have hm := (List.take_sublist_take_left (l := birthWord target plan.assignment)
      (show index.val + 16 + 1 ≤ (followingBirth plan index).val by omega)).count_le target[index]
    omega
  have hs : (target.take (index.val + 1)).count target[index] =
      (target.take index.val).count target[index] + 1 := by
    rw [List.take_succ_eq_append_getElem index.isLt]
    simp only [List.count_append, List.count_singleton, Fin.getElem_fin, beq_self_eq_true, ite_true]
  have hm := (List.take_sublist_take_left (l := target)
    (show (followingBirth plan index).val - 16 ≤ index.val by omega)).count_le target[index]
  change (target.take ((followingBirth plan index).val - 16)).count _ <
    ((birthWord target plan.assignment).take (followingBirth plan index).val).count _
  rw [followingBirth_value plan index hlater]
  omega

end Shuffler.Optimality.BirthPlacement.Dual
