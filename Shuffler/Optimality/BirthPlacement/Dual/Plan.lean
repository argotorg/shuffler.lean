import Shuffler.Optimality.BirthPlacement.Dual.Occurrences
import Shuffler.Optimality.BirthPlacement.RawWord.Theorems

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {target : Stack}

def targetGap (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (target : Stack) (index : Fin target.length) : Gap where
  value := target[index]
  cut := index.val + 16
  required := (target.take (index.val + 1)).count target[index]
  reward := if ∃ later : Fin target.length, index < later ∧ target[later] = target[index]
    then 2 * (directPrice costs weights spills target[index] - costs.dup.score weights) else 0

def directTotal (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (target : Stack) : Nat :=
  ∑ index : Fin target.length, directPrice costs weights spills target[index]

def planReuse (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target)
    (index : Fin target.length) : Nat :=
  if (targetGap costs weights spills target index).required <
    prefixCount target (targetGap costs weights spills target index) plan.assignment then 1 else 0

theorem planReuse_le_one (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target)
    (index : Fin target.length) : planReuse costs weights plan index ≤ 1 := by
  unfold planReuse
  split_ifs <;> omega

theorem prefixCount_eq_count (gap : Gap) (assignment : Equiv.Perm (Fin target.length)) :
    prefixCount target gap assignment = ((birthWord target assignment).take (gap.cut + 1)).count gap.value := by
  rw [birthWord, Occurrences.count_take_ofFn]
  unfold prefixCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro index _
  simp only [covers, Nat.lt_add_one_iff]

theorem targetGap_required_le (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target)
    (index : Fin target.length) :
    (targetGap costs weights spills target index).required ≤
      prefixCount target (targetGap costs weights spills target index) plan.assignment := by
  have hh := (RawWord.feasible_of_plan plan).hall target[index] (index.val + 16)
  rw [RawWord.values_positions] at hh
  change (Hall.due 16 (RawWord.positions target target[index]) (index.val + 16)).card ≤ _ at hh
  rw [RawWord.due_card, RawWord.born_card] at hh
  rw [prefixCount_eq_count]
  simpa only [targetGap, show index.val + 16 + 1 - 16 = index.val + 1 by omega] using hh

theorem planReuse_quota (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target)
    (index : Fin target.length) :
    (targetGap costs weights spills target index).required + planReuse costs weights plan index ≤
      prefixCount target (targetGap costs weights spills target index) plan.assignment := by
  have hh := targetGap_required_le costs weights plan index
  unfold planReuse
  split_ifs <;> omega

def planBirths (plan : Plan spills target) : Fin target.length → Value :=
  fun index => target[plan.assignment index]

theorem planBalanced (plan : Plan spills target) :
    Word.Balanced (planBirths plan) (fun index => target[index]) :=
  Word.balanced_of_matching plan.assignment (fun _ => rfl)

def priorTarget (plan : Plan spills target) (index : Fin target.length) : Fin target.length :=
  Occurrences.ordered (planBalanced plan) (Occurrences.previous (planBirths plan) index)

theorem dup_earlier (plan : Plan spills target) (index : Fin target.length)
    (hdup : plan.method index = .dup) :
    (Occurrences.earlier (planBirths plan) index).Nonempty := by
  have ha := plan.available index
  rw [hdup] at ha
  change (target.take (index.val - 16)).count (planBirths plan index) <
    ((List.ofFn (planBirths plan)).take index.val).count (planBirths plan index) at ha
  rw [Occurrences.count_take_ofFn] at ha
  apply Finset.card_pos.mp
  exact Nat.zero_lt_of_lt ha

theorem priorTarget_value (plan : Plan spills target) (index : Fin target.length)
    (hdup : plan.method index = .dup) : target[priorTarget plan index] = planBirths plan index := by
  exact (Occurrences.compatible (planBalanced plan) _).symm.trans
    (Occurrences.previous_value (planBirths plan) index (dup_earlier plan index hdup))

theorem priorTarget_has_later (plan : Plan spills target) (index : Fin target.length)
    (hdup : plan.method index = .dup) :
    ∃ later : Fin target.length, priorTarget plan index < later ∧
      target[later] = target[priorTarget plan index] := by
  refine ⟨Occurrences.ordered (planBalanced plan) index, ?_, ?_⟩
  · apply (Occurrences.ordered_lt_iff (planBalanced plan) _ _
      (Occurrences.previous_value (planBirths plan) index (dup_earlier plan index hdup))).mpr
    exact Occurrences.previous_lt (planBirths plan) index (dup_earlier plan index hdup)
  · rw [priorTarget_value plan index hdup]
    exact (Occurrences.compatible (planBalanced plan) index).symm

theorem priorTarget_count (plan : Plan spills target) (index : Fin target.length)
    (hdup : plan.method index = .dup) :
    (target.take ((priorTarget plan index).val + 1)).count (planBirths plan index) =
      ((birthWord target plan.assignment).take index.val).count (planBirths plan index) := by
  have he := Occurrences.count_rank_succ_eq (planBalanced plan)
    (Occurrences.previous (planBirths plan) index)
  rw [Occurrences.previous_value (planBirths plan) index (dup_earlier plan index hdup)] at he
  rw [Occurrences.count_previous (planBirths plan) index (dup_earlier plan index hdup)] at he
  have ht : (List.ofFn fun index : Fin target.length => target[index]) = target := by simp
  rw [ht, show List.ofFn (planBirths plan) = birthWord target plan.assignment from rfl] at he
  exact he.symm

theorem dup_before_prior_deadline (plan : Plan spills target) (index : Fin target.length)
    (hdup : plan.method index = .dup) : index.val ≤ (priorTarget plan index).val + 16 := by
  have ha := plan.available index
  rw [hdup] at ha
  change (target.take (index.val - 16)).count (planBirths plan index) <
    ((birthWord target plan.assignment).take index.val).count (planBirths plan index) at ha
  rw [← priorTarget_count plan index hdup] at ha
  by_contra hn
  have hm := (List.take_sublist_take_left
    (l := target) (show (priorTarget plan index).val + 1 ≤ index.val - 16 by omega)).count_le
      (planBirths plan index)
  omega

theorem priorTarget_reuse (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) (index : Fin target.length) (hdup : plan.method index = .dup) :
    planReuse costs weights plan (priorTarget plan index) = 1 := by
  have hd := dup_before_prior_deadline plan index hdup
  have hs := Occurrences.count_succ (planBirths plan) index
  change ((birthWord target plan.assignment).take (index.val + 1)).count (planBirths plan index) =
    ((birthWord target plan.assignment).take index.val).count (planBirths plan index) + 1 at hs
  have hm := (List.take_sublist_take_left (l := birthWord target plan.assignment)
    (Nat.add_le_add_right hd 1)).count_le (planBirths plan index)
  have hc := priorTarget_count plan index hdup
  have hquota : (targetGap costs weights spills target (priorTarget plan index)).required <
      prefixCount target (targetGap costs weights spills target (priorTarget plan index)) plan.assignment := by
    rw [prefixCount_eq_count]
    simp only [targetGap, priorTarget_value plan index hdup]
    omega
  simp only [planReuse, ite_eq_left hquota]

theorem priorTarget_injective (plan : Plan spills target) (first second : Fin target.length)
    (hfirst : plan.method first = .dup) (hsecond : plan.method second = .dup)
    (he : priorTarget plan first = priorTarget plan second) : first = second := by
  apply Occurrences.previous_injective (planBirths plan) first second
    (dup_earlier plan first hfirst) (dup_earlier plan second hsecond)
  exact (Occurrences.ordered (planBalanced plan)).injective he

theorem priorTarget_reward (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) (index : Fin target.length) (hdup : plan.method index = .dup) :
    (targetGap costs weights spills target (priorTarget plan index)).reward *
        planReuse costs weights plan (priorTarget plan index) =
      2 * (directPrice costs weights spills (planBirths plan index) - costs.dup.score weights) := by
  rw [priorTarget_reuse costs weights plan index hdup, Nat.mul_one]
  change (if ∃ later : Fin target.length, priorTarget plan index < later ∧
    target[later] = target[priorTarget plan index] then
      2 * (directPrice costs weights spills target[priorTarget plan index] - costs.dup.score weights)
    else 0) = _
  rw [ite_eq_left (priorTarget_has_later plan index hdup), priorTarget_value plan index hdup]

end Shuffler.Optimality.BirthPlacement.Dual
