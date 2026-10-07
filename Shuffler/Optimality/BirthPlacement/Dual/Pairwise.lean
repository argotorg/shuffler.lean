import Shuffler.Optimality.BirthPlacement.Dual.FullPrice
import Shuffler.Optimality.BirthPlacement.Dual.PrefixBound
import Shuffler.Optimality.BirthPlacement.Global.Theorems

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {spills : SpillSet} {target : Stack}

-- Only values with a strict direct-over-DUP premium have a copy bound.
def PairwisePremiums (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (target : Stack) : Prop :=
  ∀ index : Fin target.length,
    costs.dup.score weights < directPrice costs weights spills target[index] →
      target.count target[index] ≤ 2

instance (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (target : Stack) :
    Decidable (PairwisePremiums costs weights spills target) := by
  unfold PairwisePremiums
  infer_instance

theorem targetGap_required_pos (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (target : Stack) (index : Fin target.length) :
    0 < (targetGap costs weights spills target index).required := by
  change 0 < (target.take (index.val + 1)).count target[index]
  rw [List.take_succ_eq_append_getElem index.isLt]
  simp only [List.count_append, List.count_singleton, Fin.getElem_fin, beq_self_eq_true, ite_true]
  omega

theorem pairwise_prefixCount_le (costs : PrimitiveCosts) (weights : Weights)
    (hpair : PairwisePremiums costs weights spills target)
    (plan : Plan spills target) (index : Fin target.length)
    (hpositive : 0 < (targetGap costs weights spills target index).reward) :
    prefixCount target (targetGap costs weights spills target index) plan.assignment ≤
      (targetGap costs weights spills target index).required + 1 := by
  have hprice : costs.dup.score weights < directPrice costs weights spills target[index] := by
    simp only [targetGap] at hpositive
    split_ifs at hpositive <;> omega
  have hcount := hpair index hprice
  have hbound := targetGap_surplus_le costs weights plan index
  have hpositiveRequired := targetGap_required_pos costs weights spills target index
  change _ ≤ min 16 (target.count target[index] -
    (targetGap costs weights spills target index).required) at hbound
  omega

theorem pairwise_reward_count_eq (costs : PrimitiveCosts) (weights : Weights)
    (hpair : PairwisePremiums costs weights spills target)
    (plan : Plan spills target) (index : Fin target.length) :
    (targetGap costs weights spills target index).reward *
        prefixCount target (targetGap costs weights spills target index) plan.assignment =
      (targetGap costs weights spills target index).reward *
        ((targetGap costs weights spills target index).required + planReuse costs weights plan index) := by
  by_cases hz : (targetGap costs weights spills target index).reward = 0
  · simp only [hz, Nat.zero_mul]
  have hb := pairwise_prefixCount_le costs weights hpair plan index (Nat.pos_of_ne_zero hz)
  have hl := targetGap_required_le costs weights plan index
  unfold planReuse
  split_ifs with h
  · congr 1
    omega
  · congr 1
    omega

theorem Certificate.pairwise_attains (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hfull : cert.FullPrices (targetGap costs weights spills target))
    (hpair : PairwisePremiums costs weights spills target)
    (plan : Plan spills target)
    (hfree : ∀ index : Fin target.length, Shuffler.Placement.Free spills target[index])
    (htight : cert.TightFor (targetGap costs weights spills target)
      (costs.swap.score weights) plan.assignment) :
    cert.lowerNumerator (targetGap costs weights spills target)
        (directTotal costs weights spills target) (costs.swap.score weights) =
      cert.scale * ((plan.cheapest costs weights).jointObjective costs weights : Nat) := by
  exact cert.lower_eq_of_fullPrices hfull (plan.cheapest costs weights).assignment htight
    (planReuse costs weights (plan.cheapest costs weights))
    (pairwise_reward_count_eq costs weights hpair (plan.cheapest costs weights))
    (cheapest_generation_discount_eq costs weights plan hfree)

theorem Certificate.pairwise_globallyMinimal (cert : Certificate target.length target.length)
    (costs : PrimitiveCosts) (weights : Weights)
    (hvalid : cert.Valid (targetGap costs weights spills target) (costs.swap.score weights))
    (hfull : cert.FullPrices (targetGap costs weights spills target))
    (hpair : PairwisePremiums costs weights spills target)
    (plan : Plan spills target)
    (hfree : ∀ index : Fin target.length, Shuffler.Placement.Free spills target[index])
    (htight : cert.TightFor (targetGap costs weights spills target)
      (costs.swap.score weights) plan.assignment) :
    (plan.cheapest costs weights).GloballyMinimal costs weights := by
  apply cert.globallyMinimal costs weights hvalid
  rw [cert.pairwise_attains costs weights hfull hpair plan hfree htight]

-- This is the fixed-price assignment objective, with every optional price
-- at its full reward. No birth method or recursive stack state occurs here.
def fullPriceReward (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (target : Stack) (assignment : Equiv.Perm (Fin target.length)) : Nat :=
  costs.swap.score weights * (Word.fixed assignment).card +
    ∑ index, (targetGap costs weights spills target index).reward *
      prefixCount target (targetGap costs weights spills target index) assignment

-- An optimizer interface, not an algorithm that finds the permutation.
def FullPriceOptimal (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (target : Stack) (assignment : Equiv.Perm (Fin target.length)) : Prop :=
  ∀ other : Equiv.Perm (Fin target.length), BirthDeadlines 16 other →
    fullPriceReward costs weights spills target other ≤
      fullPriceReward costs weights spills target assignment

theorem pairwise_joint_add_reward (costs : PrimitiveCosts) (weights : Weights)
    (hpair : PairwisePremiums costs weights spills target) (plan : Plan spills target) :
    plan.jointObjective costs weights + fullPriceReward costs weights spills target plan.assignment =
      2 * eventScore costs weights spills plan.events +
        ∑ index, (targetGap costs weights spills target index).reward * planReuse costs weights plan index +
      costs.swap.score weights * target.length +
        ∑ index, (targetGap costs weights spills target index).reward *
          (targetGap costs weights spills target index).required := by
  have hf := Word.fixed_add_support plan.assignment
  have hc := congrArg (fun count => costs.swap.score weights * count) hf
  unfold Plan.jointObjective fullPriceReward
  simp_rw [pairwise_reward_count_eq costs weights hpair plan, Nat.mul_add]
  rw [Finset.sum_add_distrib]
  nlinarith

theorem pairwise_cheapest_globallyMinimal (costs : PrimitiveCosts) (weights : Weights)
    (hpair : PairwisePremiums costs weights spills target) (plan : Plan spills target)
    (hfree : ∀ index : Fin target.length, Shuffler.Placement.Free spills target[index])
    (hoptimal : FullPriceOptimal costs weights spills target plan.assignment) :
    (plan.cheapest costs weights).GloballyMinimal costs weights := by
  intro other
  have hleft := pairwise_joint_add_reward costs weights hpair (plan.cheapest costs weights)
  have hright := pairwise_joint_add_reward costs weights hpair other
  have heq := cheapest_generation_discount_eq costs weights plan hfree
  have hle := generation_discount costs weights other
  have hopt := hoptimal other.assignment other.deadlines
  change fullPriceReward costs weights spills target other.assignment ≤
    fullPriceReward costs weights spills target (plan.cheapest costs weights).assignment at hopt
  omega

theorem pairwise_cheapest_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (hpair : PairwisePremiums costs weights spills target) (plan : Plan spills target)
    (hfree : ∀ index : Fin target.length, Shuffler.Placement.Free spills target[index])
    (hoptimal : FullPriceOptimal costs weights spills target plan.assignment)
    (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs (realize (plan.cheapest costs weights)).built.trace).score weights -
        baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills [] (target : Multiset Value)) :=
  (plan.cheapest costs weights).minimum_surplus_le_twice costs weights
    (pairwise_cheapest_globallyMinimal costs weights hpair plan hfree hoptimal) other hpop

end Shuffler.Optimality.BirthPlacement.Dual
