import Shuffler.Optimality.BirthPlacement.Improve
import Shuffler.Optimality.BirthPlacement.FixedWord.Theorems

namespace Shuffler.Optimality.BirthPlacement

theorem improveTraceWord_noPop (costs : PrimitiveCosts) (weights : Weights)
    (seed : Trace spills [] target) (hseed : seed.noPop) :
    (improveTraceWord costs weights seed hseed).noPop := by
  dsimp only [improveTraceWord]
  split_ifs
  · exact (optimizeTraceWord costs weights seed hseed).built.noPop
  · exact hseed

theorem improveTraceWord_births (costs : PrimitiveCosts) (weights : Weights)
    (seed : Trace spills [] target) (hseed : seed.noPop) :
    SwapRuns.births (improveTraceWord costs weights seed hseed) = SwapRuns.births seed := by
  dsimp only [improveTraceWord]
  split_ifs
  · exact optimizeTraceWord_births costs weights seed hseed
  · rfl

theorem improveTraceWord_additions (costs : PrimitiveCosts) (weights : Weights)
    (seed : Trace spills [] target) (hseed : seed.noPop) :
    (improveTraceWord costs weights seed hseed).additions = seed.additions := by
  have ha := (improveTraceWord costs weights seed hseed).noPop_balance
    (improveTraceWord_noPop costs weights seed hseed)
  have hb := seed.noPop_balance hseed
  simpa only [Multiset.coe_nil, zero_add] using ha.symm.trans hb

theorem improveTraceWord_score_le (costs : PrimitiveCosts) (weights : Weights)
    (seed : Trace spills [] target) (hseed : seed.noPop) :
    (traceCost costs (improveTraceWord costs weights seed hseed)).score weights ≤
      (traceCost costs seed).score weights := by
  dsimp only [improveTraceWord]
  split_ifs with h
  · exact h
  · exact Nat.le_refl _

theorem improveTraceWord_score_le_candidate (costs : PrimitiveCosts) (weights : Weights)
    (seed : Trace spills [] target) (hseed : seed.noPop) :
    (traceCost costs (improveTraceWord costs weights seed hseed)).score weights ≤
      (traceCost costs (optimizeTraceWord costs weights seed hseed).built.trace).score weights := by
  dsimp only [improveTraceWord]
  split_ifs with h
  · exact Nat.le_refl _
  · exact (Nat.lt_of_not_ge h).le

theorem improveTraceWord_score_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills [] target) (hseed : seed.noPop) (hother : other.noPop)
    (hword : SwapRuns.births other = SwapRuns.births seed) :
    (traceCost costs (improveTraceWord costs weights seed hseed)).score weights ≤
      2 * (traceCost costs other).score weights :=
  (improveTraceWord_score_le_candidate costs weights seed hseed).trans
    (optimizeTraceWord_score_le_twice costs weights seed other hseed hother hword)

theorem improveTraceWord_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills [] target) (hseed : seed.noPop) (hother : other.noPop)
    (hword : SwapRuns.births other = SwapRuns.births seed) :
    (traceCost costs (improveTraceWord costs weights seed hseed)).score weights -
        baseline costs weights spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills [] (target : Multiset Value)) :=
  (Nat.sub_le_sub_right (improveTraceWord_score_le_candidate costs weights seed hseed) _).trans
    (optimizeTraceWord_surplus_le_twice costs weights seed other hseed hother hword)

end Shuffler.Optimality.BirthPlacement
