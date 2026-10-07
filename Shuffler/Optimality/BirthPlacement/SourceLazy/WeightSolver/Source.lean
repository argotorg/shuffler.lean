import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

def reassign (plan : SourcePlan spills source target)
    (result : Solution 16 source.length (fun i => target[plan.assignment i]) (fun i => target[i])) :
    SourcePlan spills source target :=
  have hvalues : ∀ i, target[result.assignment i] = target[plan.assignment i] :=
    fun i => (result.allowed i).1.symm
  have hword : birthWord target result.assignment = birthWord target plan.assignment :=
    congrArg List.ofFn (funext hvalues)
  { source_length := plan.source_length
    assignment := result.assignment
    source_values := by
      change (birthWord target result.assignment).take source.length = source
      rw [hword]
      exact plan.source_values
    deadlines := fun i => (result.allowed i).2.1
    source_frozen := fun i hi => (result.allowed i).2.2 hi
    method := plan.method
    available := by
      intro index
      rw [hword, hvalues]
      exact plan.available index }

@[simp] theorem reassign_assignment (plan : SourcePlan spills source target)
    (result : Solution 16 source.length (fun i => target[plan.assignment i]) (fun i => target[i])) :
    (reassign plan result).assignment = result.assignment := rfl

@[simp] theorem reassign_births (plan : SourcePlan spills source target)
    (result : Solution 16 source.length (fun i => target[plan.assignment i]) (fun i => target[i])) :
    (reassign plan result).births = plan.births := by
  have hw : birthWord target result.assignment = birthWord target plan.assignment :=
    congrArg List.ofFn (funext fun i => (result.allowed i).1.symm)
  change (birthWord target result.assignment).drop source.length =
    (birthWord target plan.assignment).drop source.length
  rw [hw]

theorem reassign_minimum (plan : SourcePlan spills source target)
    (result : Solution 16 source.length (fun i => target[plan.assignment i]) (fun i => target[i])) :
    MinimalWeightForWord (reassign plan result) := by
  intro other hword
  exact result.minimum other.assignment
    (allowed_same_word plan other (hword.trans (reassign_births plan result)))

structure Minimum (seed : SourcePlan spills source target) where
  plan : SourcePlan spills source target
  births : plan.births = seed.births
  minimum : MinimalWeightForWord plan

def minimize (plan : SourcePlan spills source target) : Option (Minimum plan) := do
  let result ← solve 16 source.length (fun i => target[plan.assignment i]) (fun i => target[i])
  return ⟨reassign plan result, reassign_births plan result, reassign_minimum plan result⟩

theorem Minimum.fixedWord_score_le_twice {seed : SourcePlan spills source target} (result : Minimum seed)
    (costs : PrimitiveCosts) (weights : Weights) (other : Trace spills source target)
    (hpop : other.noPop) (hword : SwapRuns.births other = seed.births) :
    (traceCost costs (realize (result.plan.cheapest costs weights)).built.trace).score weights ≤
      2 * (traceCost costs other).score weights :=
  SourceLazy.fixedWord_score_le_twice result.plan result.minimum costs weights other hpop
    (hword.trans result.births.symm)

theorem Minimum.fixedWord_surplus_le_twice {seed : SourcePlan spills source target} (result : Minimum seed)
    (costs : PrimitiveCosts) (weights : Weights) (other : Trace spills source target)
    (hpop : other.noPop) (hword : SwapRuns.births other = seed.births) :
    (traceCost costs (realize (result.plan.cheapest costs weights)).built.trace).score weights -
        baseline costs weights spills source other.additions ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills source other.additions) :=
  SourceLazy.fixedWord_surplus_le_twice result.plan result.minimum costs weights other hpop
    (hword.trans result.births.symm)

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
