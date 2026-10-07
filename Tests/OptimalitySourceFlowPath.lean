import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.FlowPath
import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Potential

namespace Tests.OptimalitySourceFlowPath

open Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.FiniteFlow

private def tail : Fin 5 → Fin 4 := ![0, 1, 2, 0, 1]
private def head : Fin 5 → Fin 4 := ![1, 2, 3, 2, 3]
private def capacity : Fin 5 → Nat := fun _ => 1
private def flow : Fin 5 → Nat := ![1, 1, 1, 0, 0]
private def other : Fin 5 → Nat := ![1, 0, 1, 1, 1]

-- The augmenting path uses 0→2, the reverse of 1→2, then 1→3.
example : Feasible tail head capacity flow 0 3 1 := by unfold Feasible; decide
example : Feasible tail head capacity other 0 3 2 := by unfold Feasible; decide
example : Residual tail head capacity flow 2 1 := by unfold Residual; decide
example : ¬Residual tail head capacity flow 0 1 := by unfold Residual; decide
example : Relation.ReflTransGen (Residual tail head capacity flow) 0 3 :=
  residual_path tail head capacity flow other 0 3 1 2
    (by unfold Feasible; decide) (by unfold Feasible; decide) (by decide)

#print axioms residual_path

open Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

#guard Potential.truncate 5 none = 5
#guard Potential.truncate 5 (some 8) = 5
#guard Potential.truncate 5 (some (-2)) = -2

-- An unreached tail receives the limit, so this residual edge stays nonnegative.
#guard Potential.reduced (fun _ : Unit => false) (fun _ => true) (fun _ => 0)
  (fun vertex => Potential.truncate 3 (if vertex then some 1 else none)) () = 2

#print axioms Potential.stopped_update_feasible
#print axioms Potential.augment_feasible

end Tests.OptimalitySourceFlowPath
