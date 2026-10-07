import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.NetworkCut

namespace Tests.OptimalitySourceNetwork

open Shuffler.Optimality.BirthPlacement.SourceLazy WeightSolver

private def word : Fin 2 → Nat := ![1, 0]
private def target : Fin 2 → Nat := ![0, 1]
private def graph := network 16 2 word target
private def assignment : Equiv.Perm (Fin 2) := Equiv.swap 0 1

example : graph.WellFormed := network_wellFormed 16 2 word target
example : Layout 2 graph := network_layout 16 2 word target
example : (network 16 0 (Fin.elim0 : Fin 0 → Nat) Fin.elim0).WellFormed :=
  network_wellFormed 16 0 _ _

-- Adding a loop retains both the forward and reverse adjacency entries.
#guard ((emptyNetwork 0).add 0 0 1 0).outgoing[0]! = [1, 0]

example : Relation.ReflTransGen (InternalArc 2 graph) 0 3 :=
  network_route 16 2 word target 0 1 (by decide)

example (cut : Finset Nat) (hs : 8 ∈ cut) (ht : 9 ∉ cut) : 2 ≤ graph.cutCapacity cut :=
  network_cut_lower 16 2 word target assignment (by decide) cut hs ht

private theorem zeroFeasible : graph.Feasible (network_wellFormed 16 2 word target) (fun _ => 0) 0 := by
  simp [Network.Feasible, FiniteFlow.Feasible, FiniteFlow.divergence]

example : Relation.ReflTransGen (graph.Residual (network_wellFormed 16 2 word target) (fun _ => 0))
    ⟨graph.source, (network_wellFormed 16 2 word target).source_lt⟩
    ⟨graph.sink, (network_wellFormed 16 2 word target).sink_lt⟩ :=
  network_residual_path 16 2 word target assignment (by decide) (fun _ => 0) 0 (by decide) zeroFeasible

#print axioms network_wellFormed
#print axioms network_route
#print axioms network_cut_lower
#print axioms network_residual_path

end Tests.OptimalitySourceNetwork
