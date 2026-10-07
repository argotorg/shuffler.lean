import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.Found

namespace Tests.OptimalitySourceDijkstra

open Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

#guard leastUnsettled ⟨#[], #[], #[]⟩ = none
#guard leastUnsettled ⟨#[some 3, some 1, some 1], #[none, none, none], #[false, false, false]⟩ =
  some (1, 1)
#guard leastUnsettled ⟨#[some 3, some 1, some 1], #[none, none, none], #[false, true, false]⟩ =
  some (2, 1)

private def earlyStop : Network :=
  ((⟨0, 2, #[], #[[], [], [], []]⟩ : Network).add 0 1 4 2).add 0 2 4 1

-- The sink is settled before vertex 1. Vertex 3 is unreachable.
-- Both receive the truncated sink distance in the actual potential update.
#guard (shortest earlyStop (initial earlyStop)).map Prod.snd = some 1
#guard (augment earlyStop (initial earlyStop)).map (fun flow => flow.potential.toList) =
  some [0, 1, 1, 1]
#guard (augment earlyStop (initial earlyStop)).map (fun flow => flow.capacity.toList) =
  some [4, 0, 3, 1]

private def zeroCycle : Network :=
  (((⟨0, 2, #[], #[[], [], []]⟩ : Network).add 0 1 1 0).add 1 0 1 0).add 1 2 1 1

-- Equal-distance zero-cost arcs cannot make a predecessor cycle.
#guard ((shortest zeroCycle (initial zeroCycle)).bind (fun result =>
  path zeroCycle result.1 zeroCycle.outgoing.size zeroCycle.sink)) = some [4, 0]

private def disconnected : Network :=
  (⟨0, 2, #[], #[[], [], []]⟩ : Network).add 0 1 1 0

#guard (shortest disconnected (initial disconnected)).isNone
#guard (augment disconnected (initial disconnected)).isNone

#print axioms Dijkstra.shortest_exists
#print axioms Dijkstra.found_exists
#print axioms Dijkstra.Found.next_feasible

end Tests.OptimalitySourceDijkstra
