import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.Search

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

def initialLabels (graph : Network) : Labels :=
  ⟨(Array.replicate graph.outgoing.size none).set! graph.source (some 0),
    Array.replicate graph.outgoing.size none, Array.replicate graph.outgoing.size false⟩

theorem replicate_default [Inhabited α] (size index : Nat) :
    (Array.replicate size (default : α))[index]! = default := by
  by_cases hi : index < size
  · rw [getElem!_pos _ _ (by simpa using hi)]
    simp
  · rw [getElem!_neg _ _ (by simpa using hi)]

theorem initialLabels_settled (graph : Network) (vertex : Nat) :
    (initialLabels graph).settled[vertex]! = false :=
  replicate_default graph.outgoing.size vertex

theorem initialLabels_distance (graph : Network) (hw : graph.WellFormed) (vertex : Nat) :
    (initialLabels graph).distance[vertex]! = if graph.source = vertex then some 0 else none := by
  change ((Array.replicate graph.outgoing.size (none : Option Int)).set! graph.source (some 0))[vertex]! = _
  rw [set_read _ _ _ _ (by simpa using hw.source_lt)]
  have he : (Array.replicate graph.outgoing.size (none : Option Int))[vertex]! = none :=
    replicate_default graph.outgoing.size vertex
  rw [he]

theorem initial_invariant (graph : Network) (hw : graph.WellFormed) (flow : Flow) :
    Invariant graph flow (initialLabels graph) (fun _ => 0) 0 := by
  refine
    { distance_size := by simp [initialLabels]
      predecessor_size := by simp [initialLabels]
      settled_size := by simp [initialLabels]
      source := by rw [initialLabels_distance graph hw]; simp
      known := ?_
      nonnegative := ?_
      lower := ?_
      scanned := ?_
      rank_le := by simp
      rank_settled := ?_
      rank_unsettled := by simp
      count := ?_
      predecessors := ?_
      sink := initialLabels_settled graph graph.sink }
  · intro vertex hs
    rw [initialLabels_settled] at hs
    cases hs
  · intro vertex value he
    rw [initialLabels_distance graph hw] at he
    split at he
    · have := Option.some.inj he
      omega
    · cases he
  · intro vertex value hs
    rw [initialLabels_settled] at hs
    cases hs
  · intro edge _ _ hs
    rw [initialLabels_settled] at hs
    cases hs
  · intro vertex _ hs
    rw [initialLabels_settled] at hs
    cases hs
  · simp [settledSet, initialLabels_settled]
  · intro vertex _ value he
    rw [initialLabels_distance graph hw] at he
    split at he
    · rename_i hs
      exact Or.inl hs.symm
    · cases he

theorem shortest_eq_search (graph : Network) (flow : Flow) :
    shortest graph flow = search graph flow graph.outgoing.size (initialLabels graph) := rfl

theorem shortest_exists (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!)
    (hreach : Relation.ReflTransGen (ActiveArc graph flow) graph.source graph.sink) :
    ∃ final distance rank step,
      shortest graph flow = some (final, distance) ∧
      Invariant graph flow final rank step ∧ leastUnsettled final = some (graph.sink, distance) :=
  search_exists graph hw flow hcost hreach graph.outgoing.size (initialLabels graph) (fun _ => 0) 0
    (initial_invariant graph hw flow) (by omega)

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
