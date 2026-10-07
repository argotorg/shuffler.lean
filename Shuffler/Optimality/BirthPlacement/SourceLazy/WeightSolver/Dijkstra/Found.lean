import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.PotentialUpdate

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

structure Found (graph : Network) (flow : Flow) where
  labels : Labels
  distance : Int
  rank : Nat → Nat
  step : Nat
  steps : List Nat
  shortest_eq : shortest graph flow = some (labels, distance)
  invariant : Invariant graph flow labels rank step
  minimum : leastUnsettled labels = some (graph.sink, distance)
  path_eq : path graph labels graph.outgoing.size graph.sink = some steps
  facts : PathFacts graph flow labels rank graph.sink distance steps

theorem found_exists (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!)
    (hreach : Relation.ReflTransGen (ActiveArc graph flow) graph.source graph.sink) :
    Nonempty (Found graph flow) := by
  obtain ⟨labels, distance, rank, step, hs, hinv, hl⟩ := shortest_exists graph hw flow hcost hreach
  have hd := (least_valid labels graph.sink distance hl).2.2
  have hr : rank graph.sink < graph.outgoing.size :=
    (hinv.rank_le graph.sink hw.sink_lt).trans_lt (hinv.step_lt graph hw flow labels rank step)
  obtain ⟨steps, hp, hf⟩ := path_exists graph hw flow labels rank hinv.predecessors hcost
    graph.outgoing.size graph.sink hw.sink_lt distance hd hr
  exact ⟨⟨labels, distance, rank, step, steps, hs, hinv, hl, hp, hf⟩⟩

def Found.next (found : Found graph flow) : Flow :=
  ⟨found.steps.foldl (pushArc graph) flow.capacity,
    updatePotential graph flow found.labels found.distance⟩

theorem Found.augment_eq (found : Found graph flow) : augment graph flow = some found.next := by
  simp [augment, found.shortest_eq, found.path_eq, Found.next]

theorem Found.potential_size (found : Found graph flow) : found.next.potential.size = flow.potential.size :=
  updatePotential_size graph flow found.labels found.distance

theorem Found.old_feasible (found : Found graph flow) (hw : graph.WellFormed)
    (hsize : flow.potential.size = graph.outgoing.size)
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!) :
    ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + found.next.potential[graph.edges[edge]!.tail]! -
        found.next.potential[graph.edges[edge]!.head]! :=
  stop_update_feasible graph hw flow hsize found.labels found.rank found.step found.invariant
    found.distance found.minimum hcost

theorem Found.path_tight (found : Found graph flow) (hw : graph.WellFormed)
    (hsize : flow.potential.size = graph.outgoing.size) :
    ∀ edge ∈ found.steps, graph.edges[edge]!.cost + found.next.potential[graph.edges[edge]!.tail]! -
      found.next.potential[graph.edges[edge]!.head]! = 0 :=
  path_update_tight graph hw flow hsize found.labels found.rank found.distance found.steps found.facts

-- The capacity proof supplies this local description of each newly active edge.
theorem Found.next_feasible (found : Found graph flow) (hw : graph.WellFormed)
    (hsize : flow.potential.size = graph.outgoing.size)
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!)
    (hnew : ∀ edge, edge < graph.edges.size → 0 < found.next.capacity[edge]! →
      0 < flow.capacity[edge]! ∨ ∃ prior ∈ found.steps, graph.edges[prior]!.reverse = edge) :
    ∀ edge, edge < graph.edges.size → 0 < found.next.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + found.next.potential[graph.edges[edge]!.tail]! -
        found.next.potential[graph.edges[edge]!.head]! := by
  intro edge he ha
  rcases hnew edge he ha with hold | ⟨prior, hp, hb⟩
  · exact found.old_feasible hw hsize hcost edge he hold
  · have ht := found.path_tight hw hsize prior hp
    have hr := hw.reverse prior (found.facts.valid prior hp).1
    dsimp only at hr
    rw [hb] at hr
    rw [hr.1, hr.2.1, hr.2.2.2]
    omega

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
