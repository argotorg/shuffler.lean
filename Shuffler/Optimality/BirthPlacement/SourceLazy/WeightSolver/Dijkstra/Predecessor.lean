import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.Path

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

theorem relaxStep_predecessors (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (labels : Labels) (rank : Nat → Nat) (vertex : Nat) (distance : Int)
    (hsize : labels.distance.size = graph.outgoing.size)
    (hpredSize : labels.predecessor.size = graph.outgoing.size)
    (hsettled : labels.settled[vertex]! = true) (hvalue : labels.distance[vertex]! = some distance)
    (hdepth : ∀ other, other < graph.outgoing.size → labels.settled[other]! = false → rank vertex < rank other)
    (hpred : Predecessors graph flow labels rank) (edge : Nat) (he : edge < graph.edges.size)
    (htail : graph.edges[edge]!.tail = vertex) :
    Predecessors graph flow (relaxStep graph flow vertex distance labels edge) rank := by
  intro other hother value hknown
  have hhead := (hw.edge_bounds edge he).2.1
  rcases relaxStep_entry graph flow vertex distance labels edge other
      (by omega) (by omega) with hsame | hnew
  · rcases hpred other hother value (hsame.1 ▸ hknown) with hs | ⟨prior, hprior, hp, hh, ha, hsettled, before, hb, ht, hr⟩
    · exact Or.inl hs
    · right
      refine ⟨prior, hprior, hsame.2.trans hp, hh, ha, ?_, before, ?_, ht, hr⟩
      · simpa only [(relaxStep_sizes graph flow vertex distance labels edge).2.2] using hsettled
      · exact (relaxStep_settled graph flow vertex distance labels edge _ hsettled).1.trans hb
  · right
    refine ⟨edge, he, hnew.2.2.2.2, hnew.1, hnew.2.1, ?_, distance, ?_, ?_, ?_⟩
    · simpa only [(relaxStep_sizes graph flow vertex distance labels edge).2.2, htail] using hsettled
    · rw [htail]
      exact (relaxStep_settled graph flow vertex distance labels edge vertex hsettled).1.trans hvalue
    · rw [htail]
      exact Option.some.inj (hknown.symm.trans hnew.2.2.2.1)
    · rw [htail]
      exact hdepth other hother hnew.2.2.1

theorem relax_predecessors (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (labels : Labels) (rank : Nat → Nat) (vertex : Nat) (distance : Int)
    (hvertex : vertex < graph.outgoing.size)
    (hsize : labels.distance.size = graph.outgoing.size)
    (hpredSize : labels.predecessor.size = graph.outgoing.size)
    (hsettled : labels.settled[vertex]! = true) (hvalue : labels.distance[vertex]! = some distance)
    (hdepth : ∀ other, other < graph.outgoing.size → labels.settled[other]! = false → rank vertex < rank other)
    (hpred : Predecessors graph flow labels rank) :
    Predecessors graph flow (relax graph flow vertex distance labels) rank := by
  have hfull : (relax graph flow vertex distance labels).distance.size = graph.outgoing.size ∧
      (relax graph flow vertex distance labels).predecessor.size = graph.outgoing.size ∧
      (relax graph flow vertex distance labels).settled = labels.settled ∧
      (relax graph flow vertex distance labels).distance[vertex]! = some distance ∧
      Predecessors graph flow (relax graph flow vertex distance labels) rank := by
    rw [relax_eq_fold]
    refine List.foldlRecOn (motive := fun current : Labels =>
      current.distance.size = graph.outgoing.size ∧ current.predecessor.size = graph.outgoing.size ∧
      current.settled = labels.settled ∧ current.distance[vertex]! = some distance ∧
      Predecessors graph flow current rank)
      (graph.outgoing[vertex]!) (relaxStep graph flow vertex distance) ?_ ?_
    · exact ⟨hsize, hpredSize, rfl, hvalue, hpred⟩
    · intro current hc edge hedge
      have hs : current.settled[vertex]! = true := hc.2.2.1 ▸ hsettled
      obtain ⟨he, ht⟩ := (hw.outgoing vertex hvertex edge).mp hedge
      obtain ⟨hd, hp, hsame⟩ := relaxStep_sizes graph flow vertex distance current edge
      refine ⟨hd.trans hc.1, hp.trans hc.2.1, hsame.trans hc.2.2.1,
        (relaxStep_settled graph flow vertex distance current edge vertex hs).1.trans hc.2.2.2.1, ?_⟩
      apply relaxStep_predecessors graph hw flow current rank vertex distance hc.1 hc.2.1 hs hc.2.2.2.1
        (fun other hother hunsettled => hdepth other hother (hc.2.2.1 ▸ hunsettled)) hc.2.2.2.2 edge he ht
  exact hfull.2.2.2.2

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
