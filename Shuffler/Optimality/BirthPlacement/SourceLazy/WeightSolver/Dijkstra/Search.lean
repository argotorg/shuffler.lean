import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.Advance

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

def ActiveArc (graph : Network) (flow : Flow) (before after : Nat) : Prop :=
  ∃ edge, edge < graph.edges.size ∧ graph.edges[edge]!.tail = before ∧
    graph.edges[edge]!.head = after ∧ 0 < flow.capacity[edge]!

theorem least_none_settled (labels : Labels) (hnone : leastUnsettled labels = none)
    (vertex : Nat) (hv : vertex < labels.distance.size) (distance : Int)
    (hd : labels.distance[vertex]! = some distance) : labels.settled[vertex]! = true := by
  cases hs : labels.settled[vertex]! with
  | true => rfl
  | false =>
      obtain ⟨other, value, he⟩ := least_exists labels vertex distance hv ⟨hs, hd⟩
      rw [hnone] at he
      cases he

theorem reachable_known_of_none (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (labels : Labels) (rank : Nat → Nat) (step : Nat) (hinv : Invariant graph flow labels rank step)
    (hnone : leastUnsettled labels = none) (vertex : Nat)
    (hreach : Relation.ReflTransGen (ActiveArc graph flow) graph.source vertex) :
    vertex < graph.outgoing.size ∧ ∃ value, labels.distance[vertex]! = some value := by
  induction hreach with
  | refl => exact ⟨hw.source_lt, 0, hinv.source⟩
  | @tail before after _ he ih =>
      obtain ⟨edge, he, ht, hh, ha⟩ := he
      obtain ⟨hbefore, value, hv⟩ := ih
      have hs := least_none_settled labels hnone before (by rw [hinv.distance_size]; exact hbefore) value hv
      obtain ⟨_, found, _, hf, _⟩ := hinv.scanned edge he ha (ht ▸ hs)
      exact ⟨hh ▸ (hw.edge_bounds edge he).2.1, found, hh ▸ hf⟩

theorem reachable_least (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (labels : Labels) (rank : Nat → Nat) (step : Nat) (hinv : Invariant graph flow labels rank step)
    (hreach : Relation.ReflTransGen (ActiveArc graph flow) graph.source graph.sink) :
    ∃ vertex distance, leastUnsettled labels = some (vertex, distance) := by
  cases he : leastUnsettled labels with
  | some pair => exact ⟨pair.1, pair.2, rfl⟩
  | none =>
      obtain ⟨hv, value, hvalue⟩ := reachable_known_of_none graph hw flow labels rank step hinv he graph.sink hreach
      have hs := least_none_settled labels he graph.sink (by rw [hinv.distance_size]; exact hv) value hvalue
      rw [hinv.sink] at hs
      cases hs

theorem Invariant.step_lt (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (labels : Labels) (rank : Nat → Nat) (step : Nat) (hinv : Invariant graph flow labels rank step) :
    step < graph.outgoing.size := by
  have hsub : settledSet graph labels ⊂ Finset.range graph.outgoing.size := by
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hs := he (Finset.mem_range.mpr hw.sink_lt)
    simp [settledSet, hinv.sink] at hs
  have he := Finset.card_lt_card hsub
  simpa only [hinv.count, Finset.card_range] using he

theorem search_exists (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!)
    (hreach : Relation.ReflTransGen (ActiveArc graph flow) graph.source graph.sink)
    (fuel : Nat) (labels : Labels) (rank : Nat → Nat) (step : Nat)
    (hinv : Invariant graph flow labels rank step) (hbudget : step + fuel = graph.outgoing.size) :
    ∃ final distance finalRank finalStep,
      search graph flow fuel labels = some (final, distance) ∧
      Invariant graph flow final finalRank finalStep ∧
      leastUnsettled final = some (graph.sink, distance) := by
  induction fuel generalizing labels rank step with
  | zero => have := hinv.step_lt graph hw flow labels rank step; omega
  | succ fuel ih =>
      obtain ⟨vertex, distance, hleast⟩ := reachable_least graph hw flow labels rank step hinv hreach
      by_cases hs : vertex = graph.sink
      · refine ⟨labels, distance, rank, step, ?_, hinv, hs ▸ hleast⟩
        simp [search, hleast, hs]
      · have hnext := advance graph hw flow labels rank step hinv hcost vertex distance hleast hs
        obtain ⟨final, value, finalRank, finalStep, he, hf, hl⟩ := ih _ _ (step + 1) hnext (by omega)
        refine ⟨final, value, finalRank, finalStep, ?_, hf, hl⟩
        simpa [search, hleast, hs, settle] using he

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
