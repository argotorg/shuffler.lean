import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.State

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

theorem advance (graph : Network) (hw : graph.WellFormed) (flow : Flow) (labels : Labels)
    (rank : Nat → Nat) (step : Nat) (hinv : Invariant graph flow labels rank step)
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!)
    (vertex : Nat) (distance : Int) (hleast : leastUnsettled labels = some (vertex, distance))
    (hne : vertex ≠ graph.sink) :
    Invariant graph flow (relax graph flow vertex distance (settle labels vertex))
      (nextRank (settle labels vertex) rank step) (step + 1) := by
  obtain ⟨hv, hc⟩ := least_valid labels vertex distance hleast
  have hvertex : vertex < graph.outgoing.size := by rw [← hinv.distance_size]; exact hv
  have hvs : vertex < labels.settled.size := by rw [hinv.settled_size]; exact hvertex
  let marked := settle labels vertex
  let result := relax graph flow vertex distance marked
  let ranks := nextRank marked rank step
  have hmarkVertex : marked.settled[vertex]! = true := by
    simp only [marked, settle_read labels vertex hvs vertex, ite_true]
  have hmarkKnown := settle_known graph flow labels rank step vertex distance hinv hvertex hc.2
  have hmarkLower := settle_lower graph flow labels rank step vertex distance hinv hleast
  have hmarkMax := settle_max graph flow labels rank step vertex distance hinv hleast
  have hheads : ∀ edge ∈ graph.outgoing[vertex]!,
      graph.edges[edge]!.head < marked.distance.size ∧ graph.edges[edge]!.head < marked.predecessor.size := by
    intro edge he
    have hb := (hw.edge_bounds edge ((hw.outgoing vertex hvertex edge).mp he).1).2.1
    exact ⟨by change _ < labels.distance.size; rw [hinv.distance_size]; exact hb,
      by change _ < labels.predecessor.size; rw [hinv.predecessor_size]; exact hb⟩
  have hweights : ∀ edge ∈ graph.outgoing[vertex]!, 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[vertex]! - flow.potential[graph.edges[edge]!.head]! := by
    intro edge he ha
    obtain ⟨he, ht⟩ := (hw.outgoing vertex hvertex edge).mp he
    simpa only [ht] using hcost edge he ha
  have hsizes := relax_sizes graph flow vertex distance marked
  have hsame : result.settled = marked.settled := hsizes.2.2
  have hknown : ∀ other : Nat, result.settled[other]! = true →
      ∃ value, result.distance[other]! = some value := by
    intro other hs
    have hmarked : marked.settled[other]! = true := hsame ▸ hs
    obtain ⟨value, he⟩ := hmarkKnown other hmarked
    exact ⟨value, (relax_settled graph flow vertex distance marked other hmarked).1.trans he⟩
  have hnonnegative : ∀ (other : Nat) value, result.distance[other]! = some value → 0 ≤ value := by
    intro other value he
    cases hs : result.settled[other]! with
    | true =>
        have hmarked : marked.settled[other]! = true := hsame ▸ hs
        have hold := (relax_settled graph flow vertex distance marked other hmarked).1.symm.trans he
        exact hinv.nonnegative other value hold
    | false =>
        apply relax_lower graph flow vertex distance marked 0 (hinv.nonnegative vertex distance hc.2)
          hheads hweights _ other value ⟨hs, he⟩
        intro next amount hnext
        exact hinv.nonnegative next amount hnext.2
  have hrankVertex : ranks vertex = step := by
    simp only [ranks, nextRank, hmarkVertex, ite_true]
    exact hinv.rank_unsettled vertex hvertex hc.1
  have hdepth : ∀ other, other < graph.outgoing.size → marked.settled[other]! = false →
      ranks vertex < ranks other := by
    intro other _ hs
    rw [hrankVertex]
    change step < nextRank marked rank step other
    simp only [nextRank, hs, Bool.false_eq_true, ite_false]
    omega
  refine
    { distance_size := hsizes.1.trans hinv.distance_size
      predecessor_size := hsizes.2.1.trans hinv.predecessor_size
      settled_size := by rw [hsame]; simpa only [marked, settle, Array.size_set!] using hinv.settled_size
      source := ?_
      known := hknown
      nonnegative := hnonnegative
      lower := ?_
      scanned := ?_
      rank_le := ?_
      rank_settled := ?_
      rank_unsettled := ?_
      count := ?_
      predecessors := ?_
      sink := ?_ }
  · obtain ⟨value, he, hb⟩ := relax_decreases graph flow vertex distance marked
      (fun edge he => (hheads edge he).1) graph.source 0 hinv.source
    have hn := hnonnegative graph.source value he
    have hz : value = 0 := by omega
    exact hz ▸ he
  · intro other value hs he next amount hnext
    have hmarked : marked.settled[other]! = true := hsame ▸ hs
    have hold := (relax_settled graph flow vertex distance marked other hmarked).1.symm.trans he
    exact relax_lower graph flow vertex distance marked value (hmarkMax other value hmarked hold)
      hheads hweights (hmarkLower other value hmarked hold) next amount hnext
  · intro edge hedge ha hs
    have hmarked : marked.settled[graph.edges[edge]!.tail]! = true := hsame ▸ hs
    by_cases ht : graph.edges[edge]!.tail = vertex
    · have hout : edge ∈ graph.outgoing[vertex]! := (hw.outgoing vertex hvertex edge).mpr ⟨hedge, ht⟩
      obtain ⟨after, haf, hb⟩ := relax_head graph flow vertex distance marked edge hout
        (fun edge he => (hheads edge he).1) ha (by
          intro hhead
          obtain ⟨value, he⟩ := hmarkKnown _ hhead
          have hm := hmarkMax _ value hhead he
          have hwgt := hweights edge hout ha
          exact ⟨value, he, by omega⟩)
      refine ⟨distance, after, ?_, haf, ?_⟩
      · rw [ht]
        exact (relax_settled graph flow vertex distance marked vertex hmarkVertex).1.trans hc.2
      · simpa only [ht] using hb
    · have hold : labels.settled[graph.edges[edge]!.tail]! = true := by
        rw [settle_read labels vertex hvs, ite_eq_right (Ne.symm ht)] at hmarked
        exact hmarked
      obtain ⟨before, after, hbefore, hafter, hb⟩ := hinv.scanned edge hedge ha hold
      obtain ⟨value, hv, hle⟩ := relax_decreases graph flow vertex distance marked
        (fun edge he => (hheads edge he).1) _ after hafter
      exact ⟨before, value, (relax_settled graph flow vertex distance marked _ hmarked).1.trans hbefore,
        hv, hle.trans hb⟩
  · intro other ho
    dsimp only [nextRank]
    split_ifs
    · exact (hinv.rank_le other ho).trans (Nat.le_succ _)
    · exact le_refl _
  · intro other ho hs
    have hmarked : marked.settled[other]! = true := hsame ▸ hs
    change nextRank marked rank step other < step + 1
    simp only [nextRank, hmarked, ite_true]
    exact Nat.lt_succ_of_le (hinv.rank_le other ho)
  · intro other _ hs
    have hmarked : marked.settled[other]! = false := hsame ▸ hs
    change nextRank marked rank step other = step + 1
    simp only [nextRank, hmarked, Bool.false_eq_true, ite_false]
  · have he : settledSet graph result = settledSet graph marked := by simp only [settledSet, hsame]
    rw [he]
    exact settle_count graph flow labels rank step vertex distance hinv hleast
  · exact relax_predecessors graph hw flow marked ranks vertex distance hvertex hinv.distance_size
      hinv.predecessor_size hmarkVertex hc.2 hdepth
      (settle_predecessors graph flow labels rank step vertex hinv hvertex)
  · rw [hsame, settle_read labels vertex hvs, ite_eq_right hne]
    exact hinv.sink

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
