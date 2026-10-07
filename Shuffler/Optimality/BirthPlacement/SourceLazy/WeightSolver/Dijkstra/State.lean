import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.Predecessor

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

def settledSet (graph : Network) (labels : Labels) : Finset Nat :=
  (Finset.range graph.outgoing.size).filter fun vertex => labels.settled[vertex]! = true

def settle (labels : Labels) (vertex : Nat) : Labels :=
  { labels with settled := labels.settled.set! vertex true }

def nextRank (labels : Labels) (rank : Nat → Nat) (step vertex : Nat) : Nat :=
  if labels.settled[vertex]! then rank vertex else step + 1

structure Invariant (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat)
    (step : Nat) : Prop where
  distance_size : labels.distance.size = graph.outgoing.size
  predecessor_size : labels.predecessor.size = graph.outgoing.size
  settled_size : labels.settled.size = graph.outgoing.size
  source : labels.distance[graph.source]! = some 0
  known : ∀ vertex : Nat, labels.settled[vertex]! = true → ∃ value, labels.distance[vertex]! = some value
  nonnegative : ∀ (vertex : Nat) value, labels.distance[vertex]! = some value → 0 ≤ value
  lower : ∀ (vertex : Nat) value, labels.settled[vertex]! = true → labels.distance[vertex]! = some value →
    ∀ other distance, Candidate labels other distance → value ≤ distance
  scanned : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
    labels.settled[graph.edges[edge]!.tail]! = true →
    ∃ before after, labels.distance[graph.edges[edge]!.tail]! = some before ∧
      labels.distance[graph.edges[edge]!.head]! = some after ∧
      after ≤ before + graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!
  rank_le : ∀ vertex, vertex < graph.outgoing.size → rank vertex ≤ step
  rank_settled : ∀ vertex, vertex < graph.outgoing.size → labels.settled[vertex]! = true → rank vertex < step
  rank_unsettled : ∀ vertex, vertex < graph.outgoing.size → labels.settled[vertex]! = false → rank vertex = step
  count : (settledSet graph labels).card = step
  predecessors : Predecessors graph flow labels rank
  sink : labels.settled[graph.sink]! = false

theorem settle_read (labels : Labels) (vertex : Nat) (hv : vertex < labels.settled.size) (other : Nat) :
    (settle labels vertex).settled[other]! = if vertex = other then true else labels.settled[other]! :=
  set_read labels.settled vertex other true hv

theorem settle_candidate (labels : Labels) (vertex other : Nat) (distance : Int)
    (hv : vertex < labels.settled.size) (hc : Candidate (settle labels vertex) other distance) :
    Candidate labels other distance := by
  refine ⟨?_, hc.2⟩
  have hs := hc.1
  rw [settle_read labels vertex hv other] at hs
  split at hs
  · cases hs
  · exact hs

theorem settle_known (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat)
    (step vertex : Nat) (distance : Int) (hinv : Invariant graph flow labels rank step)
    (hvertex : vertex < graph.outgoing.size) (hd : labels.distance[vertex]! = some distance) :
    ∀ other : Nat, (settle labels vertex).settled[other]! = true →
      ∃ value, (settle labels vertex).distance[other]! = some value := by
  intro other hs
  rw [settle_read labels vertex (by rw [hinv.settled_size]; exact hvertex) other] at hs
  split at hs
  · rename_i he
    exact ⟨distance, he ▸ hd⟩
  · exact hinv.known other hs

theorem settle_lower (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat)
    (step vertex : Nat) (distance : Int) (hinv : Invariant graph flow labels rank step)
    (hleast : leastUnsettled labels = some (vertex, distance)) :
    ∀ (other : Nat) value, (settle labels vertex).settled[other]! = true →
      (settle labels vertex).distance[other]! = some value →
      ∀ next amount, Candidate (settle labels vertex) next amount → value ≤ amount := by
  have hv := (least_valid labels vertex distance hleast).1
  have hd := (least_valid labels vertex distance hleast).2.2
  intro other value hs he next amount hc
  have hsize : vertex < labels.settled.size := by rw [hinv.settled_size, ← hinv.distance_size]; exact hv
  have hnext := settle_candidate labels vertex next amount hsize hc
  rw [settle_read labels vertex hsize other] at hs
  split at hs
  · rename_i hother
    have hvalue : value = distance := by
      have hi := he
      change labels.distance[other]! = some value at hi
      rw [← hother, hd] at hi
      exact (Option.some.inj hi).symm
    rw [hvalue]
    have hnextSize : next < labels.distance.size := by
      by_contra hn
      have hh : labels.distance[next]! = none := getElem!_neg _ _ (by omega)
      have hn := hnext.2
      rw [hh] at hn
      cases hn
    exact least_le labels vertex distance hleast next amount hnextSize hnext
  · exact hinv.lower other value hs he next amount hnext

theorem settle_max (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat)
    (step vertex : Nat) (distance : Int) (hinv : Invariant graph flow labels rank step)
    (hleast : leastUnsettled labels = some (vertex, distance)) :
    ∀ (other : Nat) value, (settle labels vertex).settled[other]! = true →
      (settle labels vertex).distance[other]! = some value → value ≤ distance := by
  obtain ⟨hv, hc⟩ := least_valid labels vertex distance hleast
  intro other value hs he
  rw [settle_read labels vertex (by rw [hinv.settled_size, ← hinv.distance_size]; exact hv) other] at hs
  split at hs
  · rename_i hh
    change labels.distance[other]! = some value at he
    rw [← hh, hc.2] at he
    exact le_of_eq (Option.some.inj he).symm
  · exact hinv.lower other value hs he vertex distance hc

theorem settle_set (graph : Network) (labels : Labels) (vertex : Nat)
    (hsize : labels.settled.size = graph.outgoing.size) (hv : vertex < graph.outgoing.size) :
    settledSet graph (settle labels vertex) = insert vertex (settledSet graph labels) := by
  ext other
  simp only [settledSet, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    settle_read labels vertex (by omega) other]
  by_cases he : vertex = other
  · subst other
    simp [hv]
  · simp [he, Ne.symm he]

theorem settle_rank_fixed (labels : Labels) (rank : Nat → Nat) (step vertex other : Nat)
    (hv : vertex < labels.settled.size) (hs : labels.settled[other]! = true) :
    nextRank (settle labels vertex) rank step other = rank other := by
  simp only [nextRank, settle_read labels vertex hv other, hs]
  split_ifs <;> simp_all

theorem settle_rank_le (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat)
    (step vertex : Nat) (hinv : Invariant graph flow labels rank step)
    (other : Nat) (ho : other < graph.outgoing.size) :
    rank other ≤ nextRank (settle labels vertex) rank step other := by
  dsimp only [nextRank]
  split_ifs
  · exact le_refl _
  · exact (hinv.rank_le other ho).trans (Nat.le_succ _)

theorem settle_predecessors (graph : Network) (flow : Flow)
    (labels : Labels) (rank : Nat → Nat) (step vertex : Nat)
    (hinv : Invariant graph flow labels rank step) (hv : vertex < graph.outgoing.size) :
    Predecessors graph flow (settle labels vertex) (nextRank (settle labels vertex) rank step) := by
  intro other ho value he
  rcases hinv.predecessors other ho value he with hs | ⟨edge, he, hp, hh, ha, hs, before, hb, ht, hr⟩
  · exact Or.inl hs
  · right
    refine ⟨edge, he, hp, hh, ha, ?_, before, hb, ht, ?_⟩
    · rw [settle_read labels vertex (by rw [hinv.settled_size]; exact hv)]
      split_ifs <;> simp_all
    · rw [settle_rank_fixed labels rank step vertex _ (by rw [hinv.settled_size]; exact hv) hs]
      exact hr.trans_le (settle_rank_le graph flow labels rank step vertex hinv other ho)

theorem settle_count (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat)
    (step vertex : Nat) (distance : Int) (hinv : Invariant graph flow labels rank step)
    (hleast : leastUnsettled labels = some (vertex, distance)) :
    (settledSet graph (settle labels vertex)).card = step + 1 := by
  obtain ⟨hv, hc⟩ := least_valid labels vertex distance hleast
  rw [settle_set graph labels vertex hinv.settled_size (by rw [← hinv.distance_size]; exact hv)]
  have hn : vertex ∉ settledSet graph labels := by simp [settledSet, hc.1]
  rw [Finset.card_insert_of_notMem hn, hinv.count]

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
