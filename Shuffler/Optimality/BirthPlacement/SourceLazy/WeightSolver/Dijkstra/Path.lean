import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.Relax
import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.NetworkFacts

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

def Predecessors (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat) : Prop :=
  ∀ vertex, vertex < graph.outgoing.size → ∀ distance, labels.distance[vertex]! = some distance →
    vertex = graph.source ∨ ∃ edge, edge < graph.edges.size ∧
      labels.predecessor[vertex]! = some edge ∧ graph.edges[edge]!.head = vertex ∧
      0 < flow.capacity[edge]! ∧ labels.settled[graph.edges[edge]!.tail]! = true ∧
      ∃ before, labels.distance[graph.edges[edge]!.tail]! = some before ∧
        distance = before + graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
          flow.potential[vertex]! ∧ rank (graph.edges[edge]!.tail) < rank vertex

def BackwardPath (graph : Network) (source : Nat) : Nat → List Nat → Prop
  | vertex, [] => vertex = source
  | vertex, edge :: rest => graph.edges[edge]!.head = vertex ∧
      BackwardPath graph source graph.edges[edge]!.tail rest

structure PathFacts (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat)
    (vertex : Nat) (distance : Int) (steps : List Nat) : Prop where
  chain : BackwardPath graph graph.source vertex steps
  valid : ∀ edge ∈ steps, edge < graph.edges.size ∧ 0 < flow.capacity[edge]!
  ranks : ∀ edge ∈ steps, rank (graph.edges[edge]!.head) ≤ rank vertex
  forwardRanks : ∀ edge ∈ steps, rank (graph.edges[edge]!.tail) < rank (graph.edges[edge]!.head)
  ordered : steps.Pairwise (fun before after =>
    rank (graph.edges[after]!.head) < rank (graph.edges[before]!.head))
  tight : ∀ edge ∈ steps, ∃ before after,
    labels.distance[graph.edges[edge]!.tail]! = some before ∧
    labels.distance[graph.edges[edge]!.head]! = some after ∧
    after = before + graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
      flow.potential[graph.edges[edge]!.head]! ∧ before ≤ after ∧ after ≤ distance

theorem path_exists (graph : Network) (hw : graph.WellFormed) (flow : Flow) (labels : Labels)
    (rank : Nat → Nat) (hpred : Predecessors graph flow labels rank)
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!)
    (fuel vertex : Nat) (hv : vertex < graph.outgoing.size) (distance : Int)
    (hd : labels.distance[vertex]! = some distance) (hrank : rank vertex < fuel) :
    ∃ steps, path graph labels fuel vertex = some steps ∧
      PathFacts graph flow labels rank vertex distance steps := by
  induction fuel generalizing vertex distance with
  | zero => omega
  | succ fuel ih =>
      by_cases hs : vertex = graph.source
      · refine ⟨[], by simp only [path, hs, ite_true], ?_⟩
        exact ⟨hs, by simp, by simp, by simp, by simp, by simp⟩
      · rcases hpred vertex hv distance hd with he | ⟨edge, he, hp, hh, ha, hsettled, before, hb, ht, hr⟩
        · exact False.elim (hs he)
        · have htail := (hw.edge_bounds edge he).1
          obtain ⟨steps, hsteps, facts⟩ := ih (graph.edges[edge]!.tail) htail before hb (by omega)
          have hnonneg := hcost edge he ha
          have hle : before ≤ distance := by rw [hh] at hnonneg; omega
          refine ⟨edge :: steps, ?_, ?_⟩
          · simp [path, hs, hp, hsteps]
          · refine ⟨⟨hh, facts.chain⟩, ?_, ?_, ?_, ?_, ?_⟩
            · intro index hi
              rcases List.mem_cons.mp hi with rfl | hi
              · exact ⟨he, ha⟩
              · exact facts.valid index hi
            · intro index hi
              rcases List.mem_cons.mp hi with rfl | hi
              · rw [hh]
              · exact (facts.ranks index hi).trans (Nat.le_of_lt hr)
            · intro index hi
              rcases List.mem_cons.mp hi with rfl | hi
              · simpa only [hh] using hr
              · exact facts.forwardRanks index hi
            · rw [List.pairwise_cons]
              refine ⟨?_, facts.ordered⟩
              intro index hi
              rw [hh]
              exact (facts.ranks index hi).trans_lt hr
            · intro index hi
              rcases List.mem_cons.mp hi with rfl | hi
              · exact ⟨before, distance, hb, hh ▸ hd, by simpa only [hh] using ht, hle, le_refl _⟩
              · obtain ⟨first, last, hfirst, hlast, heq, horder, hbound⟩ := facts.tight index hi
                exact ⟨first, last, hfirst, hlast, heq, horder, hbound.trans hle⟩

theorem PathFacts.nodup (facts : PathFacts graph flow labels rank vertex distance steps) : steps.Nodup := by
  apply List.Pairwise.imp _ facts.ordered
  intro before after hlt he
  subst after
  omega

theorem PathFacts.reverse_not_mem (hw : graph.WellFormed)
    (facts : PathFacts graph flow labels rank vertex distance steps) (edge : Nat) (he : edge ∈ steps) :
    graph.edges[edge]!.reverse ∉ steps := by
  intro hb
  have hforward := facts.forwardRanks edge he
  have hback := facts.forwardRanks _ hb
  have hrev := hw.reverse edge (facts.valid edge he).1
  dsimp only at hrev
  rw [hrev.1, hrev.2.1] at hback
  omega

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
