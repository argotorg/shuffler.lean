import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra.Initial

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

theorem fold_set_size (array : Array α) (indices : List Nat) (value : Nat → α) :
    (indices.foldl (fun current index => current.set! index (value index)) array).size = array.size := by
  refine List.foldlRecOn (motive := fun current : Array α => current.size = array.size)
    indices (fun current index => current.set! index (value index)) rfl ?_
  intro current hc index _
  simpa only [Array.size_set!] using hc

theorem fold_set_read [Inhabited α] (array : Array α) (indices : List Nat) (value : Nat → α)
    (hindices : ∀ index ∈ indices, index < array.size) (other : Nat) :
    (indices.foldl (fun current index => current.set! index (value index)) array)[other]! =
      if other ∈ indices then value other else array[other]! := by
  induction indices generalizing array with
  | nil => simp
  | cons index rest ih =>
      rw [List.foldl_cons, ih]
      · rw [set_read array index other (value index) (hindices index (by simp))]
        by_cases hr : other ∈ rest
        · simp [hr]
        · by_cases he : index = other
          · subst other
            simp [hr]
          · simp [hr, he, Ne.symm he]
      · intro vertex hv
        simpa only [Array.size_set!] using hindices vertex (by simp [hv])

theorem updatePotential_size (graph : Network) (flow : Flow) (labels : Labels) (distance : Int) :
    (updatePotential graph flow labels distance).size = flow.potential.size :=
  fold_set_size flow.potential (List.range graph.outgoing.size)
    (fun vertex => flow.potential[vertex]! + Potential.truncate distance (labels.distance[vertex]!))

theorem updatePotential_apply (graph : Network) (flow : Flow) (labels : Labels) (distance : Int)
    (hsize : flow.potential.size = graph.outgoing.size) (vertex : Nat) (hv : vertex < graph.outgoing.size) :
    (updatePotential graph flow labels distance)[vertex]! =
      flow.potential[vertex]! + Potential.truncate distance (labels.distance[vertex]!) := by
  change ((List.range graph.outgoing.size).foldl (fun current index => current.set! index
    (flow.potential[index]! + Potential.truncate distance (labels.distance[index]!))) flow.potential)[vertex]! = _
  rw [fold_set_read flow.potential (List.range graph.outgoing.size) _
    (by intro index hi; rw [hsize]; exact List.mem_range.mp hi) vertex]
  simp only [List.mem_range.mpr hv, ite_true]

theorem known_in_range (labels : Labels) (vertex : Nat) (distance : Int)
    (hd : labels.distance[vertex]! = some distance) : vertex < labels.distance.size := by
  by_contra hn
  have he : labels.distance[vertex]! = none := getElem!_neg _ _ (by omega)
  rw [he] at hd
  cases hd

theorem stop_triangle (graph : Network) (flow : Flow) (labels : Labels) (rank : Nat → Nat)
    (step : Nat) (hinv : Invariant graph flow labels rank step) (distance : Int)
    (hleast : leastUnsettled labels = some (graph.sink, distance))
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!) :
    ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      Potential.truncate distance (labels.distance[graph.edges[edge]!.head]!) ≤
        Potential.truncate distance (labels.distance[graph.edges[edge]!.tail]!) +
          (graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
            flow.potential[graph.edges[edge]!.head]!) := by
  have h := Potential.stopped_triangle (fun edge : Nat => graph.edges[edge]!.tail)
    (fun edge => graph.edges[edge]!.head) (fun edge => graph.edges[edge]!.cost)
    (fun edge => edge < graph.edges.size ∧ 0 < flow.capacity[edge]!)
    (fun vertex => flow.potential[vertex]!) (fun vertex => labels.distance[vertex]!)
    (fun vertex => labels.settled[vertex]! = true) distance
    (fun edge he => hcost edge he.1 he.2)
    (by
      intro vertex hs value hv
      exact least_le labels graph.sink distance hleast vertex value (known_in_range labels vertex value hv)
        ⟨by simpa using hs, hv⟩)
    (by
      intro edge he hs
      obtain ⟨before, after, hb, ha, ht⟩ := hinv.scanned edge he.1 he.2 hs
      exact ⟨before, after, hb, ha, by dsimp only [Potential.reduced]; omega⟩)
  exact fun edge he ha => h edge ⟨he, ha⟩

theorem stop_update_feasible (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (hsize : flow.potential.size = graph.outgoing.size)
    (labels : Labels) (rank : Nat → Nat) (step : Nat) (hinv : Invariant graph flow labels rank step)
    (distance : Int) (hleast : leastUnsettled labels = some (graph.sink, distance))
    (hcost : ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[graph.edges[edge]!.tail]! -
        flow.potential[graph.edges[edge]!.head]!) :
    ∀ edge, edge < graph.edges.size → 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost +
        (updatePotential graph flow labels distance)[graph.edges[edge]!.tail]! -
        (updatePotential graph flow labels distance)[graph.edges[edge]!.head]! := by
  intro edge he ha
  have hb := hw.edge_bounds edge he
  rw [updatePotential_apply graph flow labels distance hsize _ hb.1,
    updatePotential_apply graph flow labels distance hsize _ hb.2.1]
  have ht := stop_triangle graph flow labels rank step hinv distance hleast hcost edge he ha
  omega

theorem path_update_tight (graph : Network) (hw : graph.WellFormed) (flow : Flow)
    (hsize : flow.potential.size = graph.outgoing.size)
    (labels : Labels) (rank : Nat → Nat) (distance : Int) (steps : List Nat)
    (facts : PathFacts graph flow labels rank graph.sink distance steps) :
    ∀ edge ∈ steps, graph.edges[edge]!.cost +
      (updatePotential graph flow labels distance)[graph.edges[edge]!.tail]! -
      (updatePotential graph flow labels distance)[graph.edges[edge]!.head]! = 0 := by
  intro edge he
  have hb := hw.edge_bounds edge (facts.valid edge he).1
  rw [updatePotential_apply graph flow labels distance hsize _ hb.1,
    updatePotential_apply graph flow labels distance hsize _ hb.2.1]
  obtain ⟨before, after, hbefore, hafter, ht, horder, hbound⟩ := facts.tight edge he
  rw [hbefore, hafter]
  simp only [Potential.truncate, min_eq_left hbound, min_eq_left (horder.trans hbound)]
  omega

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
