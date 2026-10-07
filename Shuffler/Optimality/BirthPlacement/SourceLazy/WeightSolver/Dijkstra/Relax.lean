import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra

abbrev relaxStep (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex : Nat) : Labels :=
  let edge := graph.edges[edgeIndex]!
  if flow.capacity[edgeIndex]! = 0 || labels.settled[edge.head]! then labels
  else
    let candidate := distance + edge.cost + flow.potential[vertex]! - flow.potential[edge.head]!
    let improve := match labels.distance[edge.head]! with
      | none => true
      | some old => candidate < old
    if improve then { labels with
      distance := labels.distance.set! edge.head (some candidate)
      predecessor := labels.predecessor.set! edge.head (some edgeIndex) }
    else labels

theorem relax_eq_fold (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) :
    relax graph flow vertex distance labels =
      (graph.outgoing[vertex]!).foldl (relaxStep graph flow vertex distance) labels := rfl

theorem relaxStep_sizes (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex : Nat) :
    (relaxStep graph flow vertex distance labels edgeIndex).distance.size = labels.distance.size ∧
    (relaxStep graph flow vertex distance labels edgeIndex).predecessor.size = labels.predecessor.size ∧
    (relaxStep graph flow vertex distance labels edgeIndex).settled = labels.settled := by
  dsimp only [relaxStep]
  split_ifs <;> simp

theorem relax_sizes (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) :
    (relax graph flow vertex distance labels).distance.size = labels.distance.size ∧
    (relax graph flow vertex distance labels).predecessor.size = labels.predecessor.size ∧
    (relax graph flow vertex distance labels).settled = labels.settled := by
  rw [relax_eq_fold]
  refine List.foldlRecOn (motive := fun current : Labels =>
    current.distance.size = labels.distance.size ∧
    current.predecessor.size = labels.predecessor.size ∧ current.settled = labels.settled)
    (graph.outgoing[vertex]!) (relaxStep graph flow vertex distance) ?_ ?_
  · exact ⟨rfl, rfl, rfl⟩
  · intro current hc edge _
    obtain ⟨hd, hp, hs⟩ := relaxStep_sizes graph flow vertex distance current edge
    exact ⟨hd.trans hc.1, hp.trans hc.2.1, hs.trans hc.2.2⟩

-- Every changed label records the edge that supplied its new distance.
theorem relaxStep_cases (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex : Nat) :
    relaxStep graph flow vertex distance labels edgeIndex = labels ∨
    (let edge := graph.edges[edgeIndex]!
     let candidate := distance + edge.cost + flow.potential[vertex]! - flow.potential[edge.head]!
     0 < flow.capacity[edgeIndex]! ∧ labels.settled[edge.head]! = false ∧
       (∀ old, labels.distance[edge.head]! = some old → candidate < old) ∧
       relaxStep graph flow vertex distance labels edgeIndex =
         { labels with
           distance := labels.distance.set! edge.head (some candidate)
           predecessor := labels.predecessor.set! edge.head (some edgeIndex) }) := by
  unfold relaxStep
  dsimp only
  split_ifs with hactive himprove
  · exact Or.inl rfl
  · right
    refine ⟨?_, ?_, ?_, rfl⟩
    · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hactive
      omega
    · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hactive
      simpa using hactive.2
    · intro old hold
      rw [hold] at himprove
      simpa using himprove
  · exact Or.inl rfl

theorem set_read [Inhabited α] (array : Array α) (index other : Nat) (value : α)
    (hi : index < array.size) :
    (array.set! index value)[other]! = if index = other then value else array[other]! := by
  by_cases he : index = other
  · subst other
    rw [Array.getElem!_set!_self array index value hi]
    simp
  · rw [Array.getElem!_set!_ne array index other value he]
    simp [he]

theorem relaxStep_settled (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex other : Nat) (hs : labels.settled[other]! = true) :
    (relaxStep graph flow vertex distance labels edgeIndex).distance[other]! = labels.distance[other]! ∧
    (relaxStep graph flow vertex distance labels edgeIndex).predecessor[other]! = labels.predecessor[other]! := by
  rcases relaxStep_cases graph flow vertex distance labels edgeIndex with he | hc
  · rw [he]
    exact ⟨rfl, rfl⟩
  · dsimp only at hc
    rw [hc.2.2.2]
    have hn : graph.edges[edgeIndex]!.head ≠ other := by
      intro hh
      rw [hh, hs] at hc
      simp at hc
    exact ⟨Array.getElem!_set!_ne _ _ _ _ hn, Array.getElem!_set!_ne _ _ _ _ hn⟩

theorem relaxStep_decreases (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex : Nat)
    (hh : graph.edges[edgeIndex]!.head < labels.distance.size)
    (other : Nat) (old : Int) (hold : labels.distance[other]! = some old) :
    ∃ next, (relaxStep graph flow vertex distance labels edgeIndex).distance[other]! = some next ∧
      next ≤ old := by
  rcases relaxStep_cases graph flow vertex distance labels edgeIndex with he | hc
  · exact ⟨old, by rw [he]; exact hold, le_refl _⟩
  · dsimp only at hc
    rw [hc.2.2.2]
    simp only [set_read _ _ _ _ hh]
    split
    · rename_i he
      exact ⟨_, rfl, le_of_lt (hc.2.2.1 old (he ▸ hold))⟩
    · exact ⟨old, hold, le_refl _⟩

theorem relax_settled (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (other : Nat) (hs : labels.settled[other]! = true) :
    (relax graph flow vertex distance labels).distance[other]! = labels.distance[other]! ∧
    (relax graph flow vertex distance labels).predecessor[other]! = labels.predecessor[other]! := by
  have hfull : (relax graph flow vertex distance labels).settled = labels.settled ∧
      (relax graph flow vertex distance labels).distance[other]! = labels.distance[other]! ∧
      (relax graph flow vertex distance labels).predecessor[other]! = labels.predecessor[other]! := by
    rw [relax_eq_fold]
    refine List.foldlRecOn (motive := fun current : Labels =>
      current.settled = labels.settled ∧ current.distance[other]! = labels.distance[other]! ∧
      current.predecessor[other]! = labels.predecessor[other]!)
      (graph.outgoing[vertex]!) (relaxStep graph flow vertex distance) ?_ ?_
    · exact ⟨rfl, rfl, rfl⟩
    · intro current hc edge _
      obtain ⟨hd, hp⟩ := relaxStep_settled graph flow vertex distance current edge other (hc.1 ▸ hs)
      exact ⟨(relaxStep_sizes graph flow vertex distance current edge).2.2.trans hc.1,
        hd.trans hc.2.1, hp.trans hc.2.2⟩
  exact hfull.2

theorem fold_decreases (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (indices : List Nat) (labels : Labels)
    (hheads : ∀ edge ∈ indices, graph.edges[edge]!.head < labels.distance.size)
    (other : Nat) (old : Int) (hold : labels.distance[other]! = some old) :
    ∃ next, (indices.foldl (relaxStep graph flow vertex distance) labels).distance[other]! = some next ∧
      next ≤ old := by
  have hfull : (indices.foldl (relaxStep graph flow vertex distance) labels).distance.size = labels.distance.size ∧
      ∃ next, (indices.foldl (relaxStep graph flow vertex distance) labels).distance[other]! = some next ∧ next ≤ old := by
    refine List.foldlRecOn (motive := fun current : Labels =>
      current.distance.size = labels.distance.size ∧
        ∃ next, current.distance[other]! = some next ∧ next ≤ old)
      indices (relaxStep graph flow vertex distance) ?_ ?_
    · exact ⟨rfl, old, hold, le_refl _⟩
    · intro current hc edge he
      obtain ⟨next, hn, hle⟩ := hc.2
      obtain ⟨after, ha, hafter⟩ := relaxStep_decreases graph flow vertex distance current edge
        (hc.1 ▸ hheads edge he) other next hn
      exact ⟨(relaxStep_sizes graph flow vertex distance current edge).1.trans hc.1,
        after, ha, hafter.trans hle⟩
  exact hfull.2

theorem relax_decreases (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels)
    (hheads : ∀ edge ∈ graph.outgoing[vertex]!, graph.edges[edge]!.head < labels.distance.size)
    (other : Nat) (old : Int) (hold : labels.distance[other]! = some old) :
    ∃ next, (relax graph flow vertex distance labels).distance[other]! = some next ∧ next ≤ old :=
  fold_decreases graph flow vertex distance _ labels hheads other old hold

theorem relaxStep_entry (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex other : Nat)
    (hd : graph.edges[edgeIndex]!.head < labels.distance.size)
    (hp : graph.edges[edgeIndex]!.head < labels.predecessor.size) :
    ((relaxStep graph flow vertex distance labels edgeIndex).distance[other]! = labels.distance[other]! ∧
      (relaxStep graph flow vertex distance labels edgeIndex).predecessor[other]! = labels.predecessor[other]!) ∨
    (graph.edges[edgeIndex]!.head = other ∧ 0 < flow.capacity[edgeIndex]! ∧
      labels.settled[other]! = false ∧
      (relaxStep graph flow vertex distance labels edgeIndex).distance[other]! =
        some (distance + graph.edges[edgeIndex]!.cost + flow.potential[vertex]! - flow.potential[other]!) ∧
      (relaxStep graph flow vertex distance labels edgeIndex).predecessor[other]! = some edgeIndex) := by
  rcases relaxStep_cases graph flow vertex distance labels edgeIndex with he | hc
  · rw [he]
    exact Or.inl ⟨rfl, rfl⟩
  · dsimp only at hc
    rw [hc.2.2.2]
    by_cases hh : graph.edges[edgeIndex]!.head = other
    · right
      refine ⟨hh, hc.1, hh ▸ hc.2.1, ?_, ?_⟩
      · dsimp only
        rw [set_read _ _ _ _ hd]
        simp only [hh, ite_true]
      · dsimp only
        rw [set_read _ _ _ _ hp]
        simp only [hh, ite_true]
    · left
      exact ⟨Array.getElem!_set!_ne _ _ _ _ hh, Array.getElem!_set!_ne _ _ _ _ hh⟩

theorem relaxStep_lower (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex : Nat) (bound : Int)
    (hd : graph.edges[edgeIndex]!.head < labels.distance.size)
    (hp : graph.edges[edgeIndex]!.head < labels.predecessor.size)
    (hbound : bound ≤ distance)
    (hcost : 0 < flow.capacity[edgeIndex]! → 0 ≤ graph.edges[edgeIndex]!.cost + flow.potential[vertex]! -
      flow.potential[graph.edges[edgeIndex]!.head]!)
    (hlower : ∀ other value, Candidate labels other value → bound ≤ value) :
    ∀ other value, Candidate (relaxStep graph flow vertex distance labels edgeIndex) other value →
      bound ≤ value := by
  intro other value hc
  rcases relaxStep_entry graph flow vertex distance labels edgeIndex other hd hp with hsame | hnew
  · apply hlower other value
    exact ⟨by simpa only [(relaxStep_sizes graph flow vertex distance labels edgeIndex).2.2] using hc.1,
      hsame.1 ▸ hc.2⟩
  · have he := hc.2.symm.trans hnew.2.2.2.1
    have hv := Option.some.inj he
    have hweight := hcost hnew.2.1
    rw [hnew.1] at hweight
    omega

theorem relaxStep_head (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex : Nat)
    (hh : graph.edges[edgeIndex]!.head < labels.distance.size)
    (ha : 0 < flow.capacity[edgeIndex]!)
    (hs : labels.settled[graph.edges[edgeIndex]!.head]! = true →
      ∃ old, labels.distance[graph.edges[edgeIndex]!.head]! = some old ∧
        old ≤ distance + graph.edges[edgeIndex]!.cost + flow.potential[vertex]! -
          flow.potential[graph.edges[edgeIndex]!.head]!) :
    ∃ next, (relaxStep graph flow vertex distance labels edgeIndex).distance[graph.edges[edgeIndex]!.head]! =
      some next ∧ next ≤ distance + graph.edges[edgeIndex]!.cost + flow.potential[vertex]! -
        flow.potential[graph.edges[edgeIndex]!.head]! := by
  have hn : flow.capacity[edgeIndex]! ≠ 0 := by omega
  cases hsettled : labels.settled[graph.edges[edgeIndex]!.head]! with
  | true => simpa only [relaxStep, hn, decide_false, hsettled, Bool.false_or, ite_true] using hs hsettled
  | false =>
      cases hold : labels.distance[graph.edges[edgeIndex]!.head]! with
      | none =>
          refine ⟨_, ?_, le_refl _⟩
          simp only [relaxStep, hn, decide_false, hsettled, Bool.false_or, Bool.false_eq_true,
            ite_false, hold, ite_true]
          exact Array.getElem!_set!_self _ _ _ hh
      | some old =>
          by_cases hi : distance + graph.edges[edgeIndex]!.cost + flow.potential[vertex]! -
              flow.potential[graph.edges[edgeIndex]!.head]! < old
          · refine ⟨_, ?_, le_refl _⟩
            simp only [relaxStep, hn, decide_false, hsettled, Bool.false_or, Bool.false_eq_true,
              ite_false, hold, hi, decide_true, ite_true]
            exact Array.getElem!_set!_self _ _ _ hh
          · refine ⟨old, ?_, by omega⟩
            simp only [relaxStep, hn, decide_false, hsettled, Bool.false_or, Bool.false_eq_true,
              ite_false, hold, hi]

theorem fold_head (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (indices : List Nat) (labels : Labels) (edgeIndex : Nat) (he : edgeIndex ∈ indices)
    (hheads : ∀ edge ∈ indices, graph.edges[edge]!.head < labels.distance.size)
    (ha : 0 < flow.capacity[edgeIndex]!)
    (hs : labels.settled[graph.edges[edgeIndex]!.head]! = true →
      ∃ old, labels.distance[graph.edges[edgeIndex]!.head]! = some old ∧
        old ≤ distance + graph.edges[edgeIndex]!.cost + flow.potential[vertex]! -
          flow.potential[graph.edges[edgeIndex]!.head]!) :
    ∃ next, (indices.foldl (relaxStep graph flow vertex distance) labels).distance[graph.edges[edgeIndex]!.head]! =
      some next ∧ next ≤ distance + graph.edges[edgeIndex]!.cost + flow.potential[vertex]! -
        flow.potential[graph.edges[edgeIndex]!.head]! := by
  induction indices generalizing labels with
  | nil => simp at he
  | cons first rest ih =>
      have hrest : ∀ edge ∈ rest, graph.edges[edge]!.head <
          (relaxStep graph flow vertex distance labels first).distance.size := by
        intro edge hedge
        rw [(relaxStep_sizes graph flow vertex distance labels first).1]
        exact hheads edge (by simp [hedge])
      rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨next, hn, hle⟩ := relaxStep_head graph flow vertex distance labels edgeIndex
          (hheads edgeIndex (by simp)) ha hs
        obtain ⟨after, haf, hb⟩ := fold_decreases graph flow vertex distance rest _ hrest _ next hn
        exact ⟨after, haf, hb.trans hle⟩
      · apply ih _ he hrest
        intro hsettled
        have hold : labels.settled[graph.edges[edgeIndex]!.head]! = true := by
          simpa only [(relaxStep_sizes graph flow vertex distance labels first).2.2] using hsettled
        obtain ⟨old, ho, hb⟩ := hs hold
        exact ⟨old, (relaxStep_settled graph flow vertex distance labels first _ hold).1.trans ho, hb⟩

theorem relax_head (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (edgeIndex : Nat) (he : edgeIndex ∈ graph.outgoing[vertex]!)
    (hheads : ∀ edge ∈ graph.outgoing[vertex]!, graph.edges[edge]!.head < labels.distance.size)
    (ha : 0 < flow.capacity[edgeIndex]!)
    (hs : labels.settled[graph.edges[edgeIndex]!.head]! = true →
      ∃ old, labels.distance[graph.edges[edgeIndex]!.head]! = some old ∧
        old ≤ distance + graph.edges[edgeIndex]!.cost + flow.potential[vertex]! -
          flow.potential[graph.edges[edgeIndex]!.head]!) :
    ∃ next, (relax graph flow vertex distance labels).distance[graph.edges[edgeIndex]!.head]! =
      some next ∧ next ≤ distance + graph.edges[edgeIndex]!.cost + flow.potential[vertex]! -
        flow.potential[graph.edges[edgeIndex]!.head]! :=
  fold_head graph flow vertex distance _ labels edgeIndex he hheads ha hs

theorem relax_lower (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) (bound : Int) (hbound : bound ≤ distance)
    (hheads : ∀ edge ∈ graph.outgoing[vertex]!,
      graph.edges[edge]!.head < labels.distance.size ∧ graph.edges[edge]!.head < labels.predecessor.size)
    (hcost : ∀ edge ∈ graph.outgoing[vertex]!, 0 < flow.capacity[edge]! →
      0 ≤ graph.edges[edge]!.cost + flow.potential[vertex]! - flow.potential[graph.edges[edge]!.head]!)
    (hlower : ∀ other value, Candidate labels other value → bound ≤ value) :
    ∀ other value, Candidate (relax graph flow vertex distance labels) other value → bound ≤ value := by
  have hfull : (relax graph flow vertex distance labels).distance.size = labels.distance.size ∧
      (relax graph flow vertex distance labels).predecessor.size = labels.predecessor.size ∧
      ∀ other value, Candidate (relax graph flow vertex distance labels) other value → bound ≤ value := by
    rw [relax_eq_fold]
    refine List.foldlRecOn (motive := fun current : Labels =>
      current.distance.size = labels.distance.size ∧ current.predecessor.size = labels.predecessor.size ∧
      ∀ other value, Candidate current other value → bound ≤ value)
      (graph.outgoing[vertex]!) (relaxStep graph flow vertex distance) ?_ ?_
    · exact ⟨rfl, rfl, hlower⟩
    · intro current hc edge he
      obtain ⟨hd, hp, _⟩ := relaxStep_sizes graph flow vertex distance current edge
      refine ⟨hd.trans hc.1, hp.trans hc.2.1, ?_⟩
      exact relaxStep_lower graph flow vertex distance current edge bound
        (hc.1 ▸ (hheads edge he).1) (hc.2.1 ▸ (hheads edge he).2) hbound (hcost edge he) hc.2.2
  exact hfull.2.2

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Dijkstra
