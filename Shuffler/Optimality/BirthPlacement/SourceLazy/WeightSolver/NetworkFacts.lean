import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Network

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

structure Network.WellFormed (graph : Network) : Prop where
  source_lt : graph.source < graph.outgoing.size
  sink_lt : graph.sink < graph.outgoing.size
  edge_bounds : ∀ index, index < graph.edges.size →
    graph.edges[index]!.tail < graph.outgoing.size ∧
      graph.edges[index]!.head < graph.outgoing.size ∧
      graph.edges[index]!.reverse < graph.edges.size
  reverse : ∀ index, index < graph.edges.size →
    let edge := graph.edges[index]!
    let back := graph.edges[edge.reverse]!
    back.tail = edge.head ∧ back.head = edge.tail ∧
      back.reverse = index ∧ back.cost = -edge.cost
  outgoing : ∀ vertex, vertex < graph.outgoing.size → ∀ index,
    index ∈ graph.outgoing[vertex]! ↔
      index < graph.edges.size ∧ graph.edges[index]!.tail = vertex

abbrev Network.Vertex (graph : Network) := Fin graph.outgoing.size
abbrev Network.Edge (graph : Network) := Fin graph.edges.size

def Network.tail (graph : Network) (hw : graph.WellFormed) (edge : graph.Edge) : graph.Vertex :=
  ⟨graph.edges[edge.val]!.tail, (hw.edge_bounds edge.val edge.isLt).1⟩

def Network.head (graph : Network) (hw : graph.WellFormed) (edge : graph.Edge) : graph.Vertex :=
  ⟨graph.edges[edge.val]!.head, (hw.edge_bounds edge.val edge.isLt).2.1⟩

def Network.back (graph : Network) (hw : graph.WellFormed) (edge : graph.Edge) : graph.Edge :=
  ⟨graph.edges[edge.val]!.reverse, (hw.edge_bounds edge.val edge.isLt).2.2⟩

@[simp] theorem Network.add_source (graph : Network) (tail head capacity : Nat) (cost : Int) :
    (graph.add tail head capacity cost).source = graph.source := rfl

@[simp] theorem Network.add_sink (graph : Network) (tail head capacity : Nat) (cost : Int) :
    (graph.add tail head capacity cost).sink = graph.sink := rfl

@[simp] theorem Network.add_outgoing_size (graph : Network) (tail head capacity : Nat) (cost : Int) :
    (graph.add tail head capacity cost).outgoing.size = graph.outgoing.size := by
  simp [Network.add]

@[simp] theorem Network.add_edges_size (graph : Network) (tail head capacity : Nat) (cost : Int) :
    (graph.add tail head capacity cost).edges.size = graph.edges.size + 2 := by
  simp [Network.add, Nat.add_assoc]

theorem Network.add_edge (graph : Network) (tail head capacity : Nat) (cost : Int)
    (index : Nat) (hi : index < graph.edges.size + 2) :
    (graph.add tail head capacity cost).edges[index]! =
      if index < graph.edges.size then graph.edges[index]!
      else if index = graph.edges.size then ⟨tail, head, capacity, cost, graph.edges.size + 1⟩
      else ⟨head, tail, 0, -cost, graph.edges.size⟩ := by
  have hh : index < (graph.add tail head capacity cost).edges.size := by simp; omega
  rw [getElem!_pos (graph.add tail head capacity cost).edges index hh]
  simp only [Network.add, Array.getElem_push, Array.size_push]
  split_ifs <;> simp_all [getElem!_pos] <;> omega

private theorem array_set_read [Inhabited α] (xs : Array α) (i j : Nat) (value : α)
    (hi : i < xs.size) : (xs.set! i value)[j]! = if i = j then value else xs[j]! := by
  by_cases he : i = j
  · subst j
    rw [Array.getElem!_set!_self xs i value hi]
    simp
  · rw [Array.getElem!_set!_ne xs i j value he]
    simp [he]

theorem Network.add_outgoing (graph : Network) (tail head capacity : Nat) (cost : Int)
    (ht : tail < graph.outgoing.size) (hh : head < graph.outgoing.size) (vertex : Nat) :
    (graph.add tail head capacity cost).outgoing[vertex]! =
      (if head = vertex then [graph.edges.size + 1] else []) ++
        (if tail = vertex then [graph.edges.size] else []) ++ graph.outgoing[vertex]! := by
  simp only [Network.add, array_set_read, Array.size_set!, ht, hh]
  split_ifs <;> subst_vars <;> simp_all

theorem Network.WellFormed.add {graph : Network} {tail head capacity : Nat} {cost : Int}
    (hw : graph.WellFormed)
    (ht : tail < graph.outgoing.size) (hh : head < graph.outgoing.size) :
    (graph.add tail head capacity cost).WellFormed := by
  constructor
  · simpa using hw.source_lt
  · simpa using hw.sink_lt
  · intro index hi
    have hbound : index < graph.edges.size + 2 := by simpa using hi
    rw [graph.add_edge tail head capacity cost index hbound]
    simp only [Network.add_outgoing_size, Network.add_edges_size]
    split_ifs with hold he
    · obtain ⟨h₁, h₂, h₃⟩ := hw.edge_bounds index hold
      exact ⟨h₁, h₂, by omega⟩
    · exact ⟨ht, hh, by simp⟩
    · exact ⟨hh, ht, by simp⟩
  · intro index hi
    have hbound : index < graph.edges.size + 2 := by simpa using hi
    dsimp only
    rw [graph.add_edge tail head capacity cost index hbound]
    by_cases hold : index < graph.edges.size
    · simp only [hold, ite_true]
      have hr := (hw.edge_bounds index hold).2.2
      rw [graph.add_edge tail head capacity cost _ (by omega)]
      simpa only [hr, ite_true] using hw.reverse index hold
    · simp only [hold, ite_false]
      by_cases he : index = graph.edges.size
      · subst index
        simp only [ite_true]
        rw [graph.add_edge tail head capacity cost (graph.edges.size + 1) (by omega)]
        simp
      · have he' : index = graph.edges.size + 1 := by omega
        subst index
        simp only [he, ite_false]
        rw [graph.add_edge tail head capacity cost graph.edges.size (by omega)]
        simp
  · intro vertex hv index
    have hv' : vertex < graph.outgoing.size := by simpa using hv
    rw [graph.add_outgoing tail head capacity cost ht hh vertex]
    have hm (condition : Prop) [Decidable condition] (items : List Nat) :
        index ∈ (if condition then items else []) ↔ condition ∧ index ∈ items := by
      split_ifs <;> simp_all
    simp only [List.mem_append, hm, List.mem_singleton, hw.outgoing vertex hv',
      Network.add_edges_size]
    by_cases hi : index < graph.edges.size + 2
    · rw [graph.add_edge tail head capacity cost index hi]
      split_ifs <;> simp_all <;> omega
    · have hlo : ¬index < graph.edges.size := by omega
      have hn : index ≠ graph.edges.size := by omega
      have hn' : index ≠ graph.edges.size + 1 := by omega
      simp [hi, hlo, hn, hn']

structure Layout (size : Nat) (graph : Network) : Prop where
  wellFormed : graph.WellFormed
  vertices : graph.outgoing.size = 4 * size + 2
  source : graph.source = 4 * size
  sink : graph.sink = 4 * size + 1

theorem Layout.add {graph : Network} (hl : Layout size graph)
    (ht : tail < 4 * size + 2) (hh : head < 4 * size + 2) :
    Layout size (graph.add tail head capacity cost) :=
  ⟨hl.wellFormed.add (by rwa [hl.vertices]) (by rwa [hl.vertices]),
    by simpa using hl.vertices, hl.source, hl.sink⟩

theorem emptyNetwork_layout (size : Nat) : Layout size (emptyNetwork size) := by
  constructor
  · constructor
    · simp [emptyNetwork]
    · simp [emptyNetwork]
    · simp [emptyNetwork]
    · simp [emptyNetwork]
    · intro vertex hv index
      rw [getElem!_pos (emptyNetwork size).outgoing vertex hv]
      simp [emptyNetwork]
  · simp [emptyNetwork]
  · rfl
  · rfl

theorem addColumn_layout [DecidableEq α] (height : Nat) (target : Fin size → α)
    {graph : Network} (hl : Layout size graph) (index : Fin size) :
    Layout size (addColumn height target graph index) := by
  have hi := index.isLt
  have hs : graph.sink < 4 * size + 2 := by rw [hl.sink]; omega
  have h₁ := hl.add (tail := size + index.val) (capacity := 1) (cost := 0) (by omega) hs
  have h₂ := h₁.add (tail := 2 * size + index.val) (head := size + index.val)
    (capacity := size + 1) (cost := if index.val + 1 < height then 1 else 0) (by omega) (by omega)
  have h₃ := h₂.add (tail := 3 * size + index.val) (head := size + index.val)
    (capacity := size + 1) (cost := 0) (by omega) (by omega)
  cases hfind : (List.finRange size).find?
      (fun next => index.val < next.val && target index == target next) with
  | none => simpa only [addColumn, hfind] using h₃
  | some next =>
    have hn := next.isLt
    simpa only [addColumn, hfind] using
      (h₃.add (head := 2 * size + next.val) (tail := 2 * size + index.val)
        (capacity := size + 1) (cost := 0) (by omega) (by omega)).add
        (head := 3 * size + next.val) (tail := 3 * size + index.val)
        (capacity := size + 1) (cost := 0) (by omega) (by omega)

theorem addRow_layout [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    {graph : Network} (hl : Layout size graph) (index : Fin size) :
    Layout size (addRow reach height word target graph index) := by
  have hi := index.isLt
  have hs : graph.source < 4 * size + 2 := by rw [hl.source]; omega
  have h₁ := hl.add (tail := graph.source) (head := index.val) (capacity := 1) (cost := 0) hs (by omega)
  have h₂ : Layout size (if word index = target index then
      (graph.add graph.source index.val 1 0).add index.val (size + index.val) (size + 1) 0
      else graph.add graph.source index.val 1 0) := by
    split
    · exact h₁.add (by omega) (by omega)
    · exact h₁
  by_cases hf : index.val + reach + 1 < height
  · simpa only [addRow, hf, ite_true] using h₂
  · cases hfind : (List.finRange size).find?
        (fun output => index.val ≤ output.val + reach && word index == target output) with
    | none => simpa only [addRow, hf, ite_false, hfind] using h₂
    | some output =>
      have ho := output.isLt
      have hb : (if index.val + 1 < height then 2 else 3) * size + output.val < 4 * size + 2 := by
        split_ifs <;> omega
      simpa only [addRow, hf, ite_false, hfind] using h₂.add
        (tail := index.val) (capacity := size + 1) (cost := 1) (by omega) hb

theorem network_layout [DecidableEq α] (reach height : Nat) (word target : Fin size → α) :
    Layout size (network reach height word target) := by
  unfold network
  apply List.foldlRecOn
  · apply List.foldlRecOn
    · exact emptyNetwork_layout size
    · intro graph hl index _
      exact addColumn_layout _ _ hl index
  · intro graph hl index _
    exact addRow_layout _ _ _ _ hl index

theorem network_wellFormed [DecidableEq α] (reach height : Nat) (word target : Fin size → α) :
    (network reach height word target).WellFormed :=
  (network_layout reach height word target).wellFormed

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
