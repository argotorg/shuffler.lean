import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.NetworkFacts
import Mathlib.Logic.Relation
import Mathlib.Data.List.OfFn

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

def Network.Contains (graph : Network) (tail head capacity : Nat) (cost : Int) : Prop :=
  ∃ index, index < graph.edges.size ∧
    graph.edges[index]!.tail = tail ∧ graph.edges[index]!.head = head ∧
      graph.edges[index]!.capacity = capacity ∧ graph.edges[index]!.cost = cost

def Network.Extends (later earlier : Network) : Prop :=
  ∀ tail head capacity cost, earlier.Contains tail head capacity cost → later.Contains tail head capacity cost

theorem Network.Extends.refl (graph : Network) : graph.Extends graph := fun _ _ _ _ h => h

theorem Network.Extends.trans {first second third : Network}
    (h₁ : third.Extends second) (h₂ : second.Extends first) : third.Extends first :=
  fun _ _ _ _ h => h₁ _ _ _ _ (h₂ _ _ _ _ h)

theorem Network.add_extends (graph : Network) (tail head capacity : Nat) (cost : Int) :
    (graph.add tail head capacity cost).Extends graph := by
  intro before after cap price h
  obtain ⟨index, hi, htail, hhead, hcap, hcost⟩ := h
  refine ⟨index, by simpa using (show index < graph.edges.size + 2 by omega), ?_⟩
  rw [graph.add_edge tail head capacity cost index (by omega)]
  simpa only [hi, ite_true] using And.intro htail (And.intro hhead (And.intro hcap hcost))

theorem Network.add_contains (graph : Network) (tail head capacity : Nat) (cost : Int) :
    (graph.add tail head capacity cost).Contains tail head capacity cost := by
  refine ⟨graph.edges.size, by simp, ?_⟩
  rw [graph.add_edge tail head capacity cost graph.edges.size (by omega)]
  simp

theorem addColumn_extends [DecidableEq α] (height : Nat) (target : Fin size → α)
    (graph : Network) (index : Fin size) : (addColumn height target graph index).Extends graph := by
  have h₁ := graph.add_extends (size + index.val) graph.sink 1 0
  have h₂ := (Network.add_extends _ (2 * size + index.val) (size + index.val) (size + 1)
    (if index.val + 1 < height then 1 else 0)).trans h₁
  have h₃ := (Network.add_extends _ (3 * size + index.val) (size + index.val) (size + 1) 0).trans h₂
  cases hfind : (List.finRange size).find?
      (fun next => index.val < next.val && target index == target next) with
  | none => simpa only [addColumn, hfind] using h₃
  | some next =>
      simpa only [addColumn, hfind] using
        (Network.add_extends _ (3 * size + index.val) (3 * size + next.val) (size + 1) 0).trans
          ((Network.add_extends _ (2 * size + index.val) (2 * size + next.val) (size + 1) 0).trans h₃)

theorem addRow_extends [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (graph : Network) (index : Fin size) : (addRow reach height word target graph index).Extends graph := by
  have h₁ := graph.add_extends graph.source index.val 1 0
  have h₂ : (if word index = target index then
      (graph.add graph.source index.val 1 0).add index.val (size + index.val) (size + 1) 0
      else graph.add graph.source index.val 1 0).Extends graph := by
    split
    · exact (Network.add_extends _ index.val (size + index.val) (size + 1) 0).trans h₁
    · exact h₁
  by_cases hf : index.val + reach + 1 < height
  · simpa only [addRow, hf, ite_true] using h₂
  · cases hfind : (List.finRange size).find?
        (fun output => index.val ≤ output.val + reach && word index == target output) with
    | none => simpa only [addRow, hf, ite_false, hfind] using h₂
    | some output =>
        simpa only [addRow, hf, ite_false, hfind] using
          (Network.add_extends _ index.val
            ((if index.val + 1 < height then 2 else 3) * size + output.val) (size + 1) 1).trans h₂

theorem foldl_extends (items : List α) (step : Network → α → Network)
    (hstep : ∀ graph item, (step graph item).Extends graph) (graph : Network) :
    (items.foldl step graph).Extends graph := by
  refine List.foldlRecOn (motive := fun current => current.Extends graph) items step ?_ ?_
  · exact .refl graph
  · intro current hc item _
    exact (hstep current item).trans hc

theorem foldl_contains (items : List α) (step : Network → α → Network)
    (hstep : ∀ graph item, (step graph item).Extends graph)
    (wanted : α) (hw : wanted ∈ items)
    (hnew : ∀ graph, (step graph wanted).Contains tail head capacity cost) (graph : Network) :
    (items.foldl step graph).Contains tail head capacity cost := by
  induction items generalizing graph with
  | nil => simp at hw
  | cons first rest ih =>
      obtain he | hm := List.mem_cons.mp hw
      · subst first
        exact foldl_extends rest step hstep _ _ _ _ _ (hnew graph)
      · exact ih hm (step graph first)

theorem network_eq [DecidableEq α] (reach height : Nat) (word target : Fin size → α) :
    network reach height word target =
      (List.finRange size).foldl (addRow reach height word target)
        ((List.finRange size).foldl (addColumn height target) (emptyNetwork size)) := by
  simp only [network, Vector.getElem_ofFn]

theorem addColumn_prefix [DecidableEq α] (height : Nat) (target : Fin size → α)
    (graph : Network) (index : Fin size) :
    (addColumn height target graph index).Extends
      (((graph.add (size + index.val) graph.sink 1 0).add
        (2 * size + index.val) (size + index.val) (size + 1) (if index.val + 1 < height then 1 else 0)).add
        (3 * size + index.val) (size + index.val) (size + 1) 0) := by
  cases hfind : (List.finRange size).find?
      (fun next => index.val < next.val && target index == target next) with
  | none => simp only [addColumn, hfind]; exact .refl _
  | some next =>
      simp only [addColumn, hfind]
      exact (Network.add_extends _ _ _ _ _).trans (Network.add_extends _ _ _ _ _)

theorem addRow_prefix [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (graph : Network) (index : Fin size) :
    (addRow reach height word target graph index).Extends
      (if word index = target index then
        (graph.add graph.source index.val 1 0).add index.val (size + index.val) (size + 1) 0
        else graph.add graph.source index.val 1 0) := by
  by_cases hf : index.val + reach + 1 < height
  · simp only [addRow, hf, ite_true]; exact .refl _
  · cases hfind : (List.finRange size).find?
        (fun output => index.val ≤ output.val + reach && word index == target output) with
    | none => simp only [addRow, hf, ite_false, hfind]; exact .refl _
    | some output => simp only [addRow, hf, ite_false, hfind]; exact Network.add_extends _ _ _ _ _

theorem network_contains_identity [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (index : Fin size) (hv : word index = target index) :
    (network reach height word target).Contains index.val (size + index.val) (size + 1) 0 := by
  rw [network_eq]
  apply foldl_contains _ _ (addRow_extends reach height word target) index (by simp)
  intro graph
  apply addRow_prefix reach height word target graph index
  simpa only [hv, ite_true] using
    Network.add_contains (graph.add graph.source index.val 1 0) index.val (size + index.val) (size + 1) 0

theorem network_contains_exit [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (index : Fin size) (interior : Bool) :
    (network reach height word target).Contains
      ((if interior then 2 else 3) * size + index.val) (size + index.val) (size + 1)
      (if interior && decide (index.val + 1 < height) then 1 else 0) := by
  rw [network_eq]
  apply foldl_extends _ _ (addRow_extends reach height word target)
  apply foldl_contains _ _ (addColumn_extends height target) index (by simp)
  intro graph
  apply addColumn_prefix height target graph index
  cases interior
  · simpa using Network.add_contains
      (((graph.add (size + index.val) graph.sink 1 0).add
        (2 * size + index.val) (size + index.val) (size + 1) (if index.val + 1 < height then 1 else 0)))
      (3 * size + index.val) (size + index.val) (size + 1) 0
  · apply Network.add_extends _ _ _ _ _
    simpa using Network.add_contains (graph.add (size + index.val) graph.sink 1 0)
      (2 * size + index.val) (size + index.val) (size + 1) (if index.val + 1 < height then 1 else 0)

theorem network_contains_next [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (index next : Fin size) (interior : Bool)
    (hfind : (List.finRange size).find?
      (fun j => index.val < j.val && target index == target j) = some next) :
    (network reach height word target).Contains
      ((if interior then 2 else 3) * size + index.val)
      ((if interior then 2 else 3) * size + next.val) (size + 1) 0 := by
  rw [network_eq]
  apply foldl_extends _ _ (addRow_extends reach height word target)
  apply foldl_contains _ _ (addColumn_extends height target) index (by simp)
  intro graph
  simp only [addColumn, hfind]
  cases interior
  · exact Network.add_contains _ _ _ _ _
  · exact Network.add_extends _ _ _ _ _ _ _ _ _ (Network.add_contains _ _ _ _ _)

theorem network_contains_entry [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (index first : Fin size) (hf : ¬index.val + reach + 1 < height)
    (hfind : (List.finRange size).find?
      (fun j => index.val ≤ j.val + reach && word index == target j) = some first) :
    (network reach height word target).Contains index.val
      ((if index.val + 1 < height then 2 else 3) * size + first.val) (size + 1) 1 := by
  rw [network_eq]
  apply foldl_contains _ _ (addRow_extends reach height word target) index (by simp)
  intro graph
  simp only [addRow, hf, ite_false, hfind]
  exact Network.add_contains _ _ _ _ _

theorem find_finRange_le (predicate : Fin size → Bool) (candidate : Fin size)
    (hc : predicate candidate = true) :
    ∃ first, (List.finRange size).find? predicate = some first ∧
      predicate first = true ∧ first.val ≤ candidate.val := by
  cases hfind : (List.finRange size).find? predicate with
  | none => exact False.elim ((List.find?_eq_none.mp hfind candidate (by simp)) hc)
  | some first =>
      refine ⟨first, rfl, List.find?_some hfind, ?_⟩
      have hm := List.find?_ofFn_eq_some.mp hfind
      obtain ⟨_, index, he, hbefore⟩ := hm
      subst index
      by_contra hn
      exact hbefore candidate (by omega) hc

def InternalArc (size : Nat) (graph : Network) (before after : Nat) : Prop :=
  ∃ cost, graph.Contains before after (size + 1) cost

theorem network_chain [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (first last : Fin size) (interior : Bool) (hle : first.val ≤ last.val)
    (hvalue : target first = target last) :
    Relation.ReflTransGen (InternalArc size (network reach height word target))
      ((if interior then 2 else 3) * size + first.val)
      ((if interior then 2 else 3) * size + last.val) := by
  by_cases he : first = last
  · subst last; exact .refl
  · have hlt : first.val < last.val := by have hn := Fin.val_ne_of_ne he; omega
    obtain ⟨next, hfind, hp, hn⟩ := find_finRange_le
      (fun j => first.val < j.val && target first == target j) last (by simp [hlt, hvalue])
    have hp' : first.val < next.val ∧ target first = target next := by simpa using hp
    exact (Relation.ReflTransGen.single ⟨0,
      network_contains_next reach height word target first next interior hfind⟩).trans
        (network_chain reach height word target next last interior hn (hp'.2.symm.trans hvalue))
termination_by last.val - first.val
decreasing_by omega

theorem network_route [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (before after : Fin size) (ha : EndpointAllowed reach height word target before after) :
    Relation.ReflTransGen (InternalArc size (network reach height word target))
      before.val (size + after.val) := by
  by_cases he : before = after
  · subst after
    exact .single ⟨0, network_contains_identity reach height word target before ha.1⟩
  · have hf : ¬before.val + reach + 1 < height := fun h => he (ha.2.2 h).symm
    obtain ⟨first, hfind, hp, hn⟩ := find_finRange_le
      (fun j => before.val ≤ j.val + reach && word before == target j) after (by simp [ha.1, ha.2.1])
    have hp' : before.val ≤ first.val + reach ∧ word before = target first := by simpa using hp
    let interior := decide (before.val + 1 < height)
    have heq : (if interior then 2 else 3) = (if before.val + 1 < height then 2 else 3) := by
      simp [interior]
    have hentry : InternalArc size (network reach height word target) before.val
        ((if interior then 2 else 3) * size + first.val) :=
      ⟨1, by rw [heq]; exact network_contains_entry reach height word target before first hf hfind⟩
    exact (Relation.ReflTransGen.single hentry).trans
      ((network_chain reach height word target first after interior hn (hp'.2.symm.trans ha.1)).tail
        ⟨_, network_contains_exit reach height word target after interior⟩)

theorem foldl_contains_with (invariant : Network → Prop) (items : List α) (step : Network → α → Network)
    (hstep : ∀ graph item, (step graph item).Extends graph)
    (hkeep : ∀ graph, invariant graph → ∀ item, invariant (step graph item))
    (wanted : α) (hw : wanted ∈ items)
    (hnew : ∀ graph, invariant graph → (step graph wanted).Contains tail head capacity cost)
    (graph : Network) (hg : invariant graph) :
    (items.foldl step graph).Contains tail head capacity cost := by
  induction items generalizing graph with
  | nil => simp at hw
  | cons first rest ih =>
      obtain he | hm := List.mem_cons.mp hw
      · subst first
        exact foldl_extends rest step hstep _ _ _ _ _ (hnew graph hg)
      · exact ih hm (step graph first) (hkeep graph hg first)

theorem network_contains_source [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (index : Fin size) :
    (network reach height word target).Contains (4 * size) index.val 1 0 := by
  rw [network_eq]
  apply foldl_contains_with (Layout size) _ _ (addRow_extends reach height word target)
    (fun _ hl item => addRow_layout reach height word target hl item) index (by simp)
  · intro graph hl
    apply addRow_prefix reach height word target graph index
    have he : (graph.add graph.source index.val 1 0).Contains (4 * size) index.val 1 0 := by
      rw [← hl.source]
      exact Network.add_contains _ _ _ _ _
    split
    · exact Network.add_extends _ _ _ _ _ _ _ _ _ he
    · exact he
  · apply List.foldlRecOn
    · exact emptyNetwork_layout size
    · intro graph hl item _
      exact addColumn_layout height target hl item

theorem network_contains_sink [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (index : Fin size) :
    (network reach height word target).Contains (size + index.val) (4 * size + 1) 1 0 := by
  rw [network_eq]
  apply foldl_extends _ _ (addRow_extends reach height word target)
  apply foldl_contains_with (Layout size) _ _ (addColumn_extends height target)
    (fun _ hl item => addColumn_layout height target hl item) index (by simp)
  · intro graph hl
    apply addColumn_prefix height target graph index
    apply Network.add_extends _ _ _ _ _
    apply Network.add_extends _ _ _ _ _
    rw [← hl.sink]
    exact Network.add_contains _ _ _ _ _
  · exact emptyNetwork_layout size

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
