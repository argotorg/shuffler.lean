import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.NetworkRoutes
import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.FlowPath

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

def Network.cutCapacity (graph : Network) (cut : Finset Nat) : Nat :=
  ∑ index : graph.Edge,
    if graph.edges[index.val]!.tail ∈ cut ∧ graph.edges[index.val]!.head ∉ cut
      then graph.edges[index.val]!.capacity else 0

theorem Network.Contains.le_cutCapacity {graph : Network}
    (ha : graph.Contains before after capacity cost) (hb : before ∈ cut) (he : after ∉ cut) :
    capacity ≤ graph.cutCapacity cut := by
  obtain ⟨index, hi, ht, hh, hc, _⟩ := ha
  have hsum := Finset.single_le_sum
    (f := fun index : graph.Edge =>
      if graph.edges[index.val]!.tail ∈ cut ∧ graph.edges[index.val]!.head ∉ cut
        then graph.edges[index.val]!.capacity else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨index, hi⟩ : graph.Edge))
  simpa [Network.cutCapacity, ht, hh, hc, hb, he] using hsum

theorem cut_large_or_closed (size : Nat) (graph : Network) (cut : Finset Nat) :
    size + 1 ≤ graph.cutCapacity cut ∨
      ∀ before ∈ cut, ∀ after, InternalArc size graph before after → after ∈ cut := by
  by_cases hlarge : size + 1 ≤ graph.cutCapacity cut
  · exact Or.inl hlarge
  · right
    intro before hb after ha
    by_contra hn
    obtain ⟨cost, hedge⟩ := ha
    exact hlarge (hedge.le_cutCapacity hb hn)

theorem Network.cut_lower_of_routes (graph : Network) (assignment : Equiv.Perm (Fin size))
    (hsource : ∀ index : Fin size, graph.Contains (4 * size) index.val 1 0)
    (hsink : ∀ index : Fin size, graph.Contains (size + index.val) (4 * size + 1) 1 0)
    (hroute : ∀ index : Fin size,
      Relation.ReflTransGen (InternalArc size graph) index.val (size + (assignment index).val))
    (cut : Finset Nat) (hstart : 4 * size ∈ cut) (hfinish : 4 * size + 1 ∉ cut) :
    size ≤ graph.cutCapacity cut := by
  classical
  obtain hlarge | hclosed := cut_large_or_closed size graph cut
  · omega
  have hreach {before after : Nat} (hr : Relation.ReflTransGen (InternalArc size graph) before after)
      (hi : before ∈ cut) : after ∈ cut := by
    induction hr with
    | refl => exact hi
    | @tail last finish _ edge ih => exact hclosed last ih finish edge
  have hcolumns (index : Fin size) (hi : index.val ∈ cut) : size + (assignment index).val ∈ cut :=
    hreach (hroute index) hi
  let fromSource : Fin size → graph.Edge := fun index =>
    ⟨(hsource index).choose, (hsource index).choose_spec.1⟩
  let toSink : Fin size → graph.Edge := fun index =>
    ⟨(hsink index).choose, (hsink index).choose_spec.1⟩
  have hfrom (index : Fin size) :
      graph.edges[(fromSource index).val]!.tail = 4 * size ∧
      graph.edges[(fromSource index).val]!.head = index.val ∧
      graph.edges[(fromSource index).val]!.capacity = 1 := by
    exact ⟨(hsource index).choose_spec.2.1, (hsource index).choose_spec.2.2.1,
      (hsource index).choose_spec.2.2.2.1⟩
  have hto (index : Fin size) :
      graph.edges[(toSink index).val]!.tail = size + index.val ∧
      graph.edges[(toSink index).val]!.head = 4 * size + 1 ∧
      graph.edges[(toSink index).val]!.capacity = 1 := by
    exact ⟨(hsink index).choose_spec.2.1, (hsink index).choose_spec.2.2.1,
      (hsink index).choose_spec.2.2.2.1⟩
  let chosen : Fin size → graph.Edge := fun index =>
    if index.val ∈ cut then toSink (assignment index) else fromSource index
  have hinj : Function.Injective chosen := by
    intro first second he
    by_cases hf : first.val ∈ cut <;> by_cases hs : second.val ∈ cut
    · simp only [chosen, hf, hs, ite_true] at he
      have ht := congrArg (fun edge : graph.Edge => graph.edges[edge.val]!.tail) he
      rw [(hto (assignment first)).1, (hto (assignment second)).1] at ht
      apply assignment.injective
      apply Fin.ext
      omega
    · simp only [chosen, hf, hs, ite_true, ite_false] at he
      have ht := congrArg (fun edge : graph.Edge => graph.edges[edge.val]!.tail) he
      rw [(hto (assignment first)).1, (hfrom second).1] at ht
      have hb := (assignment first).isLt
      omega
    · simp only [chosen, hf, hs, ite_true, ite_false] at he
      have ht := congrArg (fun edge : graph.Edge => graph.edges[edge.val]!.tail) he
      rw [(hfrom first).1, (hto (assignment second)).1] at ht
      have hb := (assignment second).isLt
      omega
    · simp only [chosen, hf, hs, ite_false] at he
      have ht := congrArg (fun edge : graph.Edge => graph.edges[edge.val]!.head) he
      rw [(hfrom first).2.1, (hfrom second).2.1] at ht
      exact Fin.ext ht
  let contribution : graph.Edge → Nat := fun index =>
    if graph.edges[index.val]!.tail ∈ cut ∧ graph.edges[index.val]!.head ∉ cut
      then graph.edges[index.val]!.capacity else 0
  have hone (index : Fin size) : contribution (chosen index) = 1 := by
    by_cases hi : index.val ∈ cut
    · simp only [chosen, hi, ite_true, contribution]
      rw [(hto (assignment index)).1, (hto (assignment index)).2.1, (hto (assignment index)).2.2]
      simp [hcolumns index hi, hfinish]
    · simp only [chosen, hi, ite_false, contribution]
      rw [(hfrom index).1, (hfrom index).2.1, (hfrom index).2.2]
      simp [hstart, hi]
  have hsum : (∑ edge ∈ Finset.univ.image chosen, contribution edge) ≤ ∑ edge, contribution edge :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at hsum
  simpa only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    Network.cutCapacity, contribution] using hsum

theorem network_cut_lower [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (assignment : Equiv.Perm (Fin size))
    (ha : ∀ index, EndpointAllowed reach height word target index (assignment index))
    (cut : Finset Nat) (hsource : 4 * size ∈ cut) (hsink : 4 * size + 1 ∉ cut) :
    size ≤ (network reach height word target).cutCapacity cut :=
  Network.cut_lower_of_routes _ assignment
    (network_contains_source reach height word target)
    (network_contains_sink reach height word target)
    (fun index => network_route reach height word target index (assignment index) (ha index))
    cut hsource hsink

namespace FiniteFlow

variable {Vertex Edge : Type*} [DecidableEq Vertex] [Fintype Edge]

def cutCapacity (tail head : Edge → Vertex) (capacity : Edge → Nat) (cut : Finset Vertex) : Nat :=
  ∑ edge, if tail edge ∈ cut ∧ head edge ∉ cut then capacity edge else 0

theorem closed_cut_eq (tail head : Edge → Vertex) (capacity flow : Edge → Nat)
    (hflow : ∀ edge, flow edge ≤ capacity edge) (cut : Finset Vertex)
    (hclosed : ∀ before ∈ cut, ∀ after, Residual tail head capacity flow before after → after ∈ cut) :
    (∑ vertex ∈ cut, divergence tail head flow vertex) = cutCapacity tail head capacity cut := by
  rw [sum_divergence]
  simp only [cutCapacity, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases ht : tail edge ∈ cut <;> by_cases hh : head edge ∈ cut
  · simp [ht, hh]
  · have he : flow edge = capacity edge := by
      have hn : ¬flow edge < capacity edge := fun h =>
        hh (hclosed (tail edge) ht (head edge) ⟨edge, Or.inl ⟨rfl, rfl, h⟩⟩)
      have := hflow edge
      omega
    simp [ht, hh, he]
  · have he : flow edge = 0 := by
      have hn : ¬0 < flow edge := fun h =>
        ht (hclosed (head edge) hh (tail edge) ⟨edge, Or.inr ⟨rfl, rfl, h⟩⟩)
      omega
    simp [ht, hh, he]
  · simp [ht, hh]

theorem residual_path_of_cut [Fintype Vertex]
    (tail head : Edge → Vertex) (capacity flow : Edge → Nat)
    (source sink : Vertex) (value required : Nat)
    (hflow : Feasible tail head capacity flow source sink value) (hlt : value < required)
    (hcut : ∀ cut : Finset Vertex, source ∈ cut → sink ∉ cut →
      required ≤ cutCapacity tail head capacity cut) :
    Relation.ReflTransGen (Residual tail head capacity flow) source sink := by
  classical
  by_contra hn
  let cut := Finset.univ.filter (Relation.ReflTransGen (Residual tail head capacity flow) source)
  have hsource : source ∈ cut := by simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and]; exact .refl
  have hsink : sink ∉ cut := by simpa only [cut, Finset.mem_filter, Finset.mem_univ, true_and] using hn
  have hclosed : ∀ before ∈ cut, ∀ after,
      Residual tail head capacity flow before after → after ∈ cut := by
    intro before hb after ha
    simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb.tail ha
  have he := closed_cut_eq tail head capacity flow hflow.1 cut hclosed
  rw [sum_divergence_eq_value tail head capacity flow source sink value hflow cut hsource hsink] at he
  have hl := hcut cut hsource hsink
  omega

end FiniteFlow

def Network.Feasible (graph : Network) (hw : graph.WellFormed) (flow : graph.Edge → Nat)
    (value : Nat) : Prop :=
  FiniteFlow.Feasible (graph.tail hw) (graph.head hw) (fun edge => graph.edges[edge.val]!.capacity)
    flow ⟨graph.source, hw.source_lt⟩ ⟨graph.sink, hw.sink_lt⟩ value

def Network.Residual (graph : Network) (hw : graph.WellFormed) (flow : graph.Edge → Nat) :
    graph.Vertex → graph.Vertex → Prop :=
  FiniteFlow.Residual (graph.tail hw) (graph.head hw) (fun edge => graph.edges[edge.val]!.capacity) flow

theorem network_residual_path [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (assignment : Equiv.Perm (Fin size))
    (ha : ∀ index, EndpointAllowed reach height word target index (assignment index))
    (flow : (network reach height word target).Edge → Nat) (value : Nat) (hlt : value < size)
    (hflow : (network reach height word target).Feasible (network_wellFormed reach height word target) flow value) :
    Relation.ReflTransGen
      ((network reach height word target).Residual (network_wellFormed reach height word target) flow)
      ⟨(network reach height word target).source, (network_wellFormed reach height word target).source_lt⟩
      ⟨(network reach height word target).sink, (network_wellFormed reach height word target).sink_lt⟩ := by
  apply FiniteFlow.residual_path_of_cut _ _ _ _ _ _ value size hflow hlt
  intro cut hs ht
  have hmem (vertex : (network reach height word target).Vertex) :
      vertex.val ∈ cut.image Fin.val ↔ vertex ∈ cut := by
    constructor
    · intro h
      obtain ⟨other, ho, he⟩ := Finset.mem_image.mp h
      have he' : other = vertex := Fin.ext he
      exact he' ▸ ho
    · exact fun h => Finset.mem_image.mpr ⟨vertex, h, rfl⟩
  have hl := network_layout reach height word target
  have hsource : 4 * size ∈ cut.image Fin.val := by
    rw [← hl.source]
    exact hmem ⟨_, hl.wellFormed.source_lt⟩ |>.mpr hs
  have hsink : 4 * size + 1 ∉ cut.image Fin.val := by
    rw [← hl.sink]
    exact fun h => ht (hmem ⟨_, hl.wellFormed.sink_lt⟩ |>.mp h)
  have hc := network_cut_lower reach height word target assignment ha (cut.image Fin.val) hsource hsink
  suffices he : (network reach height word target).cutCapacity (cut.image Fin.val) =
      FiniteFlow.cutCapacity ((network reach height word target).tail hl.wellFormed)
        ((network reach height word target).head hl.wellFormed)
        (fun edge => (network reach height word target).edges[edge.val]!.capacity) cut by
    exact he ▸ hc
  unfold Network.cutCapacity FiniteFlow.cutCapacity
  apply Finset.sum_congr rfl
  intro edge _
  change (if ((network reach height word target).tail hl.wellFormed edge).val ∈ cut.image Fin.val ∧
      ((network reach height word target).head hl.wellFormed edge).val ∉ cut.image Fin.val then _ else _) = _
  simp only [hmem]

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
