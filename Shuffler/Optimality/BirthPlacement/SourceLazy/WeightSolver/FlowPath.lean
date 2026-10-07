import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightCertificate
import Mathlib.Logic.Relation

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.FiniteFlow

variable {Vertex Edge : Type*} [DecidableEq Vertex] [Fintype Edge]

def divergence (tail head : Edge → Vertex) (flow : Edge → Nat) (vertex : Vertex) : Int :=
  ∑ edge, ((if tail edge = vertex then (flow edge : Int) else 0) -
    if head edge = vertex then (flow edge : Int) else 0)

def Feasible (tail head : Edge → Vertex) (capacity flow : Edge → Nat)
    (source sink : Vertex) (value : Nat) : Prop :=
  (∀ edge, flow edge ≤ capacity edge) ∧
    ∀ vertex, divergence tail head flow vertex =
      (if vertex = source then (value : Int) else 0) -
        if vertex = sink then (value : Int) else 0

def Residual (tail head : Edge → Vertex) (capacity flow : Edge → Nat)
    (before after : Vertex) : Prop :=
  ∃ edge, (tail edge = before ∧ head edge = after ∧ flow edge < capacity edge) ∨
    (head edge = before ∧ tail edge = after ∧ 0 < flow edge)

theorem sum_divergence (tail head : Edge → Vertex) (flow : Edge → Nat)
    (cut : Finset Vertex) :
    ∑ vertex ∈ cut, divergence tail head flow vertex =
      ∑ edge, ((if tail edge ∈ cut then (flow edge : Int) else 0) -
        if head edge ∈ cut then (flow edge : Int) else 0) := by
  simp only [divergence, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := cut)]
  simp [eq_comm]

theorem sum_divergence_eq_value (tail head : Edge → Vertex) (capacity flow : Edge → Nat)
    (source sink : Vertex) (value : Nat) (hflow : Feasible tail head capacity flow source sink value)
    (cut : Finset Vertex) (hsource : source ∈ cut) (hsink : sink ∉ cut) :
    ∑ vertex ∈ cut, divergence tail head flow vertex = (value : Int) := by
  simp_rw [hflow.2]
  simp [Finset.sum_sub_distrib, hsource, hsink]

-- A cut with no residual exit has no room for a flow with a larger value.
theorem cut_bound (tail head : Edge → Vertex) (capacity flow other : Edge → Nat)
    (hflow : ∀ edge, flow edge ≤ capacity edge)
    (hother : ∀ edge, other edge ≤ capacity edge) (cut : Finset Vertex)
    (hclosed : ∀ before ∈ cut, ∀ after, Residual tail head capacity flow before after → after ∈ cut) :
    (∑ vertex ∈ cut, divergence tail head other vertex) ≤
      ∑ vertex ∈ cut, divergence tail head flow vertex := by
  rw [sum_divergence, sum_divergence]
  apply Finset.sum_le_sum
  intro edge _
  by_cases ht : tail edge ∈ cut
  · by_cases hh : head edge ∈ cut
    · simp [ht, hh]
    · have he : flow edge = capacity edge := by
        have hn : ¬flow edge < capacity edge := by
          intro hlt
          exact hh (hclosed (tail edge) ht (head edge) ⟨edge, Or.inl ⟨rfl, rfl, hlt⟩⟩)
        have := hflow edge
        omega
      simp only [ht, hh, ite_true, ite_false, sub_zero]
      exact_mod_cast he ▸ hother edge
  · by_cases hh : head edge ∈ cut
    · have he : flow edge = 0 := by
        have hn : ¬0 < flow edge := by
          intro hlt
          exact ht (hclosed (head edge) hh (tail edge) ⟨edge, Or.inr ⟨rfl, rfl, hlt⟩⟩)
        omega
      simp [ht, hh, he]
    · simp [ht, hh]

theorem residual_path [Fintype Vertex] (tail head : Edge → Vertex) (capacity flow other : Edge → Nat)
    (source sink : Vertex) (value larger : Nat)
    (hflow : Feasible tail head capacity flow source sink value)
    (hother : Feasible tail head capacity other source sink larger)
    (hlt : value < larger) :
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
  have he := cut_bound tail head capacity flow other hflow.1 hother.1 cut hclosed
  rw [sum_divergence_eq_value tail head capacity other source sink larger hother cut hsource hsink,
    sum_divergence_eq_value tail head capacity flow source sink value hflow cut hsource hsink] at he
  omega

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.FiniteFlow
