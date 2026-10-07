import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.FlowPath

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

namespace Potential

variable {Vertex Edge : Type*}

def reduced (tail head : Edge → Vertex) (cost : Edge → Int) (price : Vertex → Int)
    (edge : Edge) : Int := cost edge + price (tail edge) - price (head edge)

def Feasible (tail head : Edge → Vertex) (cost : Edge → Int) (active : Edge → Prop)
    (price : Vertex → Int) : Prop :=
  ∀ edge, active edge → 0 ≤ reduced tail head cost price edge

theorem update_feasible (tail head : Edge → Vertex) (cost : Edge → Int)
    (active : Edge → Prop) (price change : Vertex → Int)
    (htriangle : ∀ edge, active edge →
      change (head edge) ≤ change (tail edge) + reduced tail head cost price edge) :
    Feasible tail head cost active (fun vertex => price vertex + change vertex) := by
  intro edge he
  have ht := htriangle edge he
  dsimp only [reduced] at ht ⊢
  omega

theorem update_tight (tail head : Edge → Vertex) (cost : Edge → Int)
    (price change : Vertex → Int) (edge : Edge)
    (htight : change (head edge) = change (tail edge) + reduced tail head cost price edge) :
    reduced tail head cost (fun vertex => price vertex + change vertex) edge = 0 := by
  dsimp only [reduced] at htight ⊢
  omega

-- Vertices not reached by the search receive the sink distance too.
def truncate (limit : Int) : Option Int → Int
  | none => limit
  | some distance => min distance limit

theorem truncate_le (limit : Int) (distance : Option Int) : truncate limit distance ≤ limit := by
  cases distance with
  | none => exact le_refl _
  | some value => exact min_le_right _ _

theorem truncate_eq (limit : Int) (distance : Option Int)
    (hlarge : ∀ value, distance = some value → limit ≤ value) :
    truncate limit distance = limit := by
  cases distance with
  | none => rfl
  | some value => exact min_eq_right (hlarge value rfl)

theorem truncate_triangle (limit before after weight : Int) (hweight : 0 ≤ weight)
    (htriangle : after ≤ before + weight) :
    truncate limit (some after) ≤ truncate limit (some before) + weight := by
  simp only [truncate]
  by_cases hb : before ≤ limit
  · rw [min_eq_left hb]
    exact (min_le_left _ _).trans htriangle
  · rw [min_eq_right (by omega : limit ≤ before)]
    have := min_le_right after limit
    omega

-- At the early sink stop, every unsettled label is at least the sink label.
-- Scanned edges supply the other case of the triangle inequality.
theorem stopped_triangle (tail head : Edge → Vertex) (cost : Edge → Int)
    (active : Edge → Prop) (price : Vertex → Int) (distance : Vertex → Option Int)
    (settled : Vertex → Prop) (limit : Int)
    (hfeasible : Feasible tail head cost active price)
    (hfrontier : ∀ vertex, ¬settled vertex → ∀ value,
      distance vertex = some value → limit ≤ value)
    (hscanned : ∀ edge, active edge → settled (tail edge) →
      ∃ before after, distance (tail edge) = some before ∧ distance (head edge) = some after ∧
        after ≤ before + reduced tail head cost price edge) :
    ∀ edge, active edge → truncate limit (distance (head edge)) ≤
      truncate limit (distance (tail edge)) + reduced tail head cost price edge := by
  intro edge he
  classical
  by_cases hs : settled (tail edge)
  · obtain ⟨before, after, hb, ha, ht⟩ := hscanned edge he hs
    rw [hb, ha]
    exact truncate_triangle limit before after _ (hfeasible edge he) ht
  · rw [truncate_eq limit _ (hfrontier _ hs)]
    have := truncate_le limit (distance (head edge))
    have := hfeasible edge he
    omega

theorem stopped_update_feasible (tail head : Edge → Vertex) (cost : Edge → Int)
    (active : Edge → Prop) (price : Vertex → Int) (distance : Vertex → Option Int)
    (settled : Vertex → Prop) (limit : Int)
    (hfeasible : Feasible tail head cost active price)
    (hfrontier : ∀ vertex, ¬settled vertex → ∀ value,
      distance vertex = some value → limit ≤ value)
    (hscanned : ∀ edge, active edge → settled (tail edge) →
      ∃ before after, distance (tail edge) = some before ∧ distance (head edge) = some after ∧
        after ≤ before + reduced tail head cost price edge) :
    Feasible tail head cost active (fun vertex => price vertex + truncate limit (distance vertex)) :=
  update_feasible tail head cost active price _
    (stopped_triangle tail head cost active price distance settled limit hfeasible hfrontier hscanned)

theorem stopped_update_tight (tail head : Edge → Vertex) (cost : Edge → Int)
    (price : Vertex → Int) (distance : Vertex → Option Int) (limit before after : Int)
    (edge : Edge) (hb : distance (tail edge) = some before) (ha : distance (head edge) = some after)
    (hbefore : before ≤ limit) (hafter : after ≤ limit)
    (htight : after = before + reduced tail head cost price edge) :
    reduced tail head cost (fun vertex => price vertex + truncate limit (distance vertex)) edge = 0 := by
  apply update_tight
  simpa only [hb, ha, truncate, min_eq_left hbefore, min_eq_left hafter] using htight

theorem reverse_reduced (tail head : Edge → Vertex) (cost : Edge → Int) (price : Vertex → Int)
    (edge reverse : Edge) (htail : tail reverse = head edge) (hhead : head reverse = tail edge)
    (hcost : cost reverse = -cost edge) :
    reduced tail head cost price reverse = -reduced tail head cost price edge := by
  unfold reduced
  rw [htail, hhead, hcost]
  omega

-- A new residual edge reverses an edge of the tight augmenting path.
theorem augment_feasible (tail head : Edge → Vertex) (cost : Edge → Int)
    (active next path : Edge → Prop) (price : Vertex → Int)
    (hfeasible : Feasible tail head cost active price)
    (htight : ∀ edge, path edge → reduced tail head cost price edge = 0)
    (hnext : ∀ edge, next edge → active edge ∨ ∃ prior, path prior ∧
      tail edge = head prior ∧ head edge = tail prior ∧ cost edge = -cost prior) :
    Feasible tail head cost next price := by
  intro edge he
  rcases hnext edge he with hold | ⟨prior, hp, ht, hh, hc⟩
  · exact hfeasible edge hold
  · rw [reverse_reduced tail head cost price prior edge ht hh hc, htight prior hp]
    omega

end Potential

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
