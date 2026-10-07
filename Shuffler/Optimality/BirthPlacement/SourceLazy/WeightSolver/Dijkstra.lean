import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.ShortestPath
import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Potential

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

namespace Dijkstra

def Candidate (labels : Labels) (vertex : Nat) (distance : Int) : Prop :=
  labels.settled[vertex]! = false ∧ labels.distance[vertex]! = some distance

private abbrev select (labels : Labels) (best : Option (Nat × Int)) (index : Nat) :=
  if labels.settled[index]! then best
  else match labels.distance[index]!, best with
    | none, _ => best
    | some distance, none => some (index, distance)
    | some distance, some (_, prior) => if distance < prior then some (index, distance) else best

private def Below (best : Option (Nat × Int)) (bound : Int) : Prop :=
  ∃ vertex distance, best = some (vertex, distance) ∧ distance ≤ bound

private theorem select_below (labels : Labels) (best : Option (Nat × Int)) (index : Nat)
    (bound : Int) (hbest : Below best bound) : Below (select labels best index) bound := by
  obtain ⟨vertex, distance, rfl, hd⟩ := hbest
  cases hs : labels.settled[index]! with
  | true => simpa only [select, hs, ite_true] using (show Below (some (vertex, distance)) bound from
      ⟨vertex, distance, rfl, hd⟩)
  | false =>
      cases hh : labels.distance[index]! with
      | none => exact ⟨vertex, distance, by simp [select, hs, hh], hd⟩
      | some found =>
          by_cases hf : found < distance
          · exact ⟨index, found, by simp [select, hs, hh, hf], by omega⟩
          · exact ⟨vertex, distance, by simp [select, hs, hh, hf], hd⟩

private theorem select_self (labels : Labels) (best : Option (Nat × Int)) (index : Nat)
    (distance : Int) (hc : Candidate labels index distance) :
    Below (select labels best index) distance := by
  cases best with
  | none => exact ⟨index, distance, by simp [select, hc.1, hc.2], le_refl _⟩
  | some pair =>
      obtain ⟨vertex, prior⟩ := pair
      by_cases hl : distance < prior
      · exact ⟨index, distance, by simp [select, hc.1, hc.2, hl], le_refl _⟩
      · exact ⟨vertex, prior, by simp [select, hc.1, hc.2, hl], by omega⟩

private theorem fold_below (labels : Labels) (indices : List Nat) (best : Option (Nat × Int))
    (bound : Int) (hbest : Below best bound) :
    Below (indices.foldl (select labels) best) bound := by
  induction indices generalizing best with
  | nil => exact hbest
  | cons index rest ih => exact ih _ (select_below labels best index bound hbest)

private theorem fold_candidate (labels : Labels) (indices : List Nat) (best : Option (Nat × Int))
    (index : Nat) (distance : Int) (hi : index ∈ indices) (hc : Candidate labels index distance) :
    Below (indices.foldl (select labels) best) distance := by
  induction indices generalizing best with
  | nil => simp at hi
  | cons first rest ih =>
      rcases List.mem_cons.mp hi with rfl | hi
      · exact fold_below labels rest _ distance (select_self labels best index distance hc)
      · exact ih _ hi

private theorem fold_valid (labels : Labels) (indices : List Nat) (best : Option (Nat × Int))
    (hbest : ∀ vertex distance, best = some (vertex, distance) →
      vertex < labels.distance.size ∧ Candidate labels vertex distance)
    (hindices : ∀ index ∈ indices, index < labels.distance.size) :
    ∀ vertex distance, indices.foldl (select labels) best = some (vertex, distance) →
      vertex < labels.distance.size ∧ Candidate labels vertex distance := by
  induction indices generalizing best with
  | nil => exact hbest
  | cons index rest ih =>
      apply ih
      · intro vertex distance he
        unfold select at he
        split at he
        · exact hbest vertex distance he
        · split at he
          · exact hbest vertex distance he
          · cases he
            exact ⟨hindices index (by simp), by simp_all [Candidate]⟩
          · split at he
            · cases he
              exact ⟨hindices index (by simp), by simp_all [Candidate]⟩
            · exact hbest vertex distance he
      · intro vertex hv
        exact hindices vertex (by simp [hv])

theorem least_valid (labels : Labels) (vertex : Nat) (distance : Int)
    (he : leastUnsettled labels = some (vertex, distance)) :
    vertex < labels.distance.size ∧ Candidate labels vertex distance :=
  fold_valid labels (List.range labels.distance.size) none
    (by intro _ _ h; cases h) (by intro index hi; exact List.mem_range.mp hi) vertex distance he

theorem least_le (labels : Labels) (vertex : Nat) (distance : Int)
    (he : leastUnsettled labels = some (vertex, distance))
    (other : Nat) (value : Int) (hother : other < labels.distance.size)
    (hc : Candidate labels other value) : distance ≤ value := by
  obtain ⟨found, cost, hf, hb⟩ := fold_candidate labels (List.range labels.distance.size) none
    other value (List.mem_range.mpr hother) hc
  change leastUnsettled labels = some (found, cost) at hf
  rw [he] at hf
  cases hf
  exact hb

theorem least_exists (labels : Labels) (other : Nat) (value : Int)
    (hother : other < labels.distance.size) (hc : Candidate labels other value) :
    ∃ vertex distance, leastUnsettled labels = some (vertex, distance) := by
  obtain ⟨vertex, distance, he, _⟩ := fold_candidate labels (List.range labels.distance.size) none
    other value (List.mem_range.mpr hother) hc
  exact ⟨vertex, distance, he⟩

end Dijkstra

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
