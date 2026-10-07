import Shuffler.Optimality.ValueGraph.Euler

namespace Shuffler.Optimality.ValueGraph

section Trail

variable {ι : Type} {start finish : ι → Value} {first last : Value} {edges : List ι}

theorem Trail.head (h : Trail start finish first last edges) (hne : 0 < edges.length) :
    start edges[0] = first := by
  cases edges with
  | nil => simp at hne
  | cons edge rest => exact h.1.symm

theorem Trail.adjacent (h : Trail start finish first last edges)
    (i : Nat) (hi : i + 1 < edges.length) :
    finish (edges[i]'(by omega)) = start edges[i + 1] := by
  induction edges generalizing first i with
  | nil => simp at hi
  | cons edge rest ih =>
      cases i with
      | zero =>
          cases rest with
          | nil => simp at hi
          | cons next tail => exact h.2.1
      | succ i =>
          exact ih h.2 i (by simp only [List.length_cons] at hi; omega)

theorem Trail.last_value (h : Trail start finish first last edges) (i : Nat)
    (hi : i < edges.length) (hlast : i + 1 = edges.length) :
    finish edges[i] = last := by
  induction edges generalizing first i with
  | nil => simp at hi
  | cons edge rest ih =>
      cases i with
      | zero =>
          have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hlast.symm)
          subst rest
          exact h.2
      | succ i =>
          exact ih h.2 i (by simp only [List.length_cons] at hi; omega)
            (by simp only [List.length_cons] at hlast; omega)

end Trail

section Circuit

variable {ι : Type} [DecidableEq ι]

theorem Circuit.formPerm (start finish : ι → Value) (edges : List ι)
    (hc : Circuit start finish edges) (hn : edges.Nodup) (edge : ι) (he : edge ∈ edges) :
    finish edge = start (edges.formPerm edge) := by
  obtain ⟨root, ht⟩ := hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  rw [List.formPerm_apply_getElem edges hn i hi]
  by_cases hnext : i + 1 < edges.length
  · simpa only [Nat.mod_eq_of_lt hnext] using ht.adjacent i hnext
  · have hlast : i + 1 = edges.length := by omega
    simp only [hlast, Nat.mod_self]
    exact (ht.last_value i hi hlast).trans (ht.head (by omega)).symm

theorem formPerm_product_fixed (cycles : List (List ι)) (edge : ι)
    (he : edge ∉ cycles.flatten) :
    ((cycles.map List.formPerm).prod : Equiv.Perm ι) edge = edge := by
  induction cycles with
  | nil => rfl
  | cons cycle rest ih =>
      have hnot : edge ∉ cycle ∧ edge ∉ rest.flatten := by
        simpa only [List.flatten_cons, List.mem_append, not_or] using he
      simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hnot.2,
        List.formPerm_apply_of_notMem hnot.1]

-- Disjoint occurrence circuits can be composed without changing one
-- another's values. This lemma permits the graph and Permute proofs to stay
-- separate from the executable assignment definition.
theorem formPerm_product_values (start finish : ι → Value) (cycles : List (List ι))
    (hc : ∀ cycle ∈ cycles, Circuit start finish cycle) (hn : cycles.flatten.Nodup)
    (edge : ι) (he : edge ∈ cycles.flatten) :
    finish edge = start (((cycles.map List.formPerm).prod : Equiv.Perm ι) edge) := by
  induction cycles with
  | nil => simp at he
  | cons cycle rest ih =>
      obtain ⟨hnc, hnr, hdisjoint⟩ := List.nodup_append.mp hn
      have hc' : ∀ c ∈ rest, Circuit start finish c := fun c hm => hc c (List.mem_cons_of_mem _ hm)
      simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      rcases List.mem_append.mp he with he | he
      · have hnot : edge ∉ rest.flatten := fun hm => hdisjoint edge he edge hm rfl
        rw [formPerm_product_fixed rest edge hnot]
        exact Circuit.formPerm start finish cycle (hc cycle List.mem_cons_self) hnc edge he
      · have hnot : ((rest.map List.formPerm).prod : Equiv.Perm ι) edge ∉ cycle := by
          intro hm
          have hfixed := formPerm_product_fixed rest (((rest.map List.formPerm).prod : Equiv.Perm ι) edge)
            (fun hn => hdisjoint _ hm _ hn rfl)
          have heq := ((rest.map List.formPerm).prod : Equiv.Perm ι).injective hfixed
          exact hdisjoint _ hm _ he heq
        rw [List.formPerm_apply_of_notMem hnot]
        exact ih hc' hnr he

end Circuit

end Shuffler.Optimality.ValueGraph
