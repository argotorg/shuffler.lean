import Shuffler.Optimality.ValueGraph.Defs

namespace Shuffler.Optimality.ValueGraph

section Euler

variable {ι : Type} [DecidableEq ι]

theorem walk_preserves (start finish : ι → Value) (good : ι → Prop)
    (fuel : Nat) (pending : List (Value × Option ι)) (remaining circuit : List ι)
    (hp : ∀ entry ∈ pending, ∀ edge ∈ entry.2.toList, good edge)
    (hr : ∀ edge ∈ remaining, good edge)
    (hc : ∀ edge ∈ circuit, good edge) :
    (∀ edge ∈ (walk start finish fuel pending remaining circuit).1, good edge) ∧
    (∀ edge ∈ (walk start finish fuel pending remaining circuit).2, good edge) := by
  induction fuel generalizing pending remaining circuit with
  | zero => exact ⟨hc, hr⟩
  | succ fuel ih =>
      cases pending with
      | nil => exact ⟨hc, hr⟩
      | cons entry pending =>
          rcases entry with ⟨vertex, incoming⟩
          simp only [walk]
          split
          · rename_i edge he
            apply ih
            · intro entry hentry next hnext
              rcases List.mem_cons.mp hentry with rfl | hentry
              · have : next = edge := by simpa using hnext
                subst next
                exact hr edge (List.mem_of_find?_eq_some he)
              · exact hp entry hentry next hnext
            · intro next hnext
              exact hr next (List.mem_of_mem_erase hnext)
            · exact hc
          · apply ih
            · intro entry hentry next hnext
              exact hp entry (List.mem_cons_of_mem _ hentry) next hnext
            · exact hr
            · intro edge hedge
              rcases List.mem_append.mp hedge with hedge | hedge
              · exact hp (vertex, incoming) (List.mem_cons_self) edge hedge
              · exact hc edge hedge

theorem tour_preserves (start finish : ι → Value) (good : ι → Prop)
    (first : ι) (edges : List ι) (he : ∀ edge ∈ edges, good edge) :
    (∀ edge ∈ (tour start finish first edges).1, good edge) ∧
    (∀ edge ∈ (tour start finish first edges).2, good edge) := by
  exact walk_preserves start finish good _ _ _ _ (by simp) he (by simp)

theorem decompose_preserves (start finish : ι → Value) (good : ι → Prop)
    (fuel : Nat) (edges : List ι) (he : ∀ edge ∈ edges, good edge) :
    ∀ circuit ∈ decompose start finish fuel edges, ∀ edge ∈ circuit, good edge := by
  induction fuel generalizing edges with
  | zero => simp [decompose]
  | succ fuel ih =>
      cases edges with
      | nil => simp [decompose]
      | cons first rest =>
          have ht := tour_preserves start finish good first (first :: rest) he
          intro circuit hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ht.1
          · exact ih _ ht.2 _ hc

end Euler

theorem edges_reachable (source target : Stack) (hlen : source.length = target.length) :
    ∀ i ∈ edges source target hlen, i.rev.val ≤ MAX_SWAP_DEPTH := by
  have hm : ∀ i ∈ mismatches source target hlen, i.rev.val ≤ MAX_SWAP_DEPTH := by
    intro i hi
    exact (of_decide_eq_true (List.mem_filter.mp hi).2).1
  unfold edges
  split
  · rename_i hn
    dsimp only
    split
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hm i hi
      · simp only [List.mem_singleton] at hi
        subst i
        dsimp [Fin.rev]
        omega
    · exact hm
  · exact hm

-- No position deeper than SWAP16 can enter any generated occurrence cycle.
-- This statement holds even when counts or the frozen prefix do not match.
theorem assignment_reachable (source target : Stack) (hlen : source.length = target.length) :
    Shuffler.Permute.all_swaps_reachable (assignment source target hlen) := by
  intro i hi
  change i ∈ (((circuits source target hlen).map List.formPerm).prod)⁻¹.support at hi
  rw [Equiv.Perm.support_inv] at hi
  obtain ⟨perm, hp, hi⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hi
  obtain ⟨circuit, hc, rfl⟩ := List.mem_map.mp hp
  have he : i ∈ circuit := by
    exact List.mem_of_formPerm_apply_ne (Equiv.Perm.mem_support.mp hi)
  exact decompose_preserves _ _ (fun i : Fin source.length => i.rev.val ≤ MAX_SWAP_DEPTH)
    _ _ (edges_reachable source target hlen) circuit hc i he

end Shuffler.Optimality.ValueGraph
