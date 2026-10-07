import Shuffler.Optimality.Lineage
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.ForcedIntroduction

open Shuffler.Placement Lineage

private def Origin (value : Value) (source current : Stack) : Prop :=
  ∀ pos : Fin current.length, frozen source ≤ pos.val →
    current[pos] = value → value ∈ window source

private theorem Origin.append {source current : Stack}
    (h : Origin value source current) (added : Value)
    (hv : added = value → value ∈ window source) :
    Origin value source (current ++ [added]) := by
  intro pos hp he
  by_cases hi : pos.val < current.length
  · exact h ⟨pos.val, hi⟩ hp (by simpa [List.getElem_append_left hi] using he)
  · have heq : pos.val = current.length := by have := pos.isLt; simp at this; omega
    exact hv (by simpa [heq] using he)

private theorem Origin.swap {source current : Stack}
    (h : Origin value source current) (a b : Fin current.length)
    (ha : frozen source ≤ a.val) (hb : frozen source ≤ b.val) :
    Origin value source (current.swap a b) := by
  intro pos hp he
  by_cases hea : pos.val = a.val
  · exact h b hb (by simpa [List.getElem_swap, hea, a.isLt, b.isLt] using he)
  by_cases heb : pos.val = b.val
  · exact h a ha (by simpa [List.getElem_swap, hea, heb, a.isLt, b.isLt] using he)
  have hi : pos.val < current.length := by have := pos.isLt; simpa using this
  exact h ⟨pos.val, hi⟩ hp (by simpa [List.getElem_swap, hea, heb] using he)

private theorem origin_of_no_direct (value : Value) (trace : Trace spills source result)
    (h : trace.noPop) (hno : directCount value trace = 0) :
    Origin value source result := by
  induction trace with
  | Lit =>
      intro pos hp he
      rw [← he]
      exact getElem_mem_drop_of_le source pos (frozen source) hp
  | Pop _ _ => exact False.elim h
  | @Swap prev idx hlen hlo hhi trace ih =>
      have hl := trace.noPop_length_le h
      let a : Fin prev.length := ⟨prev.length - 1, by omega⟩
      let b : Fin prev.length := ⟨prev.length - 1 - idx, by omega⟩
      exact (ih h hno).swap a b
        (by dsimp [a, frozen]; omega)
        (by dsimp [b, frozen]; unfold MAX_SWAP_DEPTH at *; omega)
  | @Dup prev idx hlen hlo hhi trace ih =>
      have hl := trace.noPop_length_le h
      have hi : prev.length - idx < prev.length := by omega
      apply (ih h hno).append
      apply ih h hno ⟨prev.length - idx, hi⟩
      change source.length - (MAX_SWAP_DEPTH + 1) ≤ prev.length - idx
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
  | Push added hfree trace ih =>
      have hz : directCount value trace = 0 := by simp only [directCount] at hno; omega
      apply (ih h hz).append
      intro he
      simp [directCount, he] at hno
  | Load id hspill trace ih =>
      have hz : directCount value trace = 0 := by simp only [directCount] at hno; omega
      apply (ih h hz).append
      intro he
      simp [directCount, he] at hno

theorem addition_mem_window_of_no_direct (value : Value)
    (trace : Trace spills source result) (h : trace.noPop)
    (hno : directCount value trace = 0) (hv : value ∈ trace.additions) :
    value ∈ window source := by
  induction trace with
  | Lit => simp [Trace.additions] at hv
  | Pop _ _ => exact False.elim h
  | Swap _ _ _ _ _ ih => exact ih h hno hv
  | @Dup prev idx hlen hlo hhi trace ih =>
      rcases Multiset.mem_add.mp hv with hold | hnew
      · exact ih h hno hold
      have he : value = prev[prev.length - idx]'(by omega) := by simpa using hnew
      apply origin_of_no_direct value trace h hno ⟨prev.length - idx, by omega⟩
      · have := trace.noPop_length_le h
        change source.length - (MAX_SWAP_DEPTH + 1) ≤ prev.length - idx
        unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
        omega
      · exact he.symm
  | Push added hfree trace ih =>
      have hz : directCount value trace = 0 := by simp only [directCount] at hno; omega
      rcases Multiset.mem_add.mp hv with hold | hnew
      · exact ih h hz hold
      have he := Multiset.mem_singleton.mp hnew
      simp [directCount, he] at hno
  | Load id hspill trace ih =>
      have hz : directCount value trace = 0 := by simp only [directCount] at hno; omega
      rcases Multiset.mem_add.mp hv with hold | hnew
      · exact ih h hz hold
      have he := Multiset.mem_singleton.mp hnew
      simp [directCount, he] at hno

end Shuffler.Optimality.ForcedIntroduction
