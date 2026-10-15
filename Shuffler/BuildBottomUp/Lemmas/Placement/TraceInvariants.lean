import Shuffler.BuildBottomUp.Lemmas.Placement.Basic
import Shuffler.BuildBottomUp.Lemmas.Reachability
import Batteries.Data.List.Perm

namespace Shuffler.Placement

theorem getElem_mem_drop_of_le (stack : Stack) (pos : Fin stack.length) (cursor : Nat)
    (h : cursor ≤ pos.val) : stack[pos] ∈ stack.drop cursor := by
  apply List.mem_drop_iff_getElem.mpr
  refine ⟨pos.val - cursor, by have := pos.isLt; omega, ?_⟩
  have he : cursor + (pos.val - cursor) = pos.val := by omega
  simp only [he]
  rfl

theorem take_swap_of_le (stack : Stack) (cursor a b : Nat)
    (ha : cursor ≤ a) (hb : cursor ≤ b) :
    (stack.swap a b).take cursor = stack.take cursor := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hic : i < cursor := by
      simp only [List.length_take, List.length_swap] at hi
      omega
    simp only [List.getElem_take]
    exact List.getElem_swap_of_ne (by omega) (by omega) _

end Shuffler.Placement

theorem Trace.noPop_balance (trace : Trace spills source result) (h : trace.noPop) :
    (result : Multiset Value) = (source : Multiset Value) + trace.additions := by
  induction trace with
  | Lit => simp [Trace.additions]
  | Pop _ _ => exact False.elim h
  | @Swap prev idx hlen hlo hhi trace ih =>
    rw [Multiset.coe_eq_coe.mpr (List.swap_perm _ _ _)]
    exact ih h
  | Dup _ _ _ _ _ ih | Push _ _ _ ih | Load _ _ _ ih =>
    simpa only [← Multiset.coe_add, Multiset.coe_singleton, Trace.additions, add_assoc] using
      congrArg (fun values : Multiset Value => values + {_}) (ih h)

theorem Trace.noPop_length (trace : Trace spills source result) (h : trace.noPop) :
    result.length = source.length + trace.additions.card := by
  have hc := congrArg Multiset.card (trace.noPop_balance h)
  simpa using hc

theorem Trace.noPop_length_le (trace : Trace spills source result) (h : trace.noPop) :
    source.length ≤ result.length := by
  have := trace.noPop_length h
  omega

theorem Trace.noPop_frozen (trace : Trace spills source result) (h : trace.noPop) :
    result.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source) := by
  induction trace with
  | Lit => rfl
  | Pop _ _ => exact False.elim h
  | @Swap prev idx hlen hlo hhi trace ih =>
    have hl := trace.noPop_length_le h
    rw [Shuffler.Placement.take_swap_of_le]
    · exact ih h
    · unfold Shuffler.Placement.frozen MAX_SWAP_DEPTH at *; omega
    · unfold Shuffler.Placement.frozen MAX_SWAP_DEPTH at *; omega
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
    rw [List.take_append_of_le_length]
    · exact ih h
    · have := trace.noPop_length_le h
      unfold Shuffler.Placement.frozen
      omega

namespace Shuffler.Placement

private def Origin (spills : SpillSet) (source current : Stack) : Prop :=
  ∀ pos : Fin current.length, frozen source ≤ pos.val →
    Free spills current[pos] ∨ current[pos] ∈ window source

private theorem Origin.append {source current : Stack}
    (h : Origin spills source current) (value : Value)
    (hv : Free spills value ∨ value ∈ window source) :
    Origin spills source (current ++ [value]) := by
  intro pos hp
  by_cases hi : pos.val < current.length
  · simpa [List.getElem_append_left hi] using h ⟨pos.val, hi⟩ hp
  · have he : pos.val = current.length := by have := pos.isLt; simp at this; omega
    simpa [he] using hv

private theorem Origin.swap {source current : Stack}
    (h : Origin spills source current) (a b : Fin current.length)
    (ha : frozen source ≤ a.val) (hb : frozen source ≤ b.val) :
    Origin spills source (current.swap a b) := by
  intro pos hp
  by_cases hea : pos.val = a.val
  · simpa [List.getElem_swap, hea, a.isLt, b.isLt] using h b hb
  by_cases heb : pos.val = b.val
  · simpa [List.getElem_swap, hea, heb, a.isLt, b.isLt] using h a ha
  have hi : pos.val < current.length := by have := pos.isLt; simpa using this
  simpa [List.getElem_swap, hea, heb] using h ⟨pos.val, hi⟩ hp

private theorem origin_of_noPop (trace : Trace spills source result) (h : trace.noPop) :
    Origin spills source result := by
  induction trace with
  | Lit =>
    intro pos hp
    exact Or.inr (getElem_mem_drop_of_le source pos (frozen source) hp)
  | Pop _ _ => exact False.elim h
  | @Swap prev idx hlen hlo hhi trace ih =>
    have hl := trace.noPop_length_le h
    let a : Fin prev.length := ⟨prev.length - 1, by omega⟩
    let b : Fin prev.length := ⟨prev.length - 1 - idx, by omega⟩
    exact (ih h).swap a b
      (by dsimp [a, frozen]; omega)
      (by dsimp [b, frozen]; unfold MAX_SWAP_DEPTH at *; omega)
  | @Dup prev idx hlen hlo hhi trace ih =>
    have hl := trace.noPop_length_le h
    have hi : prev.length - idx < prev.length := by omega
    apply (ih h).append
    apply ih h ⟨prev.length - idx, hi⟩
    change source.length - (MAX_SWAP_DEPTH + 1) ≤ prev.length - idx
    unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
    omega
  | Push value hfree trace ih =>
    exact (ih h).append value (Or.inl (Or.inl hfree))
  | Load id hspilled trace ih =>
    exact (ih h).append (.Var id) (Or.inl (Or.inr hspilled))

theorem addition_free_or_mem_window (trace : Trace spills source result) (h : trace.noPop)
    {value : Value} (hv : value ∈ trace.additions) :
    Free spills value ∨ value ∈ window source := by
  induction trace with
  | Lit => simp [Trace.additions] at hv
  | Pop _ _ => exact False.elim h
  | Swap _ _ _ _ _ ih => exact ih h hv
  | @Dup prev idx hlen hlo hhi trace ih =>
    rcases Multiset.mem_add.mp hv with hold | hnew
    · exact ih h hold
    have he : value = prev[prev.length - idx]'(by omega) := by simpa using hnew
    rw [he]
    apply origin_of_noPop trace h ⟨prev.length - idx, by omega⟩
    have := trace.noPop_length_le h
    change source.length - (MAX_SWAP_DEPTH + 1) ≤ prev.length - idx
    unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
    omega
  | Push value hfree trace ih =>
    rcases Multiset.mem_add.mp hv with hold | hnew
    · exact ih h hold
    have he := Multiset.mem_singleton.mp hnew
    subst he
    exact Or.inl (Or.inl hfree)
  | Load id hspilled trace ih =>
    rcases Multiset.mem_add.mp hv with hold | hnew
    · exact ih h hold
    have he := Multiset.mem_singleton.mp hnew
    subst he
    exact Or.inl (Or.inr hspilled)

end Shuffler.Placement
