import Shuffler.BuildBottomUp.Lemmas.Placement.Basic
import Shuffler.BuildBottomUp.Lemmas.Generate.Basic
import Shuffler.BuildBottomUp.Lemmas.Reachability
import Mathlib.Data.Multiset.OrderedMonoid

namespace Shuffler.Placement

@[simp] theorem mem_seeds (spills : SpillSet) (missing : Multiset Value) (value : Value) :
    value ∈ seeds spills missing ↔ value ∈ missing ∧ ¬Free spills value := by
  simp [seeds]

theorem seeds_nodup (spills : SpillSet) (missing : Multiset Value) :
    (seeds spills missing).Nodup := (missing.toFinset.filter _).nodup

theorem seeds_le_iff (spills : SpillSet) (missing resources : Multiset Value) :
    seeds spills missing ≤ resources ↔
      ∀ value ∈ missing, ¬Free spills value → value ∈ resources := by
  rw [Multiset.le_iff_subset (seeds_nodup spills missing)]
  simp only [Multiset.subset_iff, mem_seeds]
  aesop

theorem seeds_mono {first second : Multiset Value} (h : first ≤ second) :
    seeds spills first ≤ seeds spills second := by
  apply (seeds_le_iff _ _ _).mpr
  intro value hv hf
  exact (mem_seeds _ _ _).mpr ⟨Multiset.mem_of_le h hv, hf⟩

theorem seeds_erase_source {missing : Multiset Value} {working : Stack} {value : Value}
    (h : seeds spills missing ≤ (working : Multiset Value)) (hv : value ∉ missing) :
    seeds spills missing ≤ (working.erase value : Multiset Value) := by
  apply (seeds_le_iff _ _ _).mpr
  intro other ho hf
  have he : other ≠ value := by intro he; subst other; exact hv ho
  have hm := (seeds_le_iff _ _ _).mp h other ho hf
  exact (List.mem_erase_of_ne he).mpr hm

theorem available_of_suffix {fixed working : Stack} {missing : Multiset Value}
    (hseeds : seeds spills missing ≤ (working : Multiset Value))
    (hsmall : working.length ≤ MAX_DUP_DEPTH + 1)
    (value : Value) (hv : value ∈ missing) :
    Shuffler.Generate.Available spills (fixed ++ working) value := by
  by_cases hf : Free spills value
  · exact hf.imp_right Or.inl
  apply Or.inr ∘ Or.inr
  have hm : value ∈ working := (seeds_le_iff _ _ _).mp hseeds value hv hf
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  let pos : Fin (fixed ++ working).length := ⟨fixed.length + i, by simp; omega⟩
  refine ⟨pos, ?_, ?_⟩
  · simpa [pos] using he
  · rw [Stack.isDupReachable_iff_length]
    dsimp [pos]
    simp only [List.length_append]
    omega

theorem CanPlace.append {source : Stack} {value : Value}
    (h : Shuffler.Generate.Available spills source value) :
    CanPlace spills source (source ++ [value]) {value} := by
  rcases h with hf | hs | ⟨pos, hv, hr⟩
  · exact ⟨.Push value hf (.Lit source), trivial, by simp [Trace.additions]⟩
  · cases value with
    | Var id => exact ⟨.Load id hs (.Lit source), trivial, by simp [Trace.additions]⟩
    | Lit _ | Wildcard | FunctionReturnLabel => simp [SpillSet.is_spilled] at hs
  · subst value
    let depth := source.offsetToDepth pos
    let trace := Trace.Dup (depth.val + 1) (Nat.succ_le_of_lt depth.isLt)
      (Nat.succ_pos _) (Nat.add_le_add_right hr 1) (Trace.Lit (spills := spills) source)
    refine ⟨dup_stack_eq source pos ▸ trace, (Trace.noPop_cast _ _).mpr trivial, ?_⟩
    rw [Trace.additions_cast]
    have hi : source.length - (depth.val + 1) = pos.val := by
      dsimp [depth]
      rw [Stack.offsetToDepth_val]
      have := pos.isLt
      omega
    simp [trace, Trace.additions, hi]

theorem balance_erase_missing {working tail : Stack} {missing : Multiset Value} {value : Value}
    (h : ((value :: tail : Stack) : Multiset Value) = (working : Multiset Value) + missing)
    (hv : value ∈ missing) :
    (tail : Multiset Value) = (working : Multiset Value) + missing.erase value := by
  apply (Multiset.cons_inj_right value).mp
  rw [← Multiset.add_cons, Multiset.cons_erase hv]
  exact h

theorem balance_erase_source {working tail : Stack} {missing : Multiset Value} {value : Value}
    (h : ((value :: tail : Stack) : Multiset Value) = (working : Multiset Value) + missing)
    (hv : value ∉ missing) :
    value ∈ working ∧
      (tail : Multiset Value) = (working.erase value : Multiset Value) + missing := by
  have hm : value ∈ (working : Multiset Value) + missing := h ▸ (by simp)
  have hw : value ∈ working := (Multiset.mem_add.mp hm).resolve_right hv
  refine ⟨hw, ?_⟩
  apply (Multiset.cons_inj_right value).mp
  rw [← Multiset.coe_erase, ← Multiset.cons_add, Multiset.cons_erase hw]
  exact h

end Shuffler.Placement
