import Shuffler.BuildBottomUp.Lemmas.Generate.Basic
import Shuffler.BuildBottomUp.Lemmas.Reachability

namespace Shuffler.Generate

theorem Available.step {source : Stack} {value : Value}
    (h : Available spills source value) :
    ∃ trace : Trace spills source (source ++ [value]), trace.onlyGenerates := by
  rcases h with hfree | hspill | ⟨pos, hvalue, hreach⟩
  · exact ⟨.Push value hfree (.Lit source), trivial⟩
  · cases value with
    | Var id => exact ⟨.Load id hspill (.Lit source), trivial⟩
    | Lit _ | Wildcard | FunctionReturnLabel => simp [SpillSet.is_spilled] at hspill
  · subst value
    let depth := source.offsetToDepth pos
    let trace := Trace.Dup (depth.val + 1) (Nat.succ_le_of_lt depth.isLt)
      (Nat.succ_pos _) (Nat.add_le_add_right hreach 1) (Trace.Lit (spills := spills) source)
    refine ⟨dup_stack_eq source pos ▸ trace, ?_⟩
    exact (Trace.onlyGenerates_cast _ _).mpr trivial

-- At most one distinct value has its last reachable copy at the DUP boundary.
private def Critical (source : Stack) (value : Value) : Prop :=
  ∃ pos, source.shallowestCopyPosition value = some pos ∧
    (source.offsetToDepth pos).val = MAX_DUP_DEPTH

private theorem Critical.unique {source : Stack} {left right : Value}
    (hl : Critical source left) (hr : Critical source right) : left = right := by
  obtain ⟨l, hl, hld⟩ := hl
  obtain ⟨r, hr, hrd⟩ := hr
  have he : l = r := by
    apply Fin.ext
    rw [Stack.offsetToDepth_val] at hld hrd
    have := l.isLt
    have := r.isLt
    omega
  have hlv := Shuffler.BuildBottomUp.shallowestCopyPosition_value source left l hl
  have hrv := Shuffler.BuildBottomUp.shallowestCopyPosition_value source right r hr
  rw [he] at hlv
  exact hlv.symm.trans hrv

private theorem Ready.after_append {source missing : Stack} (h : Ready spills source missing)
    (chosen : Value)
    (hsafe : ∀ value ∈ missing, ¬value.can_be_freely_generated → ¬spills.is_spilled value →
      Critical source value → value = chosen) :
    Ready spills (source ++ [chosen]) (missing.erase chosen) := by
  intro value hv
  have hm := List.mem_of_mem_erase hv
  rcases h value hm with hfree | hspill | hcopy
  · exact Or.inl hfree
  · exact Or.inr (Or.inl hspill)
  by_cases hfree : value.can_be_freely_generated
  · exact Or.inl hfree
  by_cases hspill : spills.is_spilled value
  · exact Or.inr (Or.inl hspill)
  apply Or.inr ∘ Or.inr
  by_cases he : value = chosen
  · subst value
    exact Shuffler.BuildBottomUp.hasCopy_append_new source chosen
  have hc : Stack.hasCopy source value := hcopy
  obtain ⟨pos, hp, hr⟩ := hc.shallowest
  have hd : (source.offsetToDepth pos).val ≠ MAX_DUP_DEPTH := by
    intro hd
    exact he (hsafe value hm hfree hspill ⟨pos, hp, hd⟩)
  apply Shuffler.BuildBottomUp.hasCopy_append_old source value chosen pos
    (Shuffler.BuildBottomUp.shallowestCopyPosition_value source value pos hp)
  rw [Stack.offsetToDepth_val] at hd
  rw [Stack.isDupReachable_iff_length] at hr
  have := pos.isLt
  omega

private theorem Ready.choose {source missing : Stack} (h : Ready spills source missing)
    (hne : missing ≠ []) :
    ∃ value ∈ missing, Ready spills (source ++ [value]) (missing.erase value) := by
  classical
  by_cases hc : ∃ value ∈ missing, ¬value.can_be_freely_generated ∧
      ¬spills.is_spilled value ∧ Critical source value
  · obtain ⟨value, hv, _, _, hcritical⟩ := hc
    refine ⟨value, hv, h.after_append value ?_⟩
    intro other _ _ _ ho
    exact ho.unique hcritical
  · obtain ⟨value, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨value, by simp, h.after_append value ?_⟩
    intro other ho hf hs hc'
    exact False.elim (hc ⟨other, ho, hf, hs, hc'⟩)

theorem Ready.canGenerate {source missing : Stack} (h : Ready spills source missing) :
    CanGenerate spills source missing := by
  classical
  by_cases he : missing = []
  · subst missing
    refine ⟨[], .refl [], (List.append_nil source).symm ▸ Trace.Lit source, ?_⟩
    exact (Trace.onlyGenerates_cast _ _).mpr trivial
  · obtain ⟨value, hv, hnext⟩ := h.choose he
    obtain ⟨added, hperm, tail, htail⟩ := hnext.canGenerate
    obtain ⟨first, hfirst⟩ := (h value hv).step
    have hjoined := first.onlyGenerates_concat tail hfirst htail
    have heq : (source ++ [value]) ++ added = source ++ (value :: added) := by simp
    refine ⟨value :: added, ?_, heq ▸ first.concat tail, ?_⟩
    · exact (hperm.cons value).trans (List.perm_cons_erase hv).symm
    · exact (Trace.onlyGenerates_cast _ _).mpr hjoined
termination_by missing.length
decreasing_by
  have := List.length_erase_of_mem hv
  have := List.length_pos_of_mem hv
  omega

end Shuffler.Generate
