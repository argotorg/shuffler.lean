import Shuffler.Generate.Defs
import Shuffler.BuildBottomUp.Lemmas.Reachability

namespace Shuffler.Generate

private def Origin (spills : SpillSet) (source current : Stack) : Prop :=
  source.length ≤ current.length ∧
    ∀ pos : Fin current.length, source.length ≤ pos.val + (MAX_DUP_DEPTH + 1) →
      Available spills source current[pos]

private theorem Origin.append {source current : Stack}
    (h : Origin spills source current) (value : Value) (hv : Available spills source value) :
    Origin spills source (current ++ [value]) := by
  refine ⟨by have := h.1; simp only [List.length_append, List.length_singleton]; omega, ?_⟩
  intro pos hp
  by_cases hi : pos.val < current.length
  · simpa [List.getElem_append_left hi] using h.2 ⟨pos.val, hi⟩ hp
  · have he : pos.val = current.length := by have := pos.isLt; simp at this; omega
    simpa [he] using hv

private theorem origin_of_onlyGenerates (trace : Trace spills source result)
    (h : trace.onlyGenerates) : Origin spills source result := by
  induction trace with
  | Lit =>
    refine ⟨le_rfl, ?_⟩
    intro pos hp
    exact Or.inr (Or.inr ⟨pos, rfl, (Stack.isDupReachable_iff_length _ _).mpr hp⟩)
  | Swap _ _ _ _ _ => exact False.elim h
  | Pop _ _ => exact False.elim h
  | @Dup prev idx hlen hlo hhi trace ih =>
    have hold := ih h
    have hi : prev.length - idx < prev.length := by omega
    apply hold.append
    apply hold.2 ⟨prev.length - idx, hi⟩
    change source.length ≤ prev.length - idx + (MAX_DUP_DEPTH + 1)
    have := hold.1
    omega
  | Push value hfree trace ih =>
    exact (ih h).append value (Or.inl hfree)
  | Load id hspilled trace ih =>
    exact (ih h).append (.Var id) (Or.inr (Or.inl hspilled))

theorem CanGenerate.ready {source missing : Stack}
    (h : CanGenerate spills source missing) : Ready spills source missing := by
  obtain ⟨added, hperm, trace, htrace⟩ := h
  intro value hv
  have hm := hperm.mem_iff.mpr hv
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  have ho := origin_of_onlyGenerates trace htrace
  have hb : source.length + i < (source ++ added).length := by simp; omega
  have ha := ho.2 ⟨source.length + i, hb⟩
    (by change source.length ≤ source.length + i + (MAX_DUP_DEPTH + 1); omega)
  simpa [he] using ha

end Shuffler.Generate
