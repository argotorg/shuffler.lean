import Shuffler.Optimality.BirthPlacement.RawWord
import Shuffler.Optimality.BirthPlacement.TracePlan.Build

namespace Shuffler.Optimality.BirthPlacement.RawWord

theorem feasible_of_plan (plan : Plan spills target) :
    Feasible spills target (birthWord target plan.assignment) := by
  constructor
  · apply Multiset.ext.mpr
    intro value
    simp only [Multiset.coe_count]
    rw [← positions_card, ← positions_card, birthWord, positions_ofFn]
    exact Word.balanced_of_matching plan.assignment (fun _ => rfl) value
  constructor
  · intro height
    apply Multiset.le_iff_count.mpr
    intro value
    simp only [Multiset.coe_count]
    by_cases hz : height.val = 0
    · simp [hz]
    · have hh := Word.feasible_of_matching
        (births := fun index => target[plan.assignment index])
        (target := fun index => target[index]) plan.assignment (fun _ => rfl) plan.deadlines value
      change Hall.Condition 16
        (Word.positions (fun index => target[plan.assignment index]) value)
        (positions target value) at hh
      rw [← positions_ofFn] at hh
      change Hall.Condition 16 (positions (birthWord target plan.assignment) value)
        (positions target value) at hh
      have hb := hh (height.val - 1)
      rw [due_card, born_card] at hb
      have he : height.val - 1 + 1 = height.val := by omega
      simpa only [he] using hb
  · intro index
    have hi : index.val < target.length := by simpa only [birthWord, List.length_ofFn] using index.isLt
    have hv : (birthWord target plan.assignment)[index] = target[plan.assignment ⟨index.val, hi⟩] := by
      change (birthWord target plan.assignment)[index.val] = _
      simp only [birthWord, List.getElem_ofFn]
    rw [hv]
    have ha := plan.available ⟨index.val, hi⟩
    cases hm : plan.method ⟨index.val, hi⟩ with
    | direct =>
      left
      rw [hm] at ha
      exact ha
    | dup =>
      right
      rw [hm] at ha
      exact ha

theorem feasible_of_trace (trace : Trace spills [] target) (hpop : trace.noPop) :
    Feasible spills target (SwapRuns.births trace) := by
  rw [← tracePlan_birthWord trace hpop]
  exact feasible_of_plan (tracePlan trace hpop)

theorem feasible_iff_trace : Feasible spills target births ↔
    ∃ trace : Trace spills [] target, trace.noPop ∧ SwapRuns.births trace = births := by
  constructor
  · intro h
    refine ⟨(realize h.plan).built.trace, (realize h.plan).built.noPop, ?_⟩
    exact (realize_births h.plan).trans h.assignment_birthWord
  · rintro ⟨trace, hpop, rfl⟩
    exact feasible_of_trace trace hpop

theorem parse_isSome_iff : (parse spills target births).isSome ↔ Feasible spills target births := by
  unfold parse
  split_ifs <;> simp_all

theorem parse_isSome_iff_trace : (parse spills target births).isSome ↔
    ∃ trace : Trace spills [] target, trace.noPop ∧ SwapRuns.births trace = births :=
  parse_isSome_iff.trans feasible_iff_trace

end Shuffler.Optimality.BirthPlacement.RawWord
