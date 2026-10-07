import Shuffler.Optimality.ForcedIntroduction.Origin

namespace Shuffler.Optimality.ForcedIntroduction

open Shuffler.Placement Lineage

-- Without a direct introduction of the tracked value, its first birth
-- must use an occurrence inside DUP reach before the stack grows.
theorem firstBirth (tracked : Value) (trace : Trace spills source target)
    (h : trace.noPop) (hne : trace.additions ≠ 0)
    (hno : directCount tracked trace = 0) :
    ∃ (middle : Stack) (value : Value) (before : Trace spills source middle)
      (tail : Trace spills (middle ++ [value]) target),
      before.noPop ∧ before.additions = 0 ∧
      (value = tracked → tracked ∈ middle.drop (middle.length - (MAX_DUP_DEPTH + 1))) ∧
      tail.noPop ∧ directCount tracked tail = 0 ∧
      trace.additions = {value} + tail.additions := by
  induction trace with
  | Lit => exact False.elim (hne rfl)
  | Pop _ _ => exact False.elim h
  | @Swap prev idx hlen hlo hhi trace ih =>
      obtain ⟨middle, value, before, tail, hp, hz, hv, ht, hn, he⟩ := ih h hne hno
      exact ⟨middle, value, before, .Swap idx hlen hlo hhi tail, hp, hz, hv, ht, hn, he⟩
  | @Dup prev idx hlen hlo hhi trace ih =>
      by_cases hz : trace.additions = 0
      · refine ⟨prev, prev[prev.length - idx]'(by omega), trace,
          .Lit _, h, hz, ?_, by trivial, rfl, ?_⟩
        · intro he
          rw [← he]
          exact getElem_mem_drop_of_le prev ⟨prev.length - idx, by omega⟩
            (prev.length - (MAX_DUP_DEPTH + 1)) (by dsimp; omega)
        · simp [Trace.additions, hz]
      · obtain ⟨middle, value, before, tail, hp, hzero, hv, ht, hn, he⟩ := ih h hz hno
        refine ⟨middle, value, before, .Dup idx hlen hlo hhi tail,
          hp, hzero, hv, ht, hn, ?_⟩
        simp only [Trace.additions, he, add_assoc]
  | Push value hfree trace ih =>
      have hn : directCount tracked trace = 0 := by simp only [directCount] at hno; omega
      have hneValue : value ≠ tracked := by intro he; simp [directCount, he] at hno
      by_cases hz : trace.additions = 0
      · exact ⟨_, value, trace, .Lit _, h, hz, fun he => False.elim (hneValue he),
          trivial, rfl, by simp [Trace.additions, hz]⟩
      · obtain ⟨middle, first, before, tail, hp, hzero, hv, ht, hnt, he⟩ := ih h hz hn
        refine ⟨middle, first, before, .Push value hfree tail,
          hp, hzero, hv, ht, ?_, ?_⟩
        · simp [directCount, hnt, hneValue]
        · simp only [Trace.additions, he, add_assoc]
  | Load id hspilled trace ih =>
      have hn : directCount tracked trace = 0 := by simp only [directCount] at hno; omega
      have hneValue : Value.Var id ≠ tracked := by intro he; simp [directCount, he] at hno
      by_cases hz : trace.additions = 0
      · exact ⟨_, .Var id, trace, .Lit _, h, hz, fun he => False.elim (hneValue he),
          trivial, rfl, by simp [Trace.additions, hz]⟩
      · obtain ⟨middle, first, before, tail, hp, hzero, hv, ht, hnt, he⟩ := ih h hz hn
        refine ⟨middle, first, before, .Load id hspilled tail,
          hp, hzero, hv, ht, ?_, ?_⟩
        · simp [directCount, hnt, hneValue]
        · simp only [Trace.additions, he, add_assoc]

end Shuffler.Optimality.ForcedIntroduction
