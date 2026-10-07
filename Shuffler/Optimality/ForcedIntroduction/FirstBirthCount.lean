import Shuffler.Optimality.ForcedIntroduction.Theorems
import Shuffler.Optimality.Lineage.Theorems

namespace Shuffler.Optimality.ForcedIntroduction

open Shuffler.Placement Lineage

-- For a value absent from the initial source, the first birth contributes
-- one direct introduction exactly when it introduces that value.
theorem firstBirthCount (tracked : Value) (trace : Trace spills source target)
    (h : trace.noPop) (hne : trace.additions ≠ 0) (habsent : tracked ∉ source) :
    ∃ (middle : Stack) (value : Value) (before : Trace spills source middle)
      (tail : Trace spills (middle ++ [value]) target),
      before.noPop ∧ before.additions = 0 ∧ tail.noPop ∧
      trace.additions = {value} + tail.additions ∧
      directCount tracked trace = directCount tracked tail + if value = tracked then 1 else 0 := by
  induction trace with
  | Lit => exact False.elim (hne rfl)
  | Pop _ _ => exact False.elim h
  | @Swap prev idx hlen hlo hhi trace ih =>
      obtain ⟨middle, value, before, tail, hp, hz, ht, he, hc⟩ := ih h hne
      exact ⟨middle, value, before, .Swap idx hlen hlo hhi tail, hp, hz, ht, he, hc⟩
  | @Dup prev idx hlen hlo hhi trace ih =>
      by_cases hz : trace.additions = 0
      · have hb : (prev : Multiset Value) = (source : Multiset Value) := by
          simpa [hz] using trace.noPop_balance h
        have hneValue : prev[prev.length - idx]'(by omega) ≠ tracked := by
          intro he
          have hm : tracked ∈ (prev : Multiset Value) := he ▸ List.getElem_mem (by omega)
          rw [hb] at hm
          exact habsent hm
        have hc : directCount tracked trace = 0 := by
          have hh := additions_count_eq tracked trace
          rw [hz, Multiset.count_zero] at hh
          omega
        refine ⟨prev, prev[prev.length - idx]'(by omega), trace,
          .Lit _, h, hz, by trivial, ?_, ?_⟩
        · simp [Trace.additions, hz]
        · simp [directCount, hc, hneValue]
      · obtain ⟨middle, value, before, tail, hp, hzero, ht, he, hc⟩ := ih h hz
        refine ⟨middle, value, before, .Dup idx hlen hlo hhi tail,
          hp, hzero, ht, ?_, hc⟩
        simp only [Trace.additions, he, add_assoc]
  | Push value hfree trace ih =>
      by_cases hz : trace.additions = 0
      · have hc : directCount tracked trace = 0 := by
          have hh := additions_count_eq tracked trace
          rw [hz, Multiset.count_zero] at hh
          omega
        exact ⟨_, value, trace, .Lit _, h, hz, trivial,
          by simp [Trace.additions, hz], by simp [directCount, hc]⟩
      · obtain ⟨middle, first, before, tail, hp, hzero, ht, he, hc⟩ := ih h hz
        refine ⟨middle, first, before, .Push value hfree tail, hp, hzero, ht, ?_, ?_⟩
        · simp only [Trace.additions, he, add_assoc]
        · simp only [directCount, hc]
          omega
  | Load id hspilled trace ih =>
      by_cases hz : trace.additions = 0
      · have hc : directCount tracked trace = 0 := by
          have hh := additions_count_eq tracked trace
          rw [hz, Multiset.count_zero] at hh
          omega
        exact ⟨_, .Var id, trace, .Lit _, h, hz, trivial,
          by simp [Trace.additions, hz], by simp [directCount, hc]⟩
      · obtain ⟨middle, first, before, tail, hp, hzero, ht, he, hc⟩ := ih h hz
        refine ⟨middle, first, before, .Load id hspilled tail, hp, hzero, ht, ?_, ?_⟩
        · simp only [Trace.additions, he, add_assoc]
        · simp only [directCount, hc]
          omega

end Shuffler.Optimality.ForcedIntroduction
