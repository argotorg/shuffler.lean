import Shuffler.Optimality.GroupEntry.Budget

namespace Shuffler.Optimality.GroupEntry

-- Split before the first birth. The birth changes no lower-slot selection
-- count, so each fixed position set has the stated additive count.
theorem firstBirth (trace : Trace spills source target) (hpop : trace.noPop)
    (hadded : trace.additions ≠ 0) :
    ∃ (middle : Stack) (value : Value) (before : Trace spills source middle)
      (tail : Trace spills (middle ++ [value]) target),
      before.noPop ∧ before.additions = 0 ∧ tail.noPop ∧
      ∀ positions, selections positions trace = selections positions before + selections positions tail := by
  induction trace with
  | Lit => exact False.elim (hadded rfl)
  | Pop _ _ => exact False.elim hpop
  | @Swap previous depth hd hlo hhi trace ih =>
      obtain ⟨middle, value, before, tail, hb, hz, ht, hc⟩ := ih hpop hadded
      refine ⟨middle, value, before, .Swap depth hd hlo hhi tail, hb, hz, ht, ?_⟩
      intro positions
      simp only [selections, hc positions, Nat.add_assoc]
  | @Dup previous depth hd hlo hhi trace ih =>
      by_cases hz : trace.additions = 0
      · refine ⟨previous, previous[previous.length - depth]'(by omega), trace, .Lit _,
          hpop, hz, by trivial, ?_⟩
        intro positions
        simp [selections]
      · obtain ⟨middle, value, before, tail, hb, hzero, ht, hc⟩ := ih hpop hz
        exact ⟨middle, value, before, .Dup depth hd hlo hhi tail, hb, hzero, ht, hc⟩
  | Push value hfree trace ih =>
      by_cases hz : trace.additions = 0
      · refine ⟨_, value, trace, .Lit _, hpop, hz, by trivial, ?_⟩
        intro positions
        simp [selections]
      · obtain ⟨middle, first, before, tail, hb, hzero, ht, hc⟩ := ih hpop hz
        exact ⟨middle, first, before, .Push value hfree tail, hb, hzero, ht, hc⟩
  | Load id hspill trace ih =>
      by_cases hz : trace.additions = 0
      · refine ⟨_, .Var id, trace, .Lit _, hpop, hz, by trivial, ?_⟩
        intro positions
        simp [selections]
      · obtain ⟨middle, first, before, tail, hb, hzero, ht, hc⟩ := ih hpop hz
        exact ⟨middle, first, before, .Load id hspill tail, hb, hzero, ht, hc⟩

theorem zero_selections_value (trace : Trace spills source target) (hpop : trace.noPop)
    (i : Nat) (hi : i + 1 < source.length) (hz : selections {i} trace = 0) :
    source[i]? = target[i]? := by
  have hd := differences_le_selections {i} trace (by intro j hj; have he : j = i := Finset.mem_singleton.mp hj; subst j; exact hi) hpop
  rw [hz] at hd
  have he : differences {i} target source = ∅ := Finset.card_eq_zero.mp (by omega)
  by_contra hn
  have hm : i ∈ differences {i} target source :=
    Finset.mem_filter.mpr ⟨Finset.mem_singleton_self i, Ne.symm hn⟩
  rw [he] at hm
  exact Finset.notMem_empty i hm

end Shuffler.Optimality.GroupEntry
