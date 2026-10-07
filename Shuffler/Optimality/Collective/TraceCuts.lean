import Shuffler.Optimality.Replay
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.Collective

open Shuffler.Placement

-- No POP means every intermediate height is reached by one birth. This
-- witness retains the production trace and its exact operation order.
theorem split_at_birth (trace : Trace spills source target) (hpop : trace.noPop)
    (height : Nat) (hsource : source.length < height) (htarget : height ≤ target.length) :
    ∃ (current : Stack) (value : Value) (before : Trace spills source current)
      (birth : Trace spills current (current ++ [value]))
      (tail : Trace spills (current ++ [value]) target),
      current.length + 1 = height ∧ before.noPop ∧ birth.noPop ∧ tail.noPop ∧
        birth.additions = {value} ∧ (flatten birth).length = 1 ∧
        trace = before.concat (birth.concat tail) := by
  induction trace with
  | Lit => omega
  | Pop _ _ => exact False.elim hpop
  | @Swap previous depth hlen hlo hhi trace ih =>
      obtain ⟨current, value, before, birth, tail, hc, hb, hg, ht, ha, ho, he⟩ :=
        ih hpop (by simpa only [List.length_swap] using htarget)
      refine ⟨current, value, before, birth, .Swap depth hlen hlo hhi tail,
        hc, hb, hg, ht, ha, ho, ?_⟩
      simp only [Trace.concat]
      rw [he]
  | @Dup previous depth hlen hlo hhi trace ih =>
      by_cases hh : height ≤ previous.length
      · obtain ⟨current, value, before, birth, tail, hc, hb, hg, ht, ha, ho, he⟩ := ih hpop hh
        refine ⟨current, value, before, birth, .Dup depth hlen hlo hhi tail,
          hc, hb, hg, ht, ha, ho, ?_⟩
        simp only [Trace.concat]
        rw [he]
      · refine ⟨previous, previous[previous.length-depth]'(by omega), trace,
          .Dup depth hlen hlo hhi (.Lit _), .Lit _, ?_, hpop, by trivial, by trivial,
          rfl, rfl, rfl⟩
        simp only [List.length_append, List.length_singleton] at htarget
        omega
  | @Push previous value hfree trace ih =>
      by_cases hh : height ≤ previous.length
      · obtain ⟨current, first, before, birth, tail, hc, hb, hg, ht, ha, ho, he⟩ := ih hpop hh
        refine ⟨current, first, before, birth, .Push value hfree tail,
          hc, hb, hg, ht, ha, ho, ?_⟩
        simp only [Trace.concat]
        rw [he]
      · refine ⟨previous, value, trace, .Push value hfree (.Lit _), .Lit _,
          ?_, hpop, by trivial, by trivial, rfl, rfl, rfl⟩
        simp only [List.length_append, List.length_singleton] at htarget
        omega
  | @Load previous id hspill trace ih =>
      by_cases hh : height ≤ previous.length
      · obtain ⟨current, first, before, birth, tail, hc, hb, hg, ht, ha, ho, he⟩ := ih hpop hh
        refine ⟨current, first, before, birth, .Load id hspill tail,
          hc, hb, hg, ht, ha, ho, ?_⟩
        simp only [Trace.concat]
        rw [he]
      · refine ⟨previous, .Var id, trace, .Load id hspill (.Lit _), .Lit _,
          ?_, hpop, by trivial, by trivial, rfl, rfl, rfl⟩
        simp only [List.length_append, List.length_singleton] at htarget
        omega

end Shuffler.Optimality.Collective
