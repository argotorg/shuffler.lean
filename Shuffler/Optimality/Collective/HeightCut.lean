import Shuffler.Optimality.Collective.TraceCuts
import Shuffler.Optimality.Lineage.Theorems

namespace Shuffler.Optimality.Collective

open Shuffler.Placement

structure TracePrefix (spills : SpillSet) (source target : Stack) where
  current : Stack
  before : Trace spills source current
  after : Trace spills current target

def TracePrefix.whole (trace : Trace spills source target) : TracePrefix spills source target :=
  ⟨target, trace, .Lit _⟩

def TracePrefix.Joins (trace : Trace spills source target)
    (cut : TracePrefix spills source target) : Prop := cut.before.concat cut.after = trace

def TracePrefix.NoPop (cut : TracePrefix spills source target) : Prop :=
  cut.before.noPop ∧ cut.after.noPop

-- The longest operation prefix whose final height is at most the limit.
-- The no-POP assumption is used by the theorems, not by this data function.
def takeHeight (height : Nat) (trace : Trace spills source target) : TracePrefix spills source target := by
  cases trace with
  | Lit => exact .whole (.Lit source)
  | @Swap previous depth hlen hlo hhi earlier =>
      if previous.length ≤ height then exact .whole (.Swap depth hlen hlo hhi earlier)
      else
        let cut := takeHeight height earlier
        exact ⟨cut.current, cut.before, .Swap depth hlen hlo hhi cut.after⟩
  | @Dup previous depth hlen hlo hhi earlier =>
      if previous.length + 1 ≤ height then exact .whole (.Dup depth hlen hlo hhi earlier)
      else
        let cut := takeHeight height earlier
        exact ⟨cut.current, cut.before, .Dup depth hlen hlo hhi cut.after⟩
  | @Pop previous hlen earlier =>
      if previous.dropLast.length ≤ height then exact .whole (.Pop hlen earlier)
      else
        let cut := takeHeight height earlier
        exact ⟨cut.current, cut.before, .Pop hlen cut.after⟩
  | @Push previous value hfree earlier =>
      if previous.length + 1 ≤ height then exact .whole (.Push value hfree earlier)
      else
        let cut := takeHeight height earlier
        exact ⟨cut.current, cut.before, .Push value hfree cut.after⟩
  | @Load previous id hspill earlier =>
      if previous.length + 1 ≤ height then exact .whole (.Load id hspill earlier)
      else
        let cut := takeHeight height earlier
        exact ⟨cut.current, cut.before, .Load id hspill cut.after⟩
termination_by structural trace

theorem takeHeight_whole (trace : Trace spills source target)
    (hh : target.length ≤ height) : takeHeight height trace = .whole trace := by
  cases trace <;> simp_all only [takeHeight, List.length_swap, List.length_append, List.length_singleton, dite_true]

theorem takeHeight_joined (trace : Trace spills source target) :
    (takeHeight height trace).Joins trace := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih | Dup _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      simp only [takeHeight]
      split_ifs with hh <;> try simp only [hh, dite_true, dite_false]
      · rfl
      · simp only [TracePrefix.Joins, Trace.concat]
        congr 1

theorem takeHeight_noPop (trace : Trace spills source target) (hpop : trace.noPop) :
    (takeHeight height trace).NoPop := by
  induction trace with
  | Lit => simp [takeHeight, TracePrefix.whole, TracePrefix.NoPop, Trace.noPop]
  | Pop _ _ => exact False.elim hpop
  | Swap _ _ _ _ trace ih | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      simp only [takeHeight]
      split_ifs with hh <;> try simp only [hh, dite_true, dite_false]
      · exact ⟨hpop, by trivial⟩
      · exact ih hpop

theorem takeHeight_length (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ height) :
    (takeHeight height trace).current.length = min target.length height := by
  induction trace with
  | Lit => simp [takeHeight_whole _ hsource, TracePrefix.whole, Nat.min_eq_left hsource]
  | Pop _ _ => exact False.elim hpop
  | @Swap previous depth hlen hlo hhi trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      ·
        simpa only [TracePrefix.whole, List.length_swap, List.length_append, List.length_singleton] using
          (Nat.min_eq_left hh).symm
      · simpa only [List.length_swap] using ih hpop
  | @Dup previous depth hlen hlo hhi trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      ·
        simpa only [TracePrefix.whole, List.length_swap, List.length_append, List.length_singleton] using
          (Nat.min_eq_left hh).symm
      ·
        simp only [List.length_append, List.length_singleton] at hh ⊢
        have hi := ih hpop
        omega
  | @Push previous value hfree trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      ·
        simpa only [TracePrefix.whole, List.length_swap, List.length_append, List.length_singleton] using
          (Nat.min_eq_left hh).symm
      ·
        simp only [List.length_append, List.length_singleton] at hh ⊢
        have hi := ih hpop
        omega
  | @Load previous id hspill trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      ·
        simpa only [TracePrefix.whole, List.length_swap, List.length_append, List.length_singleton] using
          (Nat.min_eq_left hh).symm
      ·
        simp only [List.length_append, List.length_singleton] at hh ⊢
        have hi := ih hpop
        omega

def residual (cut : Nat) (trace : Trace spills source target) : Stack :=
  (takeHeight (cut + 16) trace).current.drop cut

def directBefore (value : Value) (cut : Nat) (trace : Trace spills source target) : Nat :=
  Lineage.directCount value (takeHeight (cut + 16) trace).before

theorem takeHeight_take (trace : Trace spills source target) (hpop : trace.noPop) :
    (takeHeight (cut + 16) trace).current.take cut = target.take cut := by
  induction trace with
  | Lit => simp [takeHeight, TracePrefix.whole]
  | Pop _ _ => exact False.elim hpop
  | @Swap previous depth hlen hlo hhi trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      · rfl
      ·
        rw [take_swap_of_le previous cut _ _ (by omega) (by unfold MAX_SWAP_DEPTH at hhi; omega)]
        exact ih hpop
  | @Dup previous depth hlen hlo hhi trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      · rfl
      ·
        rw [List.take_append_of_le_length (by omega)]
        exact ih hpop
  | @Push previous value hfree trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      · rfl
      ·
        rw [List.take_append_of_le_length (by omega)]
        exact ih hpop
  | @Load previous id hspill trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      · rfl
      ·
        rw [List.take_append_of_le_length (by omega)]
        exact ih hpop

end Shuffler.Optimality.Collective
