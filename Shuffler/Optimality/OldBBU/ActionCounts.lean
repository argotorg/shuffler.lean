import Shuffler.BuildBottomUp.Lemmas.Contracts
import Shuffler.Feasibility.Spec
import Shuffler.Optimality.OldBBU.Extension

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxHeartbeats 2000000

namespace Shuffler.Optimality.OldBBU

open Shuffler.BuildBottomUp

@[simp] private theorem swapCount_transport (h : a = b) (trace : Trace spills source a) :
    (h ▸ trace : Trace spills source b).swapCount = trace.swapCount := by cases h; rfl

@[simp] private theorem additions_transport (h : a = b) (trace : Trace spills source a) :
    (h ▸ trace : Trace spills source b).additions = trace.additions := by cases h; rfl

@[simp] private theorem noPop_transport (h : a = b) (trace : Trace spills source a) :
    (h ▸ trace : Trace spills source b).noPop = trace.noPop := by cases h; rfl

structure GenerateCounts (before after : State source target spills) : Prop where
  swaps : after.trace.swapCount ≤ before.trace.swapCount + 1
  births : after.trace.additions.card = before.trace.additions.card + 1
  pending : after.pending_generations = before.pending_generations - 1
  noPop : before.trace.noPop → after.trace.noPop
  extension : Extends before.trace after.trace

private theorem generate_counts_triple (state : State source target spills) (offset : Nat) :
    ⦃fun s : State source target spills => s = state⦄ generate offset
      ⦃fun _ s => GenerateCounts state s; epost⟨fun _ => True⟩⦄ := by
  vcgen [generate, produce, push, dup, swapDestinations, swapWith,
    ensure, requires, index, slotAt, State.isSwapReachable, State.depthOf]
  all_goals subst_vars
  all_goals constructor
  all_goals simp_all [Trace.swapCount, Trace.additions, Trace.noPop,
    Extends.refl, Extends.swap, Extends.dup, Extends.push, Extends.load]
  all_goals
    try solve
      | apply Extends.swap; rw [Extends.transport]; apply Extends.dup; exact Extends.refl _
      | repeat' first | apply Extends.swap | apply Extends.dup | apply Extends.push |
          apply Extends.load | exact Extends.refl _
  all_goals
    have hb : offset < target.length := by assumption
    generalize hv : target[offset] = value at *
    cases value <;> simp_all [Trace.swapCount, Trace.additions, Trace.noPop,
      Value.can_be_freely_generated, SpillSet.is_spilled,
      Extends.refl, Extends.swap, Extends.dup, Extends.push, Extends.load]
  all_goals
    try solve
      | apply Extends.swap; rw [Extends.transport]; apply Extends.dup; exact Extends.refl _
      | repeat' first | apply Extends.swap | apply Extends.dup | apply Extends.push |
          apply Extends.load | exact Extends.refl _
  all_goals
    try solve
      | have h : Value.FunctionReturnLabel.can_be_freely_generated ∨
            SpillSet.is_spilled spills Value.FunctionReturnLabel := by assumption
        exact False.elim (by simpa [Value.can_be_freely_generated, SpillSet.is_spilled] using h)

private theorem run_eq_of_exec_eq (action : Action source target spills Unit)
    (state next : State source target spills) (h : action.exec state = .ok next) :
    action.run state = .ok ((), next) := by
  unfold Action.exec at h
  cases heq : action.run state with
  | error error => simp [heq] at h
  | ok result =>
      rcases result with ⟨⟨⟩,result⟩
      simp [heq] at h
      subst result
      rfl

theorem generate_counts (state next : State source target spills) (offset : Nat)
    (h : (generate offset).exec state = .ok next) : GenerateCounts state next := by
  have hp := (generate_counts_triple state offset).le_wp state rfl
  rw [StateT.wp_apply_eq, run_eq_of_exec_eq _ _ _ h] at hp
  exact hp

structure SwapCounts (before after : State source target spills) : Prop where
  swaps : after.trace.swapCount = before.trace.swapCount + 1
  births : after.trace.additions.card = before.trace.additions.card
  pending : after.pending_generations = before.pending_generations
  noPop : before.trace.noPop → after.trace.noPop
  extension : Extends before.trace after.trace

theorem swap_counts (state next : State source target spills) (offset : Nat)
    (h : (swapWith offset).exec state = .ok next) : SwapCounts state next := by
  have hs : ⦃fun s : State source target spills => s = state⦄ swapWith offset
      ⦃fun _ s => SwapCounts state s; epost⟨fun _ => True⟩⦄ := by
    vcgen [swapWith, requires, ensure, index]
    all_goals subst_vars
    all_goals constructor <;> simp [Trace.swapCount, Trace.additions, Trace.noPop,
      Extends.refl, Extends.swap, Extends.dup, Extends.push, Extends.load]
    all_goals exact Extends.swap _ _ _ _ (Extends.refl _)
  have hp := hs.le_wp state rfl
  rw [StateT.wp_apply_eq, run_eq_of_exec_eq _ _ _ h] at hp
  exact hp

theorem with_success_eq {result : Except Error α} {post : α → Prop}
    (h : Spec result post) : Spec result (fun value => post value ∧ result = .ok value) := by
  cases result with
  | ok value => exact ⟨h, rfl⟩
  | error error => cases error <;> exact h

end Shuffler.Optimality.OldBBU
