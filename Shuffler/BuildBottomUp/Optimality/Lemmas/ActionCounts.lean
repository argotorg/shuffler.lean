import Shuffler.BuildBottomUp.Lemmas.Contracts
import Shuffler.BuildBottomUp.Theorems.Feasibility.Defs
import Shuffler.BuildBottomUp.Optimality.Lemmas.Extension

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxHeartbeats 2000000

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

@[simp] private theorem swapCount_transport (h : a = b) (trace : Trace spills source a) :
    (h ▸ trace : Trace spills source b).swapCount = trace.swapCount := by cases h; rfl

@[simp] private theorem additions_transport (h : a = b) (trace : Trace spills source a) :
    (h ▸ trace : Trace spills source b).additions = trace.additions := by cases h; rfl

@[simp] private theorem noPop_transport (h : a = b) (trace : Trace spills source a) :
    (h ▸ trace : Trace spills source b).noPop = trace.noPop := by cases h; rfl

-- A successful run returns the loop result unchanged.
theorem loop_eq_of_ok {initial : State source target spills} {h : initial.Valid}
    (hrun : buildBottomUp initial h = .ok result) : buildBottomUp.loop 0 initial = .ok result := by
  unfold buildBottomUp at hrun
  cases hl : buildBottomUp.loop 0 initial with
  | error err =>
    rw [hl] at hrun
    cases hrun
  | ok value =>
    obtain ⟨res, trace⟩ := value
    rw [hl, except_ok_bind] at hrun
    dsimp only at hrun
    by_cases hs : res.length = target.length
    · rw [requires_of_true _ hs, except_ok_bind] at hrun
      exact hrun
    · simp only [requires, hs, ↓reduceDIte] at hrun
      cases hrun

structure GenerateCounts (before after : State source target spills) : Prop where
  pending : after.pending_generations = before.pending_generations - 1
  extension : Extends before.trace after.trace

private theorem generate_counts_triple (state : State source target spills) (offset : Nat) :
    ⦃True⦄ state.generate offset ⦃fun s => GenerateCounts state s; epost⟨fun _ => True⟩⦄ := by
  vcgen [State.generate, State.produce, State.push, State.dup, State.swapDestinations,
    State.swapWith, requires, index, slotAt, State.isSwapReachable, State.depthOf]
  all_goals constructor
  all_goals simp_all [Extends.refl, Extends.dup]
  all_goals
    have hb : offset < target.length := by assumption
    generalize hv : target[offset] = value at *
    cases value <;> simp_all [Value.can_be_freely_generated, SpillSet.is_spilled,
      Extends.refl, Extends.push, Extends.load]
  all_goals
    try solve
      | repeat' first | apply Extends.swap | apply Extends.dup | apply Extends.push |
          apply Extends.load | exact Extends.refl _
  all_goals
    try solve
      | have h : Value.FunctionReturnLabel.can_be_freely_generated ∨
            SpillSet.is_spilled spills Value.FunctionReturnLabel := by assumption
        simp [Value.can_be_freely_generated, SpillSet.is_spilled] at h

theorem generate_counts (state next : State source target spills) (offset : Nat)
    (h : state.generate offset = .ok next) : GenerateCounts state next := by
  have hp := (generate_counts_triple state offset).le_wp trivial
  rw [h] at hp
  exact hp

structure SwapCounts (before after : State source target spills) : Prop where
  swaps : after.trace.swapCount = before.trace.swapCount + 1
  pending : after.pending_generations = before.pending_generations
  extension : Extends before.trace after.trace

theorem swap_counts (state next : State source target spills) (offset : Nat)
    (h : state.swapWith offset = .ok next) : SwapCounts state next := by
  have hs : ⦃True⦄ state.swapWith offset ⦃fun s => SwapCounts state s; epost⟨fun _ => True⟩⦄ := by
    vcgen [State.swapWith, requires, index]
    all_goals constructor <;> simp [Trace.swapCount]
  have hp := hs.le_wp trivial
  rw [h] at hp
  exact hp

-- Keep the result equation next to the postcondition.
theorem _root_.Shuffler.BuildBottomUp.Spec.with_eq {x : Except Error α} {post : α → Prop} (h : Spec x post) :
    Spec x (fun a => post a ∧ x = .ok a) := by
  cases x with
  | ok value => exact ⟨h, rfl⟩
  | error err => cases err <;> exact h

-- Spec.ite_index, where the rest branch also gets the failed condition.
theorem ite_index_rest {A : Prop} [Decidable A] {B : Fin size → Prop} [DecidablePred B]
    {gen rest : Except Error α} {post : α → Prop} (hlt : A → offset < size)
    (hgen : (hA : A) → B ⟨offset, hlt hA⟩ → Spec gen post)
    (hrest : (¬ ∃ hA : A, B ⟨offset, hlt hA⟩) → Spec rest post) :
    Spec (if A then index size offset >>= (fun i => if B i then gen else rest) else rest) post := by
  by_cases hA : A
  · rw [ite_eq_left hA, index_eq ⟨offset, hlt hA⟩, except_ok_bind]
    by_cases hB : B ⟨offset, hlt hA⟩
    · rw [ite_eq_left hB]; exact hgen hA hB
    · rw [ite_eq_right hB]; exact hrest fun ⟨_, h⟩ => hB h
  · rw [ite_eq_right hA]; exact hrest fun ⟨h, _⟩ => hA h

end Shuffler.Optimality.BBU
