import Experiments.BuildBottomUp.CheckedProofs
import Shuffler.BuildBottomUp.Defs

namespace BuildBottomUpExperiments.Checked

@[simp] theorem isFinal_legacy_eq (state : State source target spills) (offset : ℕ) :
    State.isFinal state offset = _root_.State.is_final state offset := rfl

@[simp] theorem isAvailable_legacy_eq (state : State source target spills) (dest : Fin target.length) :
    State.isAvailable state dest = _root_.State.is_available state dest := rfl

@[simp] theorem shallowestCopyPosition_legacy_eq (stack : Stack) (slot : Value) :
    Stack.shallowestCopyPosition stack slot = _root_.Stack.shallowest_copy_position stack slot := rfl

@[simp] theorem depth_legacy_eq (stack : Stack) (pos : Fin stack.length) :
    Stack.depth stack pos = _root_.Stack.depth_of stack pos := rfl

@[simp] theorem isDupReachable_legacy_eq (stack : Stack) (pos : Fin stack.length) :
    Stack.isDupReachable stack pos = _root_.Stack.is_dup_reachable stack pos := rfl

@[simp] theorem isSwapReachable_legacy_eq (stack : Stack) (pos : Fin stack.length) :
    Stack.isSwapReachable stack pos = _root_.Stack.is_swap_reachable stack pos := rfl

-- Equality here includes the complete state, mapping, and trace.
theorem push_eq (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot)
    (hbound : state.mapping.symm dest = none) :
    push state slot dest = .ok (state.push slot dest hgen hbound) := by
  cases slot <;> simp [push, requires, State.push, hbound, hgen,
    pure, Except.pure, bind, Except.bind]

theorem dup_eq (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) (hdup : state.stack.is_dup_reachable copy)
    (hbound : state.mapping.symm dest = none) :
    dup state copy dest = .ok (state.dup copy dest hdup hbound) := by
  simp [dup, requires, State.dup, hbound, hdup, pure, Except.pure, bind, Except.bind]

theorem swapWith_eq (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.is_swap_reachable pos)
    (hnfinal : ¬ state.is_final pos.val) :
    swapWith state pos.val = .ok (state.swapWith pos hbelow hreach hnfinal) := by
  simp [swapWith, requires, State.swapWith, index, pos.isLt, bind, Except.bind,
    pure, Except.pure, hbelow, hreach, hnfinal]
  split
  rfl

theorem produce_eq (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.is_available dest) :
    produce state dest = liftResult (state.produce dest hbound havailable) := by
  by_cases hjunk : target[dest.val].is_junk
  · have hgen : target[dest.val].can_be_freely_generated ∨ spills.is_spilled target[dest.val] :=
      Or.inl (target[dest.val].can_be_freely_generated_of_is_junk hjunk)
    simp +instances [produce, State.produce, hbound, hjunk, push_eq state _ dest hgen hbound,
      ensure, requires, positionOf, dest.isLt, State.push,
      liftResult, Except.mapError, pure, Except.pure, bind, Except.bind]
  · cases hcopy : state.stack.shallowest_copy_position target[dest.val] with
    | none =>
      have hgen : target[dest.val].can_be_freely_generated ∨ spills.is_spilled target[dest.val] := by
        simpa [State.is_available, hcopy] using havailable
      simp +instances [produce, State.produce, hbound, hjunk, hcopy, hgen,
        push_eq state _ dest hgen hbound,
        ensure, requires, positionOf, dest.isLt, State.push,
        liftResult, Except.mapError, pure, Except.pure, bind, Except.bind]
    | some copy =>
      by_cases hdup : state.stack.is_dup_reachable copy
      · simp +instances [produce, State.produce, hbound, hjunk, hcopy, Option.filter_some, hdup,
          dup_eq state copy dest hdup hbound,
          ensure, requires, positionOf, dest.isLt, State.dup,
          liftResult, Except.mapError, pure, Except.pure, bind, Except.bind]
      · by_cases hgen : target[dest.val].can_be_freely_generated ∨ spills.is_spilled target[dest.val]
        · simp +instances [produce, State.produce, hbound, hjunk, hcopy, hdup, hgen,
            push_eq state _ dest hgen hbound,
            ensure, requires, positionOf, dest.isLt, State.push,
            liftResult, Except.mapError, pure, Except.pure, bind, Except.bind]
        · simp [produce, State.produce, hbound, hjunk, hcopy, hdup, hgen,
            liftResult, Except.mapError,
            pure, Except.pure, bind, Except.bind, throw, throwThe]
          rfl

theorem generate_eq (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.is_available dest) :
    generate state dest.val = liftResult (state.generate dest hbound havailable) := by
  simp only [generate, index, dest.isLt, ↓reduceDIte, pure_bind]
  simp only [bind_pure]
  rw [produce_eq state dest hbound havailable]
  unfold State.generate
  cases hresult : state.produce dest hbound havailable with
  | error err => cases err; rfl
  | ok next =>
    simp only [liftResult, Except.mapError, bind, Except.bind]
    by_cases hswap : dest.val + 1 < next.stack.length ∧ ¬ next.is_final dest.val
    · let pos : Fin next.stack.length := ⟨dest.val, by omega⟩
      have htop : next.stack.length - 1 < next.stack.length := by omega
      have hlast : next.stack[next.stack.length - 1] =
          next.stack.getLast (by intro h; simp [h] at hswap) := (List.getLast_eq_getElem _).symm
      have hreach_eq : isSwapReachable next dest.val = next.stack.is_swap_reachable pos := rfl
      simp only [isFinal_legacy_eq, hswap]
      rw [slotAt_index next.stack pos, slotAt_index next.stack ⟨next.stack.length - 1, htop⟩]
      simp only [Fin.getElem_fin, pos, hlast, hreach_eq]
      by_cases hequal : next.stack[dest.val] = next.stack.getLast (by intro h; simp [h] at hswap)
      · simp [hequal, pos, swapDestinations, index, pos.isLt, htop,
          bind, Except.bind, pure, Except.pure]
      · by_cases hreach : next.stack.is_swap_reachable pos
        · simp [hequal, pos, hreach, swapWith_eq next pos hswap.1 hreach hswap.2,
            pure, Except.pure]
        · simp [hequal, pos, hreach, pure, Except.pure]
    · simp [hswap, pure, Except.pure]


end BuildBottomUpExperiments.Checked
