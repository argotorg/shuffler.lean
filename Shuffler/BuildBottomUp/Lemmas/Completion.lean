module

public import Shuffler.BuildBottomUp.Defs
public import Shuffler.Emission.Lemmas

@[expose] public section
namespace Shuffler.Emission

theorem generate_completed (current : State source target spills) (targetOffset : ℕ) :
    (((current.generate targetOffset) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) = do

  let mut state := current
  state ← (((state.produce (← index target.length targetOffset)) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
    if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state)

  -- `produce` left the slot on top; swap it down only if its offset exists strictly below the top:
  -- as the top itself it is in place already, beyond the height it has to wait on top anyway
  if targetOffset + 1 < state.stack.length then if ¬ state.isFinal (← index state.stack.length targetOffset) then
    let top := state.stack.length - 1
    if (← slotAt state.stack targetOffset) = (← slotAt state.stack top) then
      -- an equal slot stands at the offset: retag instead of swapping two equal slots
      state ← state.swapDestinations targetOffset top
    else if state.isSwapReachable (← index state.stack.length targetOffset) then
      state ← state.swapWith targetOffset
    -- out of swap reach: leave the slot on top; buildBottomUp re-checks reach when filling the offset
  return state := by
  unfold State.generate
  simp only [bind_assoc, completed_ite, pure_bind, Option.isSome_none,
    Bool.false_eq_true, dite_false]
  congr 1
  funext dest
  congr 1
  funext result
  by_cases hb : result.blocked.isSome <;> simp [hb, bind, Except.bind] <;> rfl

theorem buildBottomUp_completed (initial : State source target spills) (h : initial.Valid) :
    ((((buildBottomUp initial h) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) = (do
      let ⟨stack, trace⟩ ← ((((buildBottomUp.loop 0 initial) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
        if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
        pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack))
      _ ← requires (stack.length = target.length) "stack and target sizes differ"
      return ⟨stack, trace⟩) := by
  unfold buildBottomUp
  cases hl : buildBottomUp.loop 0 initial with
  | error err => rfl
  | ok r => cases r with
    | mk blocked state =>
      cases blocked with
      | some b => rfl
      | none =>
        by_cases hsize : state.stack.length = target.length <;>
          simp [requires, hsize, bind, Except.bind, pure, Except.pure]
        rfl

end Shuffler.Emission
