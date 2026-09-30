import Shuffler.BuildBottomUp.Defs

namespace Shuffler.BuildBottomUp

theorem except_ok_bind (value : α) (next : α → Except ε β) :
    (Except.ok value >>= next) = next value := rfl

theorem except_error_bind (err : ε) (next : α → Except ε β) :
    (Except.error err >>= next) = .error err := rfl

theorem Action.exec_get (next : State source target spills → Action source target spills Unit)
    (state : State source target spills) : (get >>= next).exec state = (next state).exec state := rfl

theorem Action.exec_lift (action : M α) (next : α → Action source target spills Unit)
    (state : State source target spills) :
    (liftM action >>= next).exec state = (action >>= fun value => (next value).exec state) := by
  cases action <;> rfl

theorem Action.exec_set (state next : State source target spills) :
    (set next : Action source target spills Unit).exec state = .ok next := rfl

theorem Action.exec_throw (state : State source target spills) (err : Error) :
    (throw err : Action source target spills Unit).exec state = .error err := rfl

theorem Action.run_bind_update (action : Action source target spills Unit)
    (next : Unit → Action source target spills α) (state : State source target spills) :
    (action >>= next).run state = (action.exec state >>= fun state => (next ()).run state) := by
  simp only [Action.exec, StateT.run_bind]
  cases action.run state with
  | error e => rfl
  | ok result => obtain ⟨⟨⟩, next⟩ := result; rfl

theorem Action.run_get (next : State source target spills → Action source target spills α)
    (state : State source target spills) : (get >>= next).run state = (next state).run state := rfl

theorem Action.run_lift (action : M α) (next : α → Action source target spills β)
    (state : State source target spills) :
    (liftM action >>= next).run state = (action >>= fun value => (next value).run state) := by
  cases action <;> rfl

theorem Action.exec_lift_unit (action : M Unit) (state : State source target spills) :
    (liftM action : Action source target spills Unit).exec state =
      (action >>= fun _ => pure state) := by cases action <;> rfl

theorem Action.run_throw (state : State source target spills) (err : Error) :
    (throw err : Action source target spills α).run state = .error err := rfl

theorem Action.run_ite (condition : Prop) [Decidable condition]
    (yes no : Action source target spills α) (state : State source target spills) :
    (if condition then yes else no).run state =
      if condition then yes.run state else no.run state := by split <;> rfl

theorem Action.run_dite (condition : Prop) [Decidable condition]
    (yes : condition → Action source target spills α)
    (no : ¬condition → Action source target spills α) (state : State source target spills) :
    (if h : condition then yes h else no h).run state =
      if h : condition then (yes h).run state else (no h).run state := by split <;> rfl

-- Expose state passing while keeping helper actions opaque for their contracts.
macro "simp_action" : tactic => `(tactic| simp only [Action.run_ite, Action.run_dite,
  Action.run_get, Action.run_lift, Action.run_bind_update, Action.exec_lift_unit,
  StateT.run_pure, Action.run_throw, Action.exec_throw,
  bind_assoc, pure_bind, except_ok_bind, except_error_bind])

end Shuffler.BuildBottomUp
