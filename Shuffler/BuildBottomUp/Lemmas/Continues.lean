import Shuffler.BuildBottomUp.Termination.Defs

namespace Shuffler.BuildBottomUp

namespace Lemmas

open Continues

theorem continues_iff_repeatStep {σ β ε : Type}
    (body : Unit → β → StateT σ (Except ε) (ForInStep β))
    (next current : β × σ) :
    Continues body next current ↔
      ((repeatStep body).val current.1).run current.2 = .ok (.inl next.1, next.2) := by
  cases h : body () current.1 current.2 with
  | error err => simp [Continues, repeatStep, StateT.run, bind, StateT.bind, Except.bind, h]
  | ok result =>
    rcases result with ⟨step, state⟩
    cases step <;> simp [Continues, repeatStep, StateT.run, bind, StateT.bind, Except.bind,
      pure, StateT.pure, Except.pure, h]

theorem repeatM_body_eq {σ β ε : Type}
    (body : Unit → β → StateT σ (Except ε) (ForInStep β))
    (recur : β → StateT σ (Except ε) β) (current : β × σ) :
    (repeatM.body (repeatStep body).val recur current.1).run current.2 =
      match (body () current.1).run current.2 with
      | .ok (.yield control, state) => (recur control).run state
      | .ok (.done control, state) => .ok (control, state)
      | .error err => .error err := by
  cases h : body () current.1 current.2 with
  | error err => simp [repeatM.body, repeatStep, StateT.run, bind, StateT.bind, Except.bind, h]
  | ok result =>
    rcases result with ⟨step, state⟩
    cases step <;> simp [repeatM.body, repeatStep, StateT.run, bind, StateT.bind, Except.bind,
      pure, StateT.pure, Except.pure, h]

end Lemmas

end Shuffler.BuildBottomUp
