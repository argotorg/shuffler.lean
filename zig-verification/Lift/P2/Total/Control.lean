module

public import Lift.P2.Total.Memory

@[expose] public section

namespace Lift.P2.Total

/-- One local computation. Calls carry a continuation with the callee's result type. -/
inductive Command (F : Type) (argument result locals : F → Type) (f : F) where
  | next (state : locals f)
  | call (callee : F) (args : argument callee) (memory : DataMem)
      (resume : result callee → DataMem → locals f)
  | returned (value : result f) (memory : DataMem)
  | failed (reason : Failure) (memory : DataMem)
  | choose {A : Type} [NondetSupportingType A] (resume : A → locals f)

/-- The generated locals contain only the values live at each control point. -/
structure Program (F : Type) where
  argument : F → Type
  result : F → Type
  locals : F → Type
  enter : ∀ f, argument f → DataMem → locals f
  body : ∀ f, locals f → Command F argument result locals f

inductive Continuation {F : Type} (program : Program F) (root : F) : F → Type where
  | root : Continuation program root root
  | call {caller callee : F}
      (resume : program.result callee → DataMem → program.locals caller)
      (rest : Continuation program root caller) : Continuation program root callee

inductive Config {F : Type} (program : Program F) (root : F) where
  | running (f : F) (state : program.locals f) (continuation : Continuation program root f)
  | returned (value : program.result root) (memory : DataMem)
  | failed (reason : Failure) (memory : DataMem)

/-- Calls, returns, choices and local loops have steps, with no fuel parameter. -/
inductive Transition {F : Type} (program : Program F) {root : F} :
    Config program root → Config program root → Prop where
  | next {f state next k} (body : program.body f state = .next next) :
      Transition program (.running f state k) (.running f next k)
  | call {f state callee args memory resume k}
      (body : program.body f state = .call callee args memory resume) :
      Transition program (.running f state k)
        (.running callee (program.enter callee args memory) (.call resume k))
  | returned {state value memory}
      (body : program.body root state = .returned value memory) :
      Transition program (.running root state .root) (.returned value memory)
  | resume {caller callee state value memory resume k}
      (body : program.body callee state = .returned value memory) :
      Transition program (.running callee state (.call (caller := caller) resume k))
        (.running caller (resume value memory) k)
  | failed {f state reason memory k}
      (body : program.body f state = .failed reason memory) :
      Transition program (.running f state k) (.failed reason memory)
  | choose {f state A} {support : NondetSupportingType A} {resume : A → program.locals f} {k}
      (body : program.body f state = @Command.choose _ _ _ _ _ A support resume) (value : A) :
      Transition program (.running f state k) (.running f (resume value) k)

def Program.system {F : Type} (program : Program F) (root : F) :
    System (Config program root) (Outcome (program.result root) DataMem) where
  step := Transition program
  stop state outcome := match state with
    | .running _ _ _ => False
    | .returned value memory => outcome = .returned value memory
    | .failed reason memory => outcome = .failure reason memory

theorem Transition.total {F : Type} (program : Program F) {root : F}
    (f : F) (state : program.locals f) (k : Continuation program root f) :
    ∃ next, Transition program (.running f state k) next := by
  cases body : program.body f state with
  | next next => exact ⟨_, .next body⟩
  | call callee args memory resume => exact ⟨_, .call body⟩
  | returned value memory =>
    cases k with
    | root => exact ⟨_, .returned body⟩
    | call resume rest => exact ⟨_, .resume body⟩
  | failed reason memory => exact ⟨_, .failed body⟩
  | @choose A support resume =>
    exact ⟨_, .choose body (@NondetSupportingType.from_hash A support 0)⟩

end Lift.P2.Total
