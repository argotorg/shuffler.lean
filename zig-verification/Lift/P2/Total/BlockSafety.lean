module

public import Lift.P2.Total.System

@[expose] public section

namespace Lift.P2.Total

/-- A local access condition holds at every reached target state.
This condition says nothing about successful accesses or termination. -/
def BlockSafety {S O : Type} (system : System S O) (localSafe : S → Prop)
    (state : S) : Prop :=
  ∀ reached, system.Reaches state reached → localSafe reached

theorem BlockSafety.here {S O : Type} {system : System S O}
    {localSafe : S → Prop} {state : S} (safe : BlockSafety system localSafe state) :
    localSafe state := safe state (.refl state)

theorem BlockSafety.next {S O : Type} {system : System S O}
    {localSafe : S → Prop} {state target : S}
    (safe : BlockSafety system localSafe state) (edge : system.step state target) :
    BlockSafety system localSafe target := by
  intro reached path
  apply safe reached
  induction path with
  | refl => exact .tail (.refl state) edge
  | tail _ next ih => exact .tail ih next

/-- A finite supply of local safety facts. Its bound limits proof expansion.
The persistent safety condition still covers all future states. -/
def BlockSafetyFacts {S O : Type} (system : System S O) (localSafe : S → Prop) :
    Nat → S → Prop
  | 0, state => BlockSafety system localSafe state
  | depth + 1, state =>
      BlockSafety system localSafe state ∧ localSafe state ∧
        ∀ target, system.step state target → BlockSafetyFacts system localSafe depth target

theorem BlockSafety.facts {S O : Type} {system : System S O}
    {localSafe : S → Prop} {state : S} (safe : BlockSafety system localSafe state)
    (depth : Nat) : BlockSafetyFacts system localSafe depth state := by
  induction depth generalizing state with
  | zero => exact safe
  | succ depth ih => exact ⟨safe, safe.here, fun _ edge => ih (safe.next edge)⟩

/-- Each finite supply retains safety at its current state. -/
theorem BlockSafetyFacts.safe {S O : Type} {system : System S O}
    {localSafe : S → Prop} {depth : Nat} {state : S}
    (facts : BlockSafetyFacts system localSafe depth state) :
    BlockSafety system localSafe state := by
  cases depth with
  | zero => exact facts
  | succ _ => exact facts.1

end Lift.P2.Total
