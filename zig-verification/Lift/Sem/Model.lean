module

public import Lift.Sem.Reaches

@[expose] public section

namespace Lift.Sem

open Lift.P2.Total

/-- The result of a generated model. -/
inductive Res (R : Type) where
  | ok (r : R)
  | stuck (why : String)
  | noFuel

/-- A model of one function at one level, with its relation to the machine. -/
structure Model (A R : Type) where
  /-- The entry state holds the input. -/
  rep : CpuPolicy → A → MachineState → Prop
  /-- The model returns `r` on `a`. -/
  returns : A → R → Prop
  /-- The return state (last argument) holds the result, relative to the entry state. -/
  post : A → R → MachineState → MachineState → Prop

/-- When the model returns, each execution from a state that holds the input gets to `post`. -/
def Decompiles {A R : Type} (step : MachineState → Effects) (M : Model A R) : Prop :=
  ∀ policy a r s, M.rep policy a s → M.returns a r → Reaches step policy (M.post a r s) s

/-- Each return of `hi` has a return of `lo` on the same state whose `post` gives `hi.post`. -/
def Above {A B R S : Type} (lo : Model B S) (hi : Model A R) : Prop :=
  ∀ policy a r s, hi.rep policy a s → hi.returns a r →
    ∃ b r', lo.rep policy b s ∧ lo.returns b r' ∧ ∀ t, lo.post b r' s t → hi.post a r s t

theorem Decompiles.above {A B R S : Type} {step : MachineState → Effects} {lo : Model B S}
    {hi : Model A R} (h : Decompiles step lo) (ha : Above lo hi) : Decompiles step hi := by
  intro policy a r s hrep hret
  obtain ⟨b, r', hrep', hret', hpost⟩ := ha policy a r s hrep hret
  exact (h policy b r' s hrep' hret').mono hpost

/-- A property `P` of a model that returns on each input in `C` holds for the code. -/
theorem Decompiles.transfer {A R : Type} {step : MachineState → Effects} {M : Model A R}
    (h : Decompiles step M) (C : A → Prop) (P : A → R → Prop)
    (total : ∀ a, C a → ∃ r, M.returns a r) (prop : ∀ a r, C a → M.returns a r → P a r) :
    ∀ policy a s, M.rep policy a s → C a →
      Reaches step policy (fun t => ∃ r, M.post a r s t ∧ P a r) s := by
  intro policy a s hrep hc
  obtain ⟨r, hr⟩ := total a hc
  exact (h policy a r s hrep hr).mono fun t ht => ⟨r, ht, prop a r hc hr⟩

end Lift.Sem
