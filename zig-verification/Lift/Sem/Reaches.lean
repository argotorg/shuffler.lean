module

public import Lift.P2.Total.Machine

@[expose] public section

namespace Lift.Sem

open Lift.P2.Total

/-- Each execution from `s` gets to a state in `Q`; no step fails; no execution is infinite. -/
inductive Reaches (step : MachineState → Effects) (policy : CpuPolicy)
    (Q : MachineState → Prop) : MachineState → Prop
  | done {s : MachineState} : Q s → Reaches step policy Q s
  | step {s : MachineState} :
      (∀ r, Handled policy id s.data.dmem (step s) r → ∃ t, r = .next t) →
      (∀ t, Handled policy id s.data.dmem (step s) (.next t) → Reaches step policy Q t) →
      Reaches step policy Q s

/-- Sequence: reach `Q`, then from each state in `Q` reach `Q'`. -/
theorem Reaches.seq {step : MachineState → Effects} {policy : CpuPolicy}
    {Q Q' : MachineState → Prop} {s : MachineState} (h : Reaches step policy Q s)
    (k : ∀ t, Q t → Reaches step policy Q' t) : Reaches step policy Q' s := by
  induction h with
  | done hq => exact k _ hq
  | step fails _ ih => exact .step fails ih

/-- Weaken the postcondition. -/
theorem Reaches.mono {step : MachineState → Effects} {policy : CpuPolicy}
    {Q Q' : MachineState → Prop} {s : MachineState} (h : Reaches step policy Q s)
    (hQ : ∀ t, Q t → Q' t) : Reaches step policy Q' s := by
  exact h.seq fun t ht => .done (hQ t ht)

/-- One step: each result of the step is a next state from which `Q` is reached. -/
theorem Reaches.of_step {step : MachineState → Effects} {policy : CpuPolicy}
    {Q : MachineState → Prop} {s : MachineState}
    (h : ∀ r, Handled policy id s.data.dmem (step s) r → ∃ t, r = .next t ∧ Reaches step policy Q t) :
    Reaches step policy Q s := by
  refine .step (fun r hr => ?_) (fun t ht => ?_)
  · obtain ⟨t, e, _⟩ := h r hr
    exact ⟨t, e⟩
  · obtain ⟨t', e, h'⟩ := h _ ht
    cases e
    exact h'

/-- `Reaches` for a step function with `L1Spec` is `Reaches` for the Kraken step function. -/
theorem Reaches.l1Spec_iff (asm : _root_.Executable) (step : MachineState → Effects)
    (spec : Lift.P1.L1Spec asm step) (policy : CpuPolicy) (Q : MachineState → Prop)
    (s : MachineState) :
    Reaches step policy Q s ↔ Reaches (fun s => asm.step s .done) policy Q s := by
  rw [Lift.P1.L1Spec.step_eq asm step spec]

end Lift.Sem
