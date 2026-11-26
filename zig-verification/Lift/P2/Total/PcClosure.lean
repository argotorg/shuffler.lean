module

public import Lift.P2.Total.Next
public import Lift.P2.Total.Unroll

@[expose] public section

namespace Lift.P2.Total

/-- The parts of the call state needed by a read-only function with no frame. -/
def ReadOnlyFrame (initial current : MachineData) : Prop :=
  current.dmem = initial.dmem ∧ current.regs.rsp = initial.regs.rsp

theorem AllNext.mono (first second : MachineState → Prop) (effect : Effects)
    (change : ∀ state, first state → second state)
    (all : AllNext first effect) : AllNext second effect := by
  induction effect with
  | done state => exact change state all
  | undefined next ih => exact fun value => ih value (all value)
  | require_read_access address width next ih => exact ih () all
  | require_write_access address width next ih => exact ih () all
  | require_exec_access range next ih => exact ih () all
  | fault tag => trivial
  | gp_unaligned address bytes => trivial
  | unimplemented message => trivial
  | nonmem_load memory address width next ih => trivial
  | nonmem_store memory address value next ih => trivial

/-- Transport a local summary across a PC equality without unfolding the step. -/
theorem AllNext.of_pc (step : MachineState → Effects)
    (post : Int64 → MachineState → Prop) (data : MachineData) (actual expected : Int64)
    (equal : actual = expected)
    (all : AllNext (post expected) (step ⟨data, expected⟩)) :
    AllNext (post actual) (step ⟨data, actual⟩) := by
  cases equal
  exact all

/-- A strictly decreasing natural-number rank bounds every path of steps.
The invariant need not assert that the next instruction succeeds. -/
theorem System.no_steps_of_rank {S O : Type} (system : System S O)
    (invariant : S → Prop) (rank : S → Nat)
    (decrease : ∀ state next, invariant state → system.step state next →
      invariant next ∧ rank next < rank state)
    (depth : Nat) (state : S) (valid : invariant state) (bound : rank state < depth) :
    ∀ final, ¬ system.Steps depth state final := by
  induction depth generalizing state with
  | zero => exact (Nat.not_lt_zero _ bound).elim
  | succ depth ih =>
    intro final path
    cases path with
    | succ edge rest =>
      obtain ⟨preserved, lower⟩ := decrease _ _ valid edge
      exact ih _ preserved (Nat.lt_of_lt_of_le lower (Nat.lt_succ_iff.mp bound)) _ rest

/-- Checked local effect summaries suffice to close a finite CPU expansion.
Faults have no next state. Every undefined response is covered by `AllNext`. -/
theorem cpuSystem_closed_of_rank {V M : Type} (step : MachineState → Effects)
    (policy : CpuPolicy) (returned : MachineState → Option V) (visible : DataMem → M)
    (invariant : MachineState → Prop) (rank : MachineState → Nat)
    (decrease : ∀ state, invariant state → returned state = none →
      AllNext (fun next => invariant next ∧ rank next < rank state) (step state))
    (depth : Nat) (initial : MachineState) (valid : invariant initial)
    (bound : rank initial < depth) :
    ∀ final, ¬ unroll (cpuSystem step policy returned visible) depth initial (.pending final) := by
  intro final pending
  apply System.no_steps_of_rank (cpuSystem step policy returned visible)
    invariant rank ?_ depth initial valid bound final
      ((unroll_pending_iff _ _ _ _).mp pending)
  intro state next current edge
  exact AllNext.sound _ policy visible state.data.dmem (step state) next
    (decrease state current edge.1) edge.2

end Lift.P2.Total
