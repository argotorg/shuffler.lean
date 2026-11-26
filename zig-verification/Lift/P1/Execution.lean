module

public import Lift.P1.Spec

@[expose] public section

namespace Lift.P1

/-- One possible complete response to a step's requests. All responses are retained. -/
inductive Responds : Effects → MachineState → Prop
  | done (s : MachineState) : Responds (.done s) s
  | read (a : BitVec 64) (w : Width) (ok : Unit → Effects) (s : MachineState)
      (h : Responds (ok ()) s) : Responds (.require_read_access a w ok) s
  | write (a : BitVec 64) (w : Width) (ok : Unit → Effects) (s : MachineState)
      (h : Responds (ok ()) s) : Responds (.require_write_access a w ok) s
  | exec (p : Std.Rco Int64) (ok : Unit → Effects) (s : MachineState)
      (h : Responds (ok ()) s) : Responds (.require_exec_access p ok) s
  | load (m : DataMem) (a : BitVec 64) (w : Width) (k : w.type → DataMem → Effects)
      (v : w.type) (m' : DataMem) (s : MachineState) (h : Responds (k v m') s) :
      Responds (.nonmem_load m a w k) s
  | store (m : DataMem) (a : BitVec 64) (w : Width) (v : w.type) (k : DataMem → Effects)
      (m' : DataMem) (s : MachineState) (h : Responds (k m') s) :
      Responds (.nonmem_store m a v k) s
  | choice (α : Type) (support : NondetSupportingType α) (k : α → Effects)
      (v : α) (s : MachineState) (h : Responds (k v) s) :
      Responds (@Effects.undefined α support k) s

/-- Finite execution through complete machine steps. Faults have no outgoing step. -/
inductive Reaches (step : MachineState → Effects) : Nat → MachineState → MachineState → Prop
  | zero (s : MachineState) : Reaches step 0 s s
  | succ (n : Nat) (s t u : MachineState) (h : Responds (step s) t)
      (rest : Reaches step n t u) : Reaches step (n + 1) s u

/-- Each adjacent pair in an infinite state trace follows one complete step. -/
def Follows (step : MachineState → Effects) (trace : Nat → MachineState) : Prop :=
  ∀ n, Responds (step (trace n)) (trace (n + 1))

def Diverges (step : MachineState → Effects) (s : MachineState) : Prop :=
  ∃ trace, trace 0 = s ∧ Follows step trace

theorem L1Spec.step_eq (asm : _root_.Executable) (step : MachineState → Effects)
    (h : L1Spec asm step) : step = (fun s => asm.step s .done) := by
  exact funext h

/-- This also covers observations of faults and of requests that receive no response. -/
theorem L1Spec.observation_eq.{u} (asm : _root_.Executable) (step : MachineState → Effects)
    (h : L1Spec asm step) (α : Sort u) (observe : (MachineState → Effects) → α) :
    observe step = observe (fun s => asm.step s .done) := by
  rw [L1Spec.step_eq asm step h]

theorem L1Spec.reaches_iff (asm : _root_.Executable) (step : MachineState → Effects)
    (h : L1Spec asm step) (n : Nat) (s t : MachineState) :
    Reaches step n s t ↔ Reaches (fun s => asm.step s .done) n s t := by
  rw [L1Spec.step_eq asm step h]

theorem L1Spec.follows_iff (asm : _root_.Executable) (step : MachineState → Effects)
    (h : L1Spec asm step) (trace : Nat → MachineState) :
    Follows step trace ↔ Follows (fun s => asm.step s .done) trace := by
  rw [L1Spec.step_eq asm step h]

theorem L1Spec.diverges_iff (asm : _root_.Executable) (step : MachineState → Effects)
    (h : L1Spec asm step) (s : MachineState) :
    Diverges step s ↔ Diverges (fun s => asm.step s .done) s := by
  rw [L1Spec.step_eq asm step h]

end Lift.P1
