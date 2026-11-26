module

public import Lift.P2.Total.Spec
public import Lift.P2.Total.Memory
public import Lift.Sem.MappedMemory

@[expose] public section

/-! The entry and the exit of a System V call with scalar arguments. The argument and result
registers are in the `rep` and `post` of each model. -/

namespace Lift.Sem.SysV

open Lift.P2.Total

/-- The policy permits the execution of each instruction `[a, b)` in the code range `[lo, hi)`. -/
def ExecRange (policy : CpuPolicy) (lo hi : Int64) : Prop :=
  ∀ a b : Int64, lo ≤ a → a < b → b ≤ hi → policy.permits (.execute a b) = true

/-- The return address of a call from `s`: the word at `rsp`, if the memory has it. -/
def retAddr (s : MachineState) : Option Int64 :=
  (Mem.loadInt s.data.dmem s.data.regs.rsp.toBitVec 8).map fun v => Int64.ofBitVec (BitVec.ofInt 64 v)

/-- The state `s` is at the entry of a call of the code `[lo, hi)`. -/
structure Entry (policy : CpuPolicy) (lo hi entry : Int64) (s : MachineState) : Prop where
  pc : s.pc = entry
  exec : ExecRange policy lo hi
  retRead : policy.permits (.read s.data.regs.rsp.toBitVec .W64) = true
  ret : ∃ ra, retAddr s = some ra

/-- The state `t` is a return of the call from `s`. -/
structure Exit (s t : MachineState) : Prop where
  pc : retAddr s = some t.pc
  abi : AbiRestored s t

end Lift.Sem.SysV
