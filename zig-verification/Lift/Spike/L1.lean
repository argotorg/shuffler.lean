module

public import Lift.P1.Command
public import Lift.P1.Execution
public import Lift.Spike.Code

@[expose] public section

/-! The exact L1 of the toy unit (`Lift/LLVM/data/toy/toy.s`, `Lift/Spike/Code.lean`), and the entry PC of each toy function. -/

#lift_exact Lift.Spike.Code.code as Lift.Spike.L1

namespace Lift.Spike

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

/-- The entry PCs. Their values are the linked addresses of `objdump` (`compiler_layout.py` checks the sizes
that give them); the theorems below check each value against the labels of `Code.code`. -/
def toyJobPC : Int64 := 0x100000
def toySumPC : Int64 := 0x100022
def toyTwoPC : Int64 := 0x100035
def toyHalfPC : Int64 := 0x100057
def toyMarkPC : Int64 := 0x10005e
def toyIncPC : Int64 := 0x100063

/-- The first address after the unit. -/
def toyEndPC : Int64 := 0x100068

theorem toyJobPC_label : (Code.code.labels).label "toyJob" = toyJobPC := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel
theorem toySumPC_label : (Code.code.labels).label "toySum" = toySumPC := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel
theorem toyTwoPC_label : (Code.code.labels).label "toyTwo" = toyTwoPC := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel
theorem toyHalfPC_label : (Code.code.labels).label "toyHalf" = toyHalfPC := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel
theorem toyMarkPC_label : (Code.code.labels).label "toyMark" = toyMarkPC := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel
theorem toyIncPC_label : (Code.code.labels).label "toyInc" = toyIncPC := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The unit starts at the first entry and its sizes add up to `toyEndPC`. -/
theorem toyEndPC_eq : Code.code.startAddr + Int64.ofNat (Code.code.sizeBefore Code.code.program.length) = toyEndPC := by
  decide +kernel

theorem toyJobPC_start : toyJobPC = Code.code.startAddr := by decide +kernel

end Lift.Spike
