module

public import Lift.P1.Command
public import Lift.P1.Execution
public import Lift.Toys.Fast.Code

@[expose] public section

/-! The exact L1 of the ReleaseFast toy unit (`Lift/Toys/data/releasefast/toy.s`, `Lift/Toys/Fast/Code.lean`), and the entry
PC of each toy function. The values are the linked addresses of `nm` in the run of `compiler_layout.py`;
the theorems below check each value against the labels of `Code.code`. A change of `toy.zig` moves the
addresses: then these theorems fail. -/

#lift_exact Lift.Toys.Fast.Code.code as Lift.Toys.Fast.L1

namespace Lift.Toys.Fast

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

def toyCountPC : Int64 := 0x100000
def toyTailPC : Int64 := 0x100040
def toyFindPC : Int64 := 0x100070
def toyClampPC : Int64 := 0x1000a0
def toyOuterPC : Int64 := 0x1000b0
def toyTwoPC : Int64 := 0x1000e0
def toyHalfPC : Int64 := 0x100110
def toyFillPC : Int64 := 0x100120
def toyAtPC : Int64 := 0x1001b0
def toyWalkPC : Int64 := 0x1001c0
def toyJobPC : Int64 := 0x1001e0
def toySumPC : Int64 := 0x100210
def toyMarkPC : Int64 := 0x100290
def toyIncPC : Int64 := 0x1002a0

/-- The first address after the unit. -/
def toyEndPC : Int64 := 0x1002a5

/-- Each entry PC is the address of the label of its name. -/
theorem entryPCs_label :
    [("toyCount", toyCountPC), ("toyTail", toyTailPC), ("toyFind", toyFindPC),
      ("toyClamp", toyClampPC), ("toyOuter", toyOuterPC), ("toyTwo", toyTwoPC),
      ("toyHalf", toyHalfPC), ("toyFill", toyFillPC), ("toyAt", toyAtPC), ("toyWalk", toyWalkPC),
      ("toyJob", toyJobPC), ("toySum", toySumPC), ("toyMark", toyMarkPC), ("toyInc", toyIncPC)].all
      (fun p => (Code.code.labels).label p.1 == p.2) = true := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

theorem toyWalkPC_label : (Code.code.labels).label "toyWalk" = toyWalkPC := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The unit starts at the first entry and its sizes add up to `toyEndPC`. -/
theorem toyEndPC_eq :
    Code.code.startAddr + Int64.ofNat (Code.code.sizeBefore Code.code.program.length) = toyEndPC := by
  decide +kernel

theorem toyCountPC_start : toyCountPC = Code.code.startAddr := by decide +kernel

end Lift.Toys.Fast
