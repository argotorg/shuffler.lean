module

public import Lift.P1.Command
public import Lift.P1.Execution
public import Lift.Toys.Code

@[expose] public section

/-! The exact L1 of the extended toy unit (`Lift/Toys/data/toy.s`, `Lift/Toys/Code.lean`), and the entry
PC of each toy function. The values are the linked addresses of `nm` in the run of `compiler_layout.py`;
the theorems below check each value against the labels of `Code.code`. A change of `toy.zig` moves the
addresses: then these theorems fail. -/

#lift_exact Lift.Toys.Code.code as Lift.Toys.L1

namespace Lift.Toys

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

def toyCountPC : Int64 := 0x100000
def toyTailPC : Int64 := 0x10002d
def toyFindPC : Int64 := 0x100032
def toyClampPC : Int64 := 0x10004b
def toyOuterPC : Int64 := 0x100058
def toyTwoPC : Int64 := 0x10007f
def toyHalfPC : Int64 := 0x1000a1
def toyFillPC : Int64 := 0x1000a8
def toyAtPC : Int64 := 0x1000b9
def toyWalkPC : Int64 := 0x1000c5
def toyJobPC : Int64 := 0x1000d6
def toySumPC : Int64 := 0x1000f8
def toyMarkPC : Int64 := 0x10010b
def toyIncPC : Int64 := 0x100110

/-- The first address after the unit. -/
def toyEndPC : Int64 := 0x100115

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

end Lift.Toys
