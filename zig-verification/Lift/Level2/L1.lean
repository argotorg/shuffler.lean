module

public import Lift.P1.Command
public import Lift.P1.Execution
public import Lift.Level2.Code

@[expose] public section

/-! The exact L1 of benchmark level 2 (`Lift/Toys/data/level2.s`, `Lift/Level2/Code.lean`), and the entry
PC of each function. The values are the linked addresses of `nm` in the run of `compiler_layout.py`;
the theorems below check each value against the labels of `Code.code`. A change of `level2.s` moves the
addresses: then these theorems fail. -/

#lift_exact Lift.Level2.Code.code as Lift.Level2.L1

namespace Lift.Level2

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

def l2FlagsPC : Int64 := 0x100000
def l2BitsPC : Int64 := 0x10008b
def l2ArithPC : Int64 := 0x1000ed
def l2NarrowPC : Int64 := 0x100129
def l2FieldPC : Int64 := 0x100166
def l2PtrStorePC : Int64 := 0x10019e
def l2IdxPushPC : Int64 := 0x1001c2
def l2IdxPopPC : Int64 := 0x100201
def l2TwoLoopsPC : Int64 := 0x10022a
def l2NestPC : Int64 := 0x100251
def l2Exit3PC : Int64 := 0x100278
def l2FramePC : Int64 := 0x10029b
def l2Args8PC : Int64 := 0x100308
def l2StackCallerPC : Int64 := 0x100331
def l2WrapPC : Int64 := 0x100358
def l2CallLoopPC : Int64 := 0x100368
def l2AliasPC : Int64 := 0x1003cf

/-- The first address after the unit. -/
def l2EndPC : Int64 := 0x10040c

/-- Each entry PC is the address of the label of its name. -/
theorem entryPCs_label :
    [("l2Flags", l2FlagsPC), ("l2Bits", l2BitsPC), ("l2Arith", l2ArithPC),
      ("l2Narrow", l2NarrowPC), ("l2Field", l2FieldPC), ("l2PtrStore", l2PtrStorePC),
      ("l2IdxPush", l2IdxPushPC), ("l2IdxPop", l2IdxPopPC), ("l2TwoLoops", l2TwoLoopsPC),
      ("l2Nest", l2NestPC), ("l2Exit3", l2Exit3PC), ("l2Frame", l2FramePC),
      ("l2Args8", l2Args8PC), ("l2StackCaller", l2StackCallerPC), ("l2Wrap", l2WrapPC),
      ("l2CallLoop", l2CallLoopPC), ("l2Alias", l2AliasPC)].all
      (fun p => (Code.code.labels).label p.1 == p.2) = true := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The unit starts at the first entry and its sizes add up to `l2EndPC`. -/
theorem l2EndPC_eq :
    Code.code.startAddr + Int64.ofNat (Code.code.sizeBefore Code.code.program.length) = l2EndPC := by
  decide +kernel

theorem l2FlagsPC_start : l2FlagsPC = Code.code.startAddr := by decide +kernel

end Lift.Level2
