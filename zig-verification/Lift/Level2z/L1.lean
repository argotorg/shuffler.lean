module

public import Lift.P1.Command
public import Lift.P1.Execution
public import Lift.Level2z.Code

@[expose] public section

/-! The exact L1 of benchmark level 2 in Zig (`Lift/LLVM/data/level2z/level2z.s`, `Lift/Toys/data/level2z.s`,
`Lift/Level2z/Code.lean`), and the entry PC of each function. The values are the linked addresses of `nm` in the
run of `compiler_layout.py` (`Lift/Level2z/README.md`); the theorems below check each value against the labels of
`Code.code`. A change of `level2z.zig` moves the addresses: then these theorems fail. -/

#lift_exact Lift.Level2z.Code.code as Lift.Level2z.L1

namespace Lift.Level2z

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

def l2zAliasPC : Int64 := 0x100000
def l2zCallLoopPC : Int64 := 0x100031
def l2zWrapPC : Int64 := 0x100099
def l2zPtrStorePC : Int64 := 0x1000a7
def l2zStackCallerPC : Int64 := 0x1000ce
def l2zArgs8PC : Int64 := 0x1000ed
def l2zArithPC : Int64 := 0x10010f
def l2zFramePC : Int64 := 0x100141
def l2zExit3PC : Int64 := 0x100199
def l2zNestPC : Int64 := 0x1001bb
def l2zTwoLoopsPC : Int64 := 0x1001e8
def l2zIdxPopPC : Int64 := 0x10020f
def l2zIdxPushPC : Int64 := 0x10023d
def l2zFieldPC : Int64 := 0x100298
def l2zNarrowPC : Int64 := 0x1002d7
def l2zBitsPC : Int64 := 0x100309
def l2zFlagsPC : Int64 := 0x100370

/-- The first address after the unit. -/
def l2zEndPC : Int64 := 0x1003ee

/-- Each entry PC is the address of the label of its name. -/
theorem entryPCs_label :
    [("l2zAlias", l2zAliasPC), ("l2zCallLoop", l2zCallLoopPC), ("l2zWrap", l2zWrapPC),
      ("l2zPtrStore", l2zPtrStorePC), ("l2zStackCaller", l2zStackCallerPC), ("l2zArgs8", l2zArgs8PC),
      ("l2zArith", l2zArithPC), ("l2zFrame", l2zFramePC), ("l2zExit3", l2zExit3PC),
      ("l2zNest", l2zNestPC), ("l2zTwoLoops", l2zTwoLoopsPC), ("l2zIdxPop", l2zIdxPopPC),
      ("l2zIdxPush", l2zIdxPushPC), ("l2zField", l2zFieldPC), ("l2zNarrow", l2zNarrowPC),
      ("l2zBits", l2zBitsPC), ("l2zFlags", l2zFlagsPC)].all
      (fun p => (Code.code.labels).label p.1 == p.2) = true := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The unit starts at the first entry and its sizes add up to `l2zEndPC`. -/
theorem l2zEndPC_eq :
    Code.code.startAddr + Int64.ofNat (Code.code.sizeBefore Code.code.program.length) = l2zEndPC := by
  decide +kernel

theorem l2zAliasPC_start : l2zAliasPC = Code.code.startAddr := by decide +kernel

end Lift.Level2z
