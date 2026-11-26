import Lift.P1.Command
import Lift.P1.Execution
import Skel.Test.CallMem.Code

/-! The exact L1 of the synthetic pair of `Skel/Test/CallMem/Code.lean`, and the entry PC of each function (the linked
addresses of the layout of the sizes). The theorems check each value against the labels of `Code.code`. -/

#lift_exact Skel.Test.CallMem.Code.code as Skel.Test.CallMem.L1

namespace Skel.Test.CallMem

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

def putPC : Int64 := 0x100000
def putCallPC : Int64 := 0x100006
def putBadPC : Int64 := 0x100014
def incPC : Int64 := 0x10001f
def twoPC : Int64 := 0x100024
def twicePC : Int64 := 0x10003b
def twoDepthPC : Int64 := 0x100054

/-- The first address after the unit. -/
def callMemEndPC : Int64 := 0x10006c

/-- Each entry PC is the address of the label of its name. -/
theorem entryPCs_label :
    [("put", putPC), ("putCall", putCallPC), ("putBad", putBadPC), ("inc", incPC), ("two", twoPC), ("twice", twicePC),
      ("twoDepth", twoDepthPC)].all
      (fun p => (Code.code.labels).label p.1 == p.2) = true := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The sizes add up to `callMemEndPC`. -/
theorem callMemEndPC_eq :
    Code.code.startAddr + Int64.ofNat (Code.code.sizeBefore Code.code.program.length) = callMemEndPC := by
  decide +kernel

end Skel.Test.CallMem
