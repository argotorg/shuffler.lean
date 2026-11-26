import Lift.P1.Command
import Lift.P1.Execution
import Skel.Test.Saved.Code

/-! The exact L1 of the synthetic functions of `Skel/Test/Saved/Code.lean`, and the entry PC of each function (the linked
addresses of the layout of the sizes). The theorems check each value against the labels of `Code.code`. -/

#lift_exact Skel.Test.Saved.Code.code as Skel.Test.Saved.L1

namespace Skel.Test.Saved

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

def leafPC : Int64 := 0x100000
def save2PC : Int64 := 0x100004
def save2bPC : Int64 := 0x10002c
def save4PC : Int64 := 0x100051
def save4bPC : Int64 := 0x10007f
def save2nPC : Int64 := 0x1000aa
def save2xPC : Int64 := 0x1000cb
def frame8PC : Int64 := 0x1000f3
def frame4PC : Int64 := 0x100104
def frameCallPC : Int64 := 0x100115

/-- The first address after the unit. -/
def savedEndPC : Int64 := 0x100123

/-- Each entry PC is the address of the label of its name. -/
theorem entryPCs_label :
    [("leaf", leafPC), ("save2", save2PC), ("save2b", save2bPC), ("save4", save4PC), ("save4b", save4bPC),
      ("save2n", save2nPC), ("save2x", save2xPC), ("frame8", frame8PC), ("frame4", frame4PC),
      ("frameCall", frameCallPC)].all
      (fun p => (Code.code.labels).label p.1 == p.2) = true := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The sizes add up to `savedEndPC`. -/
theorem savedEndPC_eq :
    Code.code.startAddr + Int64.ofNat (Code.code.sizeBefore Code.code.program.length) = savedEndPC := by
  decide +kernel

end Skel.Test.Saved
