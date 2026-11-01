module

public import BbuKraken.FlatPlan

/-! The data shared by the assembly and Shuffler contracts. -/

@[expose] public section

namespace PlanBridge

structure Input where
  m : Bbu.Word
  n : Bbu.Word
  source : Vector Bbu.StackSlot Bbu.MAX_N
  target : Vector Bbu.StackSlot Bbu.MAX_N
  spilled : BitVec 32 → BitVec 8
  idCount : Bbu.Word
  allowed : BitVec 8
  strategy : BitVec 8
  dropped : Vector (BitVec 8) Bbu.MAX_N
  data : Vector Bbu.StackSlot Bbu.MAX_N
  sources : Vector Bbu.Word Bbu.MAX_N

abbrev FlatResult := Bbu.Word × Option (Bbu.Flat.Status × Bbu.Flat.PSt)

def Input.run (i : Input) (us : Nat → Bbu.Flat.RunU) : FlatResult :=
  Bbu.Flat.planEntry i.m i.n i.source i.target i.spilled i.idCount i.allowed i.strategy
    i.dropped i.data i.sources us

end PlanBridge
