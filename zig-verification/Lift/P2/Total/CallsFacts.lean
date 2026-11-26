module

public import Lift.P2.Total.Memory

@[expose] public section

namespace Lift.P2.Total.Calls

/-- Keep a read equation until both paths expose the access. The equation
includes successful values, failure tags, and projected failure memory. -/
structure ReadBridge (policy : CpuPolicy) (visible : DataMem → DataMem)
    (source target : DataMem) (address : BitVec 64) (width : Width) : Prop where
  same : readRam policy target address width =
    (readRam policy source address width).mapError
      (fun failure => (failure.1, visible failure.2))

theorem readRam_bridge (policy : CpuPolicy) (visible : DataMem → DataMem)
    (source target : DataMem) (address : BitVec 64) (width : Width)
    (bridge : ReadBridge policy visible source target address width) :
    readRam policy target address width =
      (readRam policy source address width).mapError
        (fun failure => (failure.1, visible failure.2)) :=
  bridge.same

end Lift.P2.Total.Calls
