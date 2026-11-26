module

public import Lift.P1.Command
public import Lift.P1.Execution
public import Lift.Level3.Fast.Code

@[expose] public section

/-! The exact L1 of the ReleaseFast pilot code of benchmark level 3 (`Lift/Level3/data/releasefast/pilot.s`,
`Lift/Level3/Fast/Code.lean`), and the entry PC of each of the 8 functions of the shuffler. The values are the linked
addresses of `nm` in the run of `as` and `ld -Ttext=0x100000` on `Lift/Level3/data/releasefast/pilot.s`; the theorems
below check each value against the labels of `Code.code`. A change of `pilot.s` moves the addresses: then these theorems
fail. -/

#lift_exact Lift.Level3.Fast.Code.code as Lift.Level3.Fast.L1

namespace Lift.Level3.Fast

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

def workspaceAlignmentPC : Int64 := 0x100000
def spillSetAddPC : Int64 := 0x100006
def shallowestCopyPositionPC : Int64 := 0x100036
def emissionPopPC : Int64 := 0x100064
def isRetainedPC : Int64 := 0x1000c2
def mappingMapPC : Int64 := 0x1000cb
def closestCopyPC : Int64 := 0x1000fe
def mapInPlacePC : Int64 := 0x1002bd

/-- The first address after the unit. -/
def pilotEndPC : Int64 := 0x100335

/-- Each entry PC is the address of the label of its name. -/
theorem entryPCs_label :
    [("solidity_shuffler_workspaceAlignment", workspaceAlignmentPC),
      (".Lshuffler.SpillSet.add", spillSetAddPC),
      (".Lshuffler.Emission.shallowestCopyPosition", shallowestCopyPositionPC),
      (".Lshuffler.Emission.pop", emissionPopPC),
      (".Lshuffler.Planner.isRetained", isRetainedPC),
      (".Lshuffler.MappingBuilder.map", mappingMapPC),
      (".Lshuffler.MappingBuilder.closestCopy", closestCopyPC),
      (".Lshuffler.MappingBuilder.mapInPlace", mapInPlacePC)].all
      (fun p => (Code.code.labels).label p.1 == p.2) = true := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The unit starts at its first entry and its sizes add up to `pilotEndPC`. -/
theorem pilotEndPC_eq :
    Code.code.startAddr + Int64.ofNat (Code.code.sizeBefore Code.code.program.length) = pilotEndPC := by
  decide +kernel

theorem workspaceAlignmentPC_start : workspaceAlignmentPC = Code.code.startAddr := by decide +kernel

end Lift.Level3.Fast
