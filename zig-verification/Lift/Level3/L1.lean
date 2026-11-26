module

public import Lift.P1.Command
public import Lift.P1.Execution
public import Lift.Level3.Code

@[expose] public section

/-! The exact L1 of the pilot code of benchmark level 3 (`Lift/Level3/data/pilot.s`, `Lift/Level3/Code.lean`),
and the entry PC of each of the 8 functions of the shuffler. The values are the linked addresses of `nm` in
the run of `as` and `ld -Ttext=0x100000` on `Lift/Level3/data/pilot.s`; the theorems below check each value
against the labels of `Code.code`. A change of `pilot.s` moves the addresses: then these theorems fail. -/

#lift_exact Lift.Level3.Code.code as Lift.Level3.L1

namespace Lift.Level3

example : Lift.P1.L1Spec Code.code L1.step := L1.spec

def workspaceAlignmentPC : Int64 := 0x100000
def spillSetAddPC : Int64 := 0x100004
def shallowestCopyPositionPC : Int64 := 0x100034
def emissionPopPC : Int64 := 0x10005a
def isRetainedPC : Int64 := 0x1000b4
def mappingMapPC : Int64 := 0x1000bd
def closestCopyPC : Int64 := 0x1000f0
def mapInPlacePC : Int64 := 0x1001bb

/-- The first address after the unit. -/
def pilotEndPC : Int64 := 0x10022b

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

end Lift.Level3
