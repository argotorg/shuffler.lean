import BbuKraken.Unit.Run.Model

namespace Bbu.Unit.RunU.Test
open Bbu

private def empty : Flat.St where
  target := Vector.replicate MAX_N StackSlot.junk
  targetSize := 0
  spills := fun _ => 0
  data := Vector.replicate MAX_N StackSlot.junk
  size := 0
  trace := []
  dest := Vector.replicate MAX_N Flat.NONE
  pos := Vector.replicate MAX_N Flat.NONE
  pend := 0
  blockedOffset := 0
  blockedExcess := 0

private def planned : Vector Word MAX_N := Vector.replicate MAX_N Flat.NONE

-- The empty target goes directly to `buildBottomUp`.
#guard (Flat.emissionRun planned zeroLocals empty).1 = .done

-- The first check rejects a wrong stack-size/pending-generation sum.
#guard (Flat.emissionRun planned zeroLocals { empty with pend := 1 }).1 =
    .assertionFailed

-- A pending generation must have an unmapped target offset.
#guard (Flat.emissionRun planned zeroLocals
    { empty with targetSize := 1, pend := 1, pos := Vector.replicate MAX_N 0 }).1 =
    .assertionFailed

-- A value with no stack copy and no spill cannot be generated.
#guard (Flat.emissionRun planned zeroLocals
    { empty with targetSize := 1, pend := 1, target := Vector.replicate MAX_N ⟨7, Value, 5⟩ }).1 =
    .assertionFailed

-- The label check still rejects an unmapped return label when its opcode passes availability.
private def labelState : Flat.St :=
  { empty with targetSize := 1, pend := 1, target := Vector.replicate MAX_N ⟨7, FunctionReturnLabel, Const⟩ }

#guard Flat.availableFrom labelState 0#64 = true
#guard Flat.labelsFrom labelState 0#64 = false
#guard (Flat.emissionRun planned zeroLocals labelState).1 = .assertionFailed

-- A free target with one pending generation reaches the generation loop.
#guard (Flat.emissionRun planned zeroLocals { empty with targetSize := 1, pend := 1 }).1 =
    .done

end Bbu.Unit.RunU.Test
