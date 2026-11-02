module

public import FlatShuffler.Unit.Run.Model
import all FlatShuffler.Unit.Run.Model

@[expose] public section

namespace FlatShuffler.Unit.RunU.Test
open FlatShuffler

private def empty : Flat.St where
  target := Vector.replicate maxStackSize StackSlot.junk
  targetSize := 0
  spills := fun _ => 0
  data := Vector.replicate maxStackSize StackSlot.junk
  size := 0
  trace := []
  dest := Vector.replicate maxStackSize Flat.NONE
  pos := Vector.replicate maxStackSize Flat.NONE
  pend := 0
  blockedOffset := 0
  blockedExcess := 0

private def planned : Vector Word maxStackSize := Vector.replicate maxStackSize Flat.NONE

-- The empty target goes directly to `buildBottomUp`.
#guard (Flat.emissionRun planned zeroLocals empty).1 = .done

-- The first check rejects a wrong stack-size/pending-generation sum.
#guard (Flat.emissionRun planned zeroLocals { empty with pend := 1 }).1 =
    .assertionFailed

-- A pending generation must have an unmapped target offset.
#guard (Flat.emissionRun planned zeroLocals
    { empty with targetSize := 1, pend := 1, pos := Vector.replicate maxStackSize 0 }).1 =
    .assertionFailed

-- A value with no stack copy and no spill cannot be generated.
#guard (Flat.emissionRun planned zeroLocals
    { empty with targetSize := 1, pend := 1, target := Vector.replicate maxStackSize ⟨7, Value, 5⟩ }).1 =
    .assertionFailed

-- The label check still rejects an unmapped return label when its opcode passes availability.
private def labelState : Flat.St :=
  { empty with targetSize := 1, pend := 1, target := Vector.replicate maxStackSize ⟨7, FunctionReturnLabel, Const⟩ }

#guard Flat.availableFrom labelState 0#64 = true
#guard Flat.labelsFrom labelState 0#64 = false
#guard (Flat.emissionRun planned zeroLocals labelState).1 = .assertionFailed

-- A free target with one pending generation reaches the generation loop.
#guard (Flat.emissionRun planned zeroLocals { empty with targetSize := 1, pend := 1 }).1 =
    .done

end FlatShuffler.Unit.RunU.Test
