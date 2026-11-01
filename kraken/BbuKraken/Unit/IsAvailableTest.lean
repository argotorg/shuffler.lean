module

public import BbuKraken.Unit.IsAvailable
import all BbuKraken.Unit.IsAvailable

@[expose] public section

open Bbu

-- A value absent from the working stack must not become available merely because its
-- destination is assigned. A spilled value is available in the same state.
private def slot : StackSlot := ⟨7, Value, 5⟩
private def state : Flat.St where
  target := Vector.replicate MAX_N slot
  targetSize := 1
  spills := fun _ => 0
  data := Vector.replicate MAX_N slot
  size := 0
  trace := []
  dest := Vector.replicate MAX_N 0
  pos := Vector.replicate MAX_N 0
  pend := 0
  blockedOffset := 0
  blockedExcess := 0

example : Flat.isAvailable state 0 = false := by decide +kernel
example : Flat.isAvailable { state with spills := fun _ => 1 } 0 = true := by decide +kernel
example : Flat.isAvailable { state with size := 1 } 0 = true := by decide +kernel

-- Availability depends on the live stack, even if no target mapping is assigned.
example : Flat.isAvailable { state with size := 1, dest := Vector.replicate MAX_N Flat.NONE } 0 = true :=
  by decide +kernel

-- Literal values and the two free kinds do not need a stack copy or a spill.
example : Flat.isAvailable { state with target := Vector.replicate MAX_N ⟨7, Value, Const⟩ } 0 = true :=
  by decide +kernel
example : Flat.isAvailable { state with target := Vector.replicate MAX_N StackSlot.junk } 0 = true :=
  by decide +kernel
example : Flat.isAvailable
    { state with target := Vector.replicate MAX_N ⟨7, FunctionCallReturnLabel, 5⟩ } 0 = true :=
  by decide +kernel

-- A function return label is not freely generated.
example : Flat.isAvailable
    { state with target := Vector.replicate MAX_N ⟨7, FunctionReturnLabel, 5⟩ } 0 = false :=
  by decide +kernel

example [Host] [FunDecls]
    (hs : Sep.Spec Names.isSpilled Unit.isSpilledA 0 Unit.isSpilledQ)
    (hc : Sep.Spec Names.shallowestCopyPosition Unit.shallowestCopyA 0 Unit.shallowestCopyQ) :
    Unit.UnitThm isAvailableAsm Unit.isAvailableA 3 Unit.isAvailableQ :=
  Unit.isAvailable_unit hs hc
