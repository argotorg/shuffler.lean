module

public import FlatShuffler.Unit.Plan.ResolveMem
import all FlatShuffler.Unit.Plan.ResolveMem

@[expose] public section

open FlatShuffler

private def variableSlot : StackSlot := ⟨7, Value, 5⟩
private def literal : StackSlot := ⟨7, Value, Const⟩

private def planner (slot : StackSlot) (allow : Bool) : Flat.Planner :=
  ⟨Vector.replicate maxStackSize slot, 1, Vector.replicate maxStackSize slot, 1, allow⟩

private def mapping : Flat.Mapping :=
  ⟨Vector.replicate maxStackSize 0, Vector.replicate maxStackSize 0⟩

private def emptyMapping : Flat.Mapping :=
  ⟨Vector.replicate maxStackSize Flat.NONE, Vector.replicate maxStackSize Flat.NONE⟩

-- Nonzero local bytes test that resolve initializes its own droppedNow array.
private def locals : Flat.ResolveU :=
  ⟨Vector.replicate maxStackSize 0xff, Vector.replicate maxStackSize Flat.NONE⟩

private def resolve (p : Flat.Planner) (M current : Flat.Mapping) (excess size : Word)
    (spilled : BitVec 8) :=
  Flat.resolve p (fun _ => spilled) (Vector.replicate maxStackSize 0) M 0 excess current size locals

-- Zero excess succeeds, including an empty current stack.
example : (resolve (planner variableSlot false) mapping emptyMapping 0 0 0).1 = .dropped :=
  by decide +kernel

-- Candidate validation runs before the zero-excess return.
example : (resolve (planner variableSlot true) { mapping with dest := emptyMapping.dest }
    mapping 0 2 0).1 = .assertionFailed := by decide +kernel

-- No candidate and no usable class both return stuck.
example : (resolve (planner variableSlot true) mapping emptyMapping 1 2 0).1 = .stuck :=
  by decide +kernel
example : (resolve (planner variableSlot false) mapping mapping 1 2 0).1 = .stuck :=
  by decide +kernel

-- Spilling changes the spill byte and the dropped byte.
example : (resolve (planner variableSlot true) mapping mapping 1 2 0).1 = .dropped :=
  by decide +kernel
example : (resolve (planner variableSlot true) mapping mapping 1 2 0).2.1 7 = 1 :=
  by decide +kernel
example : Flat.get (resolve (planner variableSlot true) mapping mapping 1 2 0).2.2 0 = 1 :=
  by decide +kernel

-- A spilled value can be dropped when new spills are disabled.
example : (resolve (planner variableSlot false) mapping mapping 1 2 0xff).1 = .dropped :=
  by decide +kernel
example : (resolve (planner variableSlot false) mapping mapping 1 2 0xff).2.1 7 = 0xff :=
  by decide +kernel

-- Two current copies produce duplicate candidates. A source is dropped once.
example : (resolve (planner variableSlot true) mapping mapping 2 3 0).1 = .stuck :=
  by decide +kernel
example : Flat.get (resolve (planner variableSlot true) mapping mapping 2 3 0).2.2 0 = 1 :=
  by decide +kernel

-- A function return label remains blocked even when spills are allowed.
example : (resolve (planner ⟨7, FunctionReturnLabel, 5⟩ true) mapping mapping 1 2 0).1 = .stuck :=
  by decide +kernel

private def twoMapping : Flat.Mapping :=
  ⟨Flat.put mapping.dest 1 1, Flat.put mapping.pos 1 1⟩

private def twoCurrent : Flat.Mapping := { mapping with dest := Flat.put mapping.dest 2 1 }

private def twoPlanner : Flat.Planner :=
  { planner literal false with sourceSize := 2, targetSize := 2 }

-- Equal classes use the source with the larger destination.
example : Flat.get (resolve twoPlanner twoMapping twoCurrent 1 3 0).2.2 0 = 0 :=
  by decide +kernel
example : Flat.get (resolve twoPlanner twoMapping twoCurrent 1 3 0).2.2 1 = 1 :=
  by decide +kernel

-- A lower class takes priority over the larger destination.
private def mixedPlanner : Flat.Planner :=
  { twoPlanner with source := Flat.put (Vector.replicate maxStackSize variableSlot) 0 literal }

example : Flat.get (resolve mixedPlanner twoMapping twoCurrent 1 3 0xff).2.2 0 = 1 :=
  by decide +kernel
example : Flat.get (resolve mixedPlanner twoMapping twoCurrent 1 3 0xff).2.2 1 = 0 :=
  by decide +kernel

-- The assembly contract excludes a blocked offset that can wrap on increment.
example (r : Unit.RG) (s : MachineData) (h : rdx s = Flat.NONE) :
    ¬ Unit.resolveA r s := by
  intro ha
  have hb := ha.2.2.2.1
  rw [h] at hb
  change 18446744073709551615 < 1024 at hb
  omega
