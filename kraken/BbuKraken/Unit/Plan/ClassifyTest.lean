module

public import BbuKraken.Unit.Plan.ClassifyMore
import all BbuKraken.Unit.Plan.ClassifyMore

@[expose] public section

open Bbu

private def variableSlot : StackSlot := ⟨7, Value, 5⟩
private def literal : StackSlot := ⟨7, Value, Const⟩

private def planner (source target : StackSlot) (m : Word) (allowed : Bool) : Flat.Planner :=
  ⟨Vector.replicate MAX_N source, m, Vector.replicate MAX_N target, 1, allowed⟩

private def mapping : Flat.Mapping :=
  ⟨Vector.replicate MAX_N 0, Vector.replicate MAX_N 0⟩

private def classify (source target : StackSlot) (m : Word) (allowed : Bool)
    (spilled droppedNow : BitVec 8) : BitVec 8 :=
  Flat.classify (planner source target m allowed) (fun _ => spilled) mapping
    (Vector.replicate MAX_N droppedNow) 0

-- A function return label is never a candidate, even when other tests succeed.
example : classify ⟨7, FunctionReturnLabel, 5⟩ StackSlot.junk 2 true 1 0 = Flat.NOCLASS :=
  by decide +kernel
example : classify ⟨7, FunctionReturnLabel, Const⟩ StackSlot.junk 2 true 1 0 = Flat.NOCLASS :=
  by decide +kernel

-- A junk destination permits a drop. A demanded destination needs the slot.
example : classify literal literal 1 false 0 0 = 1 := by decide +kernel
example : classify literal StackSlot.junk 1 false 0 0 = 0 := by decide +kernel
example : classify variableSlot variableSlot 1 false 0xff 0 = 2 := by decide +kernel
example : classify variableSlot StackSlot.junk 1 false 0xff 0 = 0 := by decide +kernel
example : classify variableSlot variableSlot 2 false 0 0 = 3 := by decide +kernel
example : classify variableSlot StackSlot.junk 2 false 0 0 = 0 := by decide +kernel

-- The slot at the selected offset does not count as another copy.
example : classify variableSlot variableSlot 1 false 0 0 = Flat.NOCLASS := by decide +kernel
example : classify variableSlot variableSlot 1 true 0 0 = Flat.SPILL := by decide +kernel

-- A dropped copy cannot supply a retained copy. Spilling is a separate choice.
example : classify variableSlot variableSlot 2 false 0 1 = Flat.NOCLASS := by decide +kernel
example : classify variableSlot variableSlot 2 true 0 1 = Flat.SPILL := by decide +kernel

-- An undemanded slot can be dropped at a junk destination without a copy.
example : classify variableSlot StackSlot.junk 1 false 0 0 = 0 := by decide +kernel
example : classify variableSlot literal 1 false 0 0 = Flat.NOCLASS := by decide +kernel

-- A non-value kind cannot be spilled. The free-generation rule still reads its opcode.
example : classify ⟨7, 0xff, 5⟩ variableSlot 1 true 0xff 0 = Flat.NOCLASS := by decide +kernel
example : classify ⟨7, 0xff, Const⟩ variableSlot 1 false 0 0 = 1 := by decide +kernel
example : classify ⟨7, 0xff, 5⟩ variableSlot 2 true 0xff 0 = 3 := by decide +kernel
example : classify ⟨7, 0xff, 5⟩ variableSlot 2 true 0xff 1 = Flat.NOCLASS := by decide +kernel

-- The two adjacent free kinds exercise both ends of the assembly range test.
example : classify ⟨7, Junk, 5⟩ variableSlot 1 false 0 0 = 1 := by decide +kernel
example : classify ⟨7, FunctionCallReturnLabel, 5⟩ variableSlot 1 false 0 0 = 1 :=
  by decide +kernel

-- The assembly contract excludes an absent destination, before any target read.
example (c : Unit.CG) (s : MachineData) (hn : c.h.p.n.toNat ≤ MAX_N)
    (hd : Flat.get c.h.M.dest (rcx s) = Flat.NONE) : ¬ Unit.classifyA c s := by
  intro ha
  have hi := ha.2
  rw [hd] at hi
  have hnone : Flat.NONE.toNat = 18446744073709551615 := rfl
  rw [hnone] at hi
  unfold MAX_N at hn
  omega
