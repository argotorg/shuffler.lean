import BbuKraken.Unit.Plan.IsDemanded

/-! The branch results used by the assembly proof of `Planner::classify`. -/

namespace Bbu.Unit.ClassifyU

-- These are the values that `classify` reads. The payload selects `spilled`.
structure Inputs where
  slot : StackSlot
  spilled : BitVec 8
  targetJunk : Bool
  other : Bool
  demanded : Bool
  allowed : Bool

def Inputs.free (x : Inputs) : Bool := canBeFreelyGenerated x.slot
def Inputs.spill (x : Inputs) : Bool := Flat.isVariable x.slot && x.spilled != 0

def Inputs.rank (x : Inputs) : BitVec 8 :=
  if x.free then 1
  else if x.spill then 2
  else if x.other then 3
  else if x.allowed && Flat.isVariable x.slot then Flat.SPILL
  else Flat.NOCLASS

def Inputs.eval (x : Inputs) : BitVec 8 :=
  if x.slot.kind = FunctionReturnLabel then Flat.NOCLASS
  else if x.targetJunk &&
      (isJunk x.slot || x.free || x.spill || x.other || !x.demanded) then 0
  else x.rank

def inputs (p : Flat.Planner) (sp : BitVec 32 → BitVec 8) (M : Flat.Mapping)
    (dn : Vector (BitVec 8) MAX_N) (off : Word) : Inputs :=
  let slot := Flat.get p.source off
  ⟨slot, sp slot.payload, isJunk (Flat.get p.target (Flat.get M.dest off)),
    Flat.hasOtherRetainedCopy p M dn off, Flat.isDemanded p slot, p.allowed⟩

theorem eval_eq_classify (p : Flat.Planner) (sp : BitVec 32 → BitVec 8) (M : Flat.Mapping)
    (dn : Vector (BitVec 8) MAX_N) (off : Word) :
    (inputs p sp M dn off).eval = Flat.classify p sp M dn off := by
  simp only [inputs, Inputs.eval, Inputs.rank, Inputs.free, Inputs.spill,
    Flat.classify, Flat.spillIsSpilled]
  congr 1

-- The result after the target test on a slot that can be generated again.
def Inputs.generated (x : Inputs) : BitVec 8 := if x.targetJunk then 0 else x.rank

-- The result after the target test when the slot is neither free nor spilled.
def Inputs.copied (x : Inputs) : BitVec 8 :=
  if x.other || !x.demanded then 0 else x.rank

theorem eval_return (x : Inputs) (h : x.slot.kind = FunctionReturnLabel) :
    x.eval = Flat.NOCLASS := by simp [Inputs.eval, h]

theorem eval_generated (x : Inputs) (h : x.slot.kind ≠ FunctionReturnLabel)
    (hg : (isJunk x.slot || x.free || x.spill) = true) : x.eval = x.generated := by
  simp only [Inputs.eval, h, ↓reduceIte, Inputs.generated]
  have he : (isJunk x.slot || x.free || x.spill || x.other || !x.demanded) = true := by
    rw [hg]
    rfl
  rw [he]
  simp

theorem eval_plain (x : Inputs) (h : x.slot.kind ≠ FunctionReturnLabel)
    (ht : x.targetJunk = false) : x.eval = x.rank := by
  simp [Inputs.eval, h, ht]

theorem eval_copied (x : Inputs) (h : x.slot.kind ≠ FunctionReturnLabel)
    (ht : x.targetJunk = true) (hj : isJunk x.slot = false)
    (hf : x.free = false) (hs : x.spill = false) : x.eval = x.copied := by
  simp [Inputs.eval, Inputs.copied, h, ht, hj, hf, hs]

theorem rank_free (x : Inputs) (h : x.free = true) : x.rank = 1 := by
  simp [Inputs.rank, h]

theorem rank_spill (x : Inputs) (hf : x.free = false) (hs : x.spill = true) :
    x.rank = 2 := by simp [Inputs.rank, hf, hs]

theorem rank_other (x : Inputs) (hf : x.free = false) (hs : x.spill = false) :
    x.rank = if x.other then 3 else
      if x.allowed && Flat.isVariable x.slot then Flat.SPILL else Flat.NOCLASS := by
  simp [Inputs.rank, hf, hs]

theorem copied_other (x : Inputs) (h : x.other = true) : x.copied = 0 := by
  simp [Inputs.copied, h]

theorem copied_undemanded (x : Inputs) (h : x.demanded = false) : x.copied = 0 := by
  simp [Inputs.copied, h]

theorem copied_demanded (x : Inputs) (ho : x.other = false) (hd : x.demanded = true) :
    x.copied = x.rank := by simp [Inputs.copied, ho, hd]

end Bbu.Unit.ClassifyU
