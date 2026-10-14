import Shuffler.Contracts
import Shuffler.Mapping
import Shuffler.Stack

namespace Shuffler.BuildMapping

variable {source target : Stack}

-- Whether the mapping builder leaves wildcard slots alone or takes them.
inductive WildcardSlotsStrategy : Type where
  | Leave
  | Take
  deriving DecidableEq, Repr

inductive CopyLocation : Type where
  | OutsideWildcardSlots
  | InWildcardSlots
  deriving DecidableEq, Repr

-- source and target never change while the mapping is built, so they are parameters.
structure MappingBuilder (source target : Stack) where
  dropped : List (Fin (2 ^ 8))
  hdropped : dropped.length = source.length
  mapping : Mapping source.length target.length
  sawWildcardCopy : Bool := false


------------------------------------ helpers (methods in the C++ shuffler code) ------------------------------------

namespace MappingBuilder

-- decides whether a target slot is a wildcard slot
def isWildcardTarget (_self : MappingBuilder source target) (targetOffset : Fin target.length) : Prop :=
  target[targetOffset].is_junk

instance (self : MappingBuilder source target) (targetOffset : Fin target.length) :
    Decidable (self.isWildcardTarget targetOffset) := by
  unfold isWildcardTarget; infer_instance

-- decides whether a source slot is in a wildcard slot
def inWildcardSlot (self : MappingBuilder source target) (sourceOffset : Fin source.length) : Prop :=
  ∃ h : sourceOffset.val < target.length, self.isWildcardTarget ⟨sourceOffset.val, h⟩

instance (self : MappingBuilder source target) (sourceOffset : Fin source.length) :
    Decidable (self.inWildcardSlot sourceOffset) := by
  unfold inWildcardSlot; infer_instance

-- returns the absolute difference between two offsets
def absDiff (_self : MappingBuilder source target) (sourceOffset : Fin source.length)
    (targetOffset : Fin target.length) : ℕ :=
  if sourceOffset.val > targetOffset.val then sourceOffset.val - targetOffset.val
  else targetOffset.val - sourceOffset.val

-- decides whether a source slot can be mapped to sth, ie. it is not dropped and not already mapped
def mappable (self : MappingBuilder source target) (sourceOffset : Fin source.length) : Prop :=
  self.dropped[sourceOffset.val]'(by rw [self.hdropped]; exact sourceOffset.isLt) = 0 ∧
    self.mapping sourceOffset = none

instance (self : MappingBuilder source target) (sourceOffset : Fin source.length) :
    Decidable (self.mappable sourceOffset) := by
  unfold mappable; infer_instance

-- decides whether a target slot is already assigned to a source slot
def hasSourceAssigned (self : MappingBuilder source target) (targetOffset : Fin target.length) : Prop :=
  (self.mapping.symm targetOffset).isSome

instance (self : MappingBuilder source target) (targetOffset : Fin target.length) :
    Decidable (self.hasSourceAssigned targetOffset) := by
  unfold hasSourceAssigned; infer_instance

-- returns the mappable source slot closest to targetOffset (that is in a wildcardslot location), if any; on ties the shallower one wins
def closestCopy (self : MappingBuilder source target) (targetOffset : Fin target.length)
    (location : CopyLocation) : Option (Fin source.length) :=
  (List.finRange source.length).foldl
    (fun best i =>
      if source[i] = target[targetOffset] ∧ self.mappable i ∧
          (self.inWildcardSlot i ↔ location = .InWildcardSlots) then
        match best with
        | none => some i
        | some b => if self.absDiff i targetOffset ≤ self.absDiff b targetOffset then some i else best
      else best
    ) none

-- helper, in C++ code in lines 192-199 of shuffler.cpp
-- The mappable source slot closest to targetOffset; on ties the deeper one wins.
def closestSurplus (self : MappingBuilder source target) (targetOffset : Fin target.length) :
    Option (Fin source.length) :=
  (List.finRange source.length).foldl
    (fun best o =>
      if self.mappable o then
        match best with
        | none => some o
        | some b => if self.absDiff o targetOffset < self.absDiff b targetOffset then some o else best
      else best
    ) none

-- binds a source slot to a target slot, returning a new mapping builder with the updated mapping
def map (self : MappingBuilder source target) (sourceOffset : Fin source.length)
    (targetOffset : Fin target.length) : Except Error (MappingBuilder source target) := do
  let ⟨hs⟩ ← requires (self.mappable sourceOffset) "source slot is dropped or already mapped"
  let ⟨ht⟩ ← requires (self.mapping.symm targetOffset = none) "target slot already has a source"
  return { self with mapping := self.mapping.bind sourceOffset targetOffset hs.2 ht }

end MappingBuilder


------------------------ buildMapping (in the constructor in shuffler.cpp) ----------------------------------

-- Each loop in the C++ constructor is one pass here: a foldlM over the offsets that threads the builder.

-- slots already in place get mapped directly
def mapInPlace (mb : MappingBuilder source target) : Except Error (MappingBuilder source target) :=
  (List.finRange (min source.length target.length)).foldlM (fun mb j => do
    let s := Fin.castLE (min_le_left _ _) j
    let t := Fin.castLE (min_le_right _ _) j
    if source[s] = target[t] ∧ mb.mappable s then mb.map s t else return mb
  ) mb

-- the remaining target offsets take the closest unused copy, deepest first: what is left over is
-- generated on top, where that is cheapest
def mapCopies (mb : MappingBuilder source target) : Except Error (MappingBuilder source target) :=
  (List.finRange target.length).foldlM (fun mb t => do
    if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then return mb
    match mb.closestCopy t .OutsideWildcardSlots with
    | some copy => mb.map copy t
    | none => return mb
  ) mb

-- copies sitting in wildcard slots are taken or left according to the strategy
def mapWildcardCopies (strategy : WildcardSlotsStrategy) (mb : MappingBuilder source target) :
    Except Error (MappingBuilder source target) :=
  (List.finRange target.length).foldlM (fun mb t => do
    if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then return mb
    match mb.closestCopy t .InWildcardSlots with
    | some copy =>
      -- a function return label is always taken, can't be duped or pushed;
      if target[t].isFunctionReturnLabel then mb.map copy t
      else if strategy = .Take then return { ← mb.map copy t with sawWildcardCopy := true }
      else return { mb with sawWildcardCopy := true }
    | none => return mb
  ) mb

-- wildcards keep whatever sits there
def keepWildcards (mb : MappingBuilder source target) : Except Error (MappingBuilder source target) :=
  (List.finRange (min source.length target.length)).foldlM (fun mb j => do
    let s := Fin.castLE (min_le_left _ _) j
    let t := Fin.castLE (min_le_right _ _) j
    if mb.isWildcardTarget t ∧ ¬ mb.hasSourceAssigned t ∧ mb.mappable s then mb.map s t
    else return mb
  ) mb

-- the remaining wildcards absorb the closest surplus slot instead of having it popped
def absorbSurplus (mb : MappingBuilder source target) : Except Error (MappingBuilder source target) :=
  (List.finRange target.length).foldlM (fun mb t => do
    if mb.hasSourceAssigned t ∨ ¬ mb.isWildcardTarget t then return mb
    match mb.closestSurplus t with
    | some best => mb.map best t
    | none => return mb
  ) mb

def buildMapping (source target : Stack) (dropped : List (Fin (2 ^ 8)))
    (strategy : WildcardSlotsStrategy) : Except Error (MappingBuilder source target) := do
  let ⟨hsizes⟩ ← requires (dropped.length = source.length) "dropped needs one entry per source slot"
  let mb ← mapInPlace { dropped, hdropped := hsizes, mapping := ⊥ }
  let mb ← mapCopies mb
  let mb ← mapWildcardCopies strategy mb
  let mb ← keepWildcards mb
  absorbSurplus mb

end Shuffler.BuildMapping
