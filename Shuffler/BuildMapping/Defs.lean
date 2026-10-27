module

public import Shuffler.Contracts
public import Shuffler.Mapping
public import Shuffler.Stack

@[expose] public section

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
  dropped : List Byte
  mapping : Mapping source.length target.length
  sawWildcardCopy : Bool := false

structure BuildMappingResult (source target : Stack) where
  mapping : Mapping source.length target.length
  sawWildcardCopy : Bool


------------------------------------ helpers (methods in the C++ shuffler code) ------------------------------------

namespace MappingBuilder

-- decides whether a source slot can be mapped to sth, ie. it is not dropped and not already mapped
def mappable (self : MappingBuilder source target) {n : ℕ} (sourceOffset : Fin n)
    (h : n ≤ source.length := by omega) : Except ShuffleErr Bool := do
  let sourceOffset := sourceOffset.castLE h
  let ⟨_⟩ ← requires (sourceOffset.val < self.dropped.length) "dropped has no entry for the source slot"
  return decide (self.dropped[sourceOffset.val] = 0 ∧ self.mapping sourceOffset = none)

  -- decides whether a target slot is already assigned to a source slot
def hasSourceAssigned (self : MappingBuilder source target) {n : ℕ} (targetOffset : Fin n)
    (h : n ≤ target.length := by omega) : Bool :=
  let targetOffset := targetOffset.castLE h
  (self.mapping.symm targetOffset).isSome

-- decides whether a target slot is a wildcard slot
def isWildcardTarget (_self : MappingBuilder source target) {n : ℕ} (targetOffset : Fin n)
    (h : n ≤ target.length := by omega) : Bool :=
  target[targetOffset].is_junk

-- decides whether a source slot is in a wildcard slot
def inWildcardSlot (self : MappingBuilder source target) (sourceOffset : Fin source.length) : Bool :=
  if h : sourceOffset.val < target.length then self.isWildcardTarget ⟨sourceOffset.val, h⟩ else false

-- returns the absolute difference between two offsets
def absDiff (_self : MappingBuilder source target) (sourceOffset : Fin source.length)
    (targetOffset : Fin target.length) : ℕ :=
  if sourceOffset.val > targetOffset.val then sourceOffset.val - targetOffset.val
  else targetOffset.val - sourceOffset.val

-- returns the mappable source slot closest to targetOffset (that is in a wildcardslot location), if any; on ties the shallower one wins
def closestCopy (self : MappingBuilder source target) (targetOffset : Fin target.length)
    (location : CopyLocation) : Except ShuffleErr (Option (Fin source.length)) := do
  let inWildcardSlots : Bool := location = .InWildcardSlots
  let mut best : Option (Fin source.length) := none
  for i in List.finRange source.length do
    if source[i] = target[targetOffset] ∧ (← self.mappable i) ∧ self.inWildcardSlot i = inWildcardSlots then
      if ¬ best.isSome ∨ best.any (λ b => self.absDiff i targetOffset ≤ self.absDiff b targetOffset) then
        best := some i
  return best

-- binds a source slot to a target slot, returning a new mapping builder with the updated mapping
def map (self : MappingBuilder source target) {n m : ℕ} (sourceOffset : Fin n)
    (targetOffset : Fin m) (hs : n ≤ source.length := by omega)
    (ht : m ≤ target.length := by omega) : Except ShuffleErr (MappingBuilder source target) := do
  let sourceOffset := sourceOffset.castLE hs
  let targetOffset := targetOffset.castLE ht
  _ ← requires (← self.mappable sourceOffset) "source slot is not mappable"
  -- hp, hd needed for bind
  let ⟨hp⟩ ← requires (self.mapping sourceOffset = none) "source position already bound"
  let ⟨hd⟩ ← requires (self.mapping.symm targetOffset = none) "target position already bound"
  return { self with mapping := self.mapping.bind sourceOffset targetOffset hp hd }

end MappingBuilder


------------------------ buildMapping (in the constructor in shuffler.cpp) ----------------------------------

def buildMapping (source target : Stack) (dropped : List Byte)
    (wildcardSlotStrategy : WildcardSlotsStrategy) : Except ShuffleErr (BuildMappingResult source target) := do
  let mut mb : MappingBuilder source target := { dropped, mapping := ⊥ }

  _ ← requires (dropped.length = source.length) "dropped needs one entry per source slot"

  let common := min source.length target.length

  -- slots already in place get mapped directly
  for j in List.finRange common do
    if source[j] = target[j] ∧ (← mb.mappable j) then
      mb ← mb.map j j

  -- the remaining target offsets take the closest unused copy, deepest first: what is left over is
  -- generated on top, where that is cheapest
  for j in List.finRange target.length do
    if ¬ mb.hasSourceAssigned j ∧ ¬ mb.isWildcardTarget j then
      if let some copy ← mb.closestCopy j .OutsideWildcardSlots then
        mb ← mb.map copy j

  -- copies sitting in wildcard slots are taken or left according to the strategy
  for j in List.finRange target.length do
    if ¬ mb.hasSourceAssigned j ∧ ¬ mb.isWildcardTarget j then
      if let some copy ← mb.closestCopy j .InWildcardSlots then
        -- a function return label is always taken, can't be duped or pushed
        if target[j].isFunctionReturnLabel then
          mb ← mb.map copy j
        else
          mb := { mb with sawWildcardCopy := true }
          if wildcardSlotStrategy = .Take then
            mb ← mb.map copy j

  -- wildcards keep whatever sits there
  for j in List.finRange common do
    if mb.isWildcardTarget j ∧ ¬ mb.hasSourceAssigned j ∧ (← mb.mappable j) then
      mb ← mb.map j j

  -- the remaining wildcards absorb the closest surplus slot instead of having it popped
  for j in List.finRange target.length do
    if mb.isWildcardTarget j ∧ ¬ mb.hasSourceAssigned j then
      let mut best : Option (Fin source.length) := none
      for o in List.finRange source.length do
        if (← mb.mappable o) ∧ (¬ best.isSome ∨ best.any (λ b => mb.absDiff o j < mb.absDiff b j)) then
          best := some o
      if h : best.isSome then
        mb ← mb.map (best.get h) j

  return { mapping := mb.mapping, sawWildcardCopy := mb.sawWildcardCopy }

end Shuffler.BuildMapping
