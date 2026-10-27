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

abbrev Byte := Fin (2 ^ 8)

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
    (h : n ≤ source.length := by omega) : Except Error Bool := do
  let sourceOffset := sourceOffset.castLE h
  let ⟨_⟩ ← requires (sourceOffset.val < self.dropped.length) "dropped has no entry for the source slot"
  return decide (self.dropped[sourceOffset.val] = 0 ∧ self.mapping sourceOffset = none)

  -- decides whether a target slot is already assigned to a source slot
def hasSourceAssigned (self : MappingBuilder source target) (targetOffset : Fin target.length) : Bool :=
  (self.mapping.symm targetOffset).isSome

-- decides whether a target slot is a wildcard slot
def isWildcardTarget (_self : MappingBuilder source target) (targetOffset : Fin target.length) : Bool :=
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
    (location : CopyLocation) : Except Error (Option (Fin source.length)) := do
  let mut best : Option (Fin source.length) := none
  for i in List.finRange source.length do
    if source[i] = target[targetOffset] ∧ (← self.mappable i) ∧
        (self.inWildcardSlot i ↔ location = .InWildcardSlots) then
      match best with
      | none => best := some i
      | some b => if self.absDiff i targetOffset ≤ self.absDiff b targetOffset then best := some i
  return best

-- helper, in C++ code of shuffler.cpp in the `MappingBuilder` constructor: loop
-- "the remaining wildcards absorb the closest surplus slot instead of having it popped"
-- The mappable source slot closest to targetOffset; on ties the deeper one wins.
def closestSurplus (self : MappingBuilder source target) (targetOffset : Fin target.length) :
    Except Error (Option (Fin source.length)) := do
  let mut best : Option (Fin source.length) := none
  for o in List.finRange source.length do
    if ← self.mappable o then
      match best with
      | none => best := some o
      | some b => if self.absDiff o targetOffset < self.absDiff b targetOffset then best := some o
  return best

-- binds a source slot to a target slot, returning a new mapping builder with the updated mapping
def map (self : MappingBuilder source target) {n m : ℕ} (sourceOffset : Fin n)
    (targetOffset : Fin m) (hs : n ≤ source.length := by omega)
    (ht : m ≤ target.length := by omega) : Except Error (MappingBuilder source target) := do
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
    (strategy : WildcardSlotsStrategy) : Except Error (BuildMappingResult source target) := do
  _ ← requires (dropped.length = source.length) "dropped needs one entry per source slot"
  let mut mb : MappingBuilder source target := { dropped, mapping := ⊥ }

  -- slots already in place get mapped directly
  for j in List.finRange (min source.length target.length) do
    let s := Fin.castLE (min_le_left _ _) j
    let t := Fin.castLE (min_le_right _ _) j
    if source[s] = target[t] ∧ (← mb.mappable s) then
      mb ← mb.map s t

  -- the remaining target offsets take the closest unused copy, deepest first: what is left over is
  -- generated on top, where that is cheapest
  for t in List.finRange target.length do
    if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then continue
    match ← mb.closestCopy t .OutsideWildcardSlots with
    | some copy => mb ← mb.map copy t
    | none => pure ()

  -- copies sitting in wildcard slots are taken or left according to the strategy
  for t in List.finRange target.length do
    if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then continue
    match ← mb.closestCopy t .InWildcardSlots with
    | some copy =>
      -- a function return label is always taken, can't be duped or pushed;
      if target[t].isFunctionReturnLabel then
        mb ← mb.map copy t
      else
        if strategy = .Take then
          mb ← mb.map copy t
        mb := { mb with sawWildcardCopy := true }
    | none => pure ()

  -- wildcards keep whatever sits there
  for j in List.finRange (min source.length target.length) do
    let s := Fin.castLE (min_le_left _ _) j
    let t := Fin.castLE (min_le_right _ _) j
    if mb.isWildcardTarget t ∧ ¬ mb.hasSourceAssigned t ∧ (← mb.mappable s) then
      mb ← mb.map s t

  -- the remaining wildcards absorb the closest surplus slot instead of having it popped
  for t in List.finRange target.length do
    if mb.hasSourceAssigned t ∨ ¬ mb.isWildcardTarget t then continue
    match ← mb.closestSurplus t with
    | some best => mb ← mb.map best t
    | none => pure ()

  return { mapping := mb.mapping, sawWildcardCopy := mb.sawWildcardCopy }

def buildMapping_new (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) : Except Error (BuildMappingResult source target) := do
  let mut mb : MappingBuilder source target := { dropped, mapping := ⊥ }

  _ ← requires (dropped.length = source.length) "dropped needs one entry per source slot"

  let common := min source.length target.length

  -- slots already in place get mapped directly
  for j in List.finRange common do
    if source[j] = target[j] ∧ (← mb.mappable j) then
      mb ← mb.map j j

  -- the remaining target offsets take the closest unused copy, deepest first: what is left over is
  -- generated on top, where that is cheapest
  for t in List.finRange target.length do
    if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then continue
    match ← mb.closestCopy t .OutsideWildcardSlots with
    | some copy => mb ← mb.map copy t
    | none => pure ()

  -- copies sitting in wildcard slots are taken or left according to the strategy
  for t in List.finRange target.length do
    if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then continue
    match ← mb.closestCopy t .InWildcardSlots with
    | some copy =>
      -- a function return label is always taken, can't be duped or pushed;
      if target[t].isFunctionReturnLabel then
        mb ← mb.map copy t
      else
        if strategy = .Take then
          mb ← mb.map copy t
        mb := { mb with sawWildcardCopy := true }
    | none => pure ()

  -- wildcards keep whatever sits there
  for j in List.finRange (min source.length target.length) do
    let s := Fin.castLE (min_le_left _ _) j
    let t := Fin.castLE (min_le_right _ _) j
    if mb.isWildcardTarget t ∧ ¬ mb.hasSourceAssigned t ∧ (← mb.mappable s) then
      mb ← mb.map s t

  -- the remaining wildcards absorb the closest surplus slot instead of having it popped
  for t in List.finRange target.length do
    if mb.hasSourceAssigned t ∨ ¬ mb.isWildcardTarget t then continue
    match ← mb.closestSurplus t with
    | some best => mb ← mb.map best t
    | none => pure ()

  return { mapping := mb.mapping, sawWildcardCopy := mb.sawWildcardCopy }

end Shuffler.BuildMapping
