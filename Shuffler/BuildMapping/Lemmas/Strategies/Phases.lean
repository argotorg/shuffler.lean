import Shuffler.BuildMapping.Lemmas.Basic

namespace Shuffler.BuildMapping.Strategies

variable {source target : Stack}

-- These phases expose the loop states used to compare the two strategies.
-- `buildMapping_eq_phases` connects them to the production function.
def initialPasses (source target : Stack) (dropped : List Byte) :
    Except Error (MappingBuilder source target) := do
  let mut mb : MappingBuilder source target := { dropped, mapping := ⊥ }
  for j in List.finRange (min source.length target.length) do
    let s := Fin.castLE (min_le_left _ _) j
    let t := Fin.castLE (min_le_right _ _) j
    if source[s] = target[t] ∧ (← mb.mappable s) then
      mb ← mb.map s t
  for t in List.finRange target.length do
    if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then continue
    match ← mb.closestCopy t .OutsideWildcardSlots with
    | some copy => mb ← mb.map copy t
    | none => pure ()
  return mb

def copyStep (strategy : WildcardSlotsStrategy) (t : Fin target.length)
    (initial : MappingBuilder source target) : Except Error (ForInStep (MappingBuilder source target)) := do
  let mut mb := initial
  if mb.hasSourceAssigned t ∨ mb.isWildcardTarget t then return .yield mb
  match ← mb.closestCopy t .InWildcardSlots with
  | some copy =>
    if target[t].isFunctionReturnLabel then
      mb ← mb.map copy t
    else
      if strategy = .Take then
        mb ← mb.map copy t
      mb := { mb with sawWildcardCopy := true }
  | none => pure ()
  return .yield mb

def copyPass (strategy : WildcardSlotsStrategy) (mb : MappingBuilder source target) :
    Except Error (MappingBuilder source target) :=
  forIn (List.finRange target.length) mb (copyStep strategy)

def keepStep (j : Fin (min source.length target.length)) (initial : MappingBuilder source target) :
    Except Error (ForInStep (MappingBuilder source target)) := do
  let mut mb := initial
  let s := Fin.castLE (min_le_left _ _) j
  let t := Fin.castLE (min_le_right _ _) j
  if mb.isWildcardTarget t ∧ ¬ mb.hasSourceAssigned t ∧ (← mb.mappable s) then
    mb ← mb.map s t
  return .yield mb

def surplusStep (t : Fin target.length) (initial : MappingBuilder source target) :
    Except Error (ForInStep (MappingBuilder source target)) := do
  let mut mb := initial
  if mb.hasSourceAssigned t ∨ ¬ mb.isWildcardTarget t then return .yield mb
  match ← mb.closestSurplus t with
  | some best => mb ← mb.map best t
  | none => pure ()
  return .yield mb

def suffix (mb : MappingBuilder source target) : Except Error (MappingBuilder source target) := do
  let mb ← forIn (List.finRange (min source.length target.length)) mb keepStep
  forIn (List.finRange target.length) mb surplusStep

end Shuffler.BuildMapping.Strategies
