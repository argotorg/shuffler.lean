import Shuffler.BuildMapping.Defs

namespace Shuffler.BuildMapping.MappingBuilder

variable {source target : Stack}

-- Search model for the final loop; on ties the first candidate remains.
def closestSurplus (self : MappingBuilder source target) (targetOffset : Fin target.length) :
    Except Error (Option (Fin source.length)) := do
  let mut best : Option (Fin source.length) := none
  for o in List.finRange source.length do
    if ← self.mappable o then
      match best with
      | none => best := some o
      | some b => if self.absDiff o targetOffset < self.absDiff b targetOffset then best := some o
  return best

end Shuffler.BuildMapping.MappingBuilder

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

-- Setting the flag before `map` gives the same result, including errors, as setting it after.
private theorem map_set_sawWildcardCopy (mb : MappingBuilder source target)
    (s : Fin source.length) (t : Fin target.length) :
    ({ mb with sawWildcardCopy := true } : MappingBuilder source target).map s t =
      (do
        let next ← mb.map s t
        pure { next with sawWildcardCopy := true }) := by
  simp only [MappingBuilder.map, bind_assoc, pure_bind]
  rfl

private theorem surplus_search_eq (mb : MappingBuilder source target) (j : Fin target.length) :
    (do
      let mut best : Option (Fin source.length) := none
      for o in List.finRange source.length do
        if (← mb.mappable o) ∧
            (¬ best.isSome ∨ best.any (λ b => mb.absDiff o j < mb.absDiff b j)) then
          best := some o
      return best) = mb.closestSurplus j := by
  simp only [MappingBuilder.closestSurplus, bind_pure]
  congr 1
  funext o best
  congr 1
  funext mappable
  cases mappable <;> cases best <;> simp

-- The phase definitions give the same computation as buildMapping.
theorem buildMapping_eq_phases (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) :
    buildMapping source target dropped strategy = (do
      _ ← requires (dropped.length = source.length) "dropped needs one entry per source slot"
      let mb ← initialPasses source target dropped
      let mb ← copyPass strategy mb
      let mb ← suffix mb
      pure { mapping := mb.mapping, sawWildcardCopy := mb.sawWildcardCopy }) := by
  unfold initialPasses copyPass suffix copyStep keepStep surplusStep
  simp only [buildMapping, ← not_or, ite_not,
    map_set_sawWildcardCopy, bind_assoc, pure_bind]
  congr 1
  funext _
  congr 1
  funext mb
  congr 1
  · -- Compare the second loop for both guard outcomes and both search results.
    congr 1
    funext j mb
    by_cases h : mb.hasSourceAssigned j ∨ mb.isWildcardTarget j
    · simp only [h, ite_true]
    · simp only [h, ite_false]
      congr 1
      funext copy
      cases copy <;> rfl
  · -- Compare the third loop after moving the flag update past `map`.
    funext mb
    congr 1
    · congr 1
      funext j mb
      by_cases h : mb.hasSourceAssigned j ∨ mb.isWildcardTarget j
      · simp only [h, ite_true]
      · simp only [h, ite_false]
        congr 1
        funext copy
        cases copy <;> rfl
    · funext mb
      congr 1
      funext mb
      -- The fourth loop is definitionally equal; compare the final loop.
      congr 1
      congr 1
      funext j mb
      by_cases hwild : mb.isWildcardTarget j <;>
        by_cases hassigned : mb.hasSourceAssigned j <;>
          simp [hwild, hassigned]
      have hsearch := surplus_search_eq mb j
      simp at hsearch
      rw [hsearch]
      congr 1
      funext best
      cases best <;> simp

end Shuffler.BuildMapping.Strategies
