import Shuffler.Stack
import Shuffler.Mapping

-- Whether the mapping builder leaves wildcard slots alone or takes them.
inductive WildcardSlotsStrategy : Type where
  | Leave
  | Take
  deriving DecidableEq, Repr

inductive CopyLocation : Type where
  | OutsideWildcardSlots
  | InWildcardSlots
  deriving DecidableEq, Repr

structure MappingBuilder where
  source : Stack
  target : Stack
  dropped : List (Fin (2 ^ 8))
  hdropped : dropped.length = source.length
  mapping : Mapping source.length target.length
  sawWildcardCopy : Bool := false

namespace MappingBuilder


------------------------------------ helpers (methods in the C++ shuffler code) ------------------------------------
-- decides whether a source slot can be mapped to sth, ie. it is not dropped and not already mapped
def mappable (self : MappingBuilder) (sourceOffset : Fin self.source.length) : Bool :=
  have : sourceOffset.val < self.dropped.length := by have := self.hdropped; omega
  self.dropped[sourceOffset] == 0 && (self.mapping sourceOffset).isNone

-- decides whether a target slot is already assigned to a source slot
def hasSourceAssigned (self : MappingBuilder) (targetOffset : Fin self.target.length) : Bool :=
 (self.mapping.symm targetOffset).isSome

-- decides whether a target slot is a wildcard slot
 def isWildcardTarget (self : MappingBuilder) (targetOffset : Fin self.target.length) : Bool :=
 self.target[targetOffset].is_junk

-- decides whether a source slot is in a wildcard slot
def inWildcardSlot (self : MappingBuilder) (sourceOffset : Fin self.source.length) : Bool :=
  if h:  sourceOffset.val < self.target.length then isWildcardTarget self (Fin.mk sourceOffset.val h) else false

-- returns the absolute difference between two offsets
def absDiff (self : MappingBuilder) (sourceOffset : Fin self.source.length) (targetOffset : Fin self.target.length) : Nat :=
  if sourceOffset.val > targetOffset.val then sourceOffset.val - targetOffset.val else targetOffset.val - sourceOffset.val

-- returns the mappable source slot closest to targetOffset (that is in a wildcardslot location), if any; on ties the shallower one wins
def closestCopy (self : MappingBuilder) (targetOffset : Fin self.target.length) (location : CopyLocation) : Option (Fin self.source.length) :=
  let inWildcardSlots := location == CopyLocation.InWildcardSlots
  (List.finRange self.source.length).foldl
    (fun best i =>
      ( if (self.source[i] == self.target[targetOffset] && (self.mappable i) && self.inWildcardSlot i == inWildcardSlots) then
        match best with
        | none => some i
        | some b => if absDiff self i targetOffset ≤ absDiff self b targetOffset then some i else best
      else best )
    ) none

-- binds a source slot to a target slot, returning a new mapping builder with the updated mapping
def map (self : MappingBuilder) (sourceOffset : Fin self.source.length) (targetOffset : Fin self.target.length) (h : self.mappable sourceOffset = true) (hfree : self.hasSourceAssigned targetOffset = false) : MappingBuilder :=
  { self with
    mapping := self.mapping.bind sourceOffset targetOffset
      (by simp [mappable] at h; exact h.2)
      (by simpa [hasSourceAssigned] using hfree)
  }


----------------------------------- helper, in C++ code in lines 192-199 of shuffler.cpp --------------------------------

-- The mappable source slot closest to targetOffset; on ties the deeper one wins.
def closestSurplus (self : MappingBuilder) (targetOffset : Fin self.target.length) : Option (Fin self.source.length) :=
  (List.finRange self.source.length).foldl
    (fun best o =>
      if self.mappable o then
        match best with
        | none => some o
        | some b => if absDiff self o targetOffset < absDiff self b targetOffset then some o else best
      else best
    ) none


---------------------------  theorems needed for buildMapping -------------------------------------
-- Every binding maps a source slot to the target slot with the same offset.
def Diagonal {a b : ℕ} (m : Mapping a b) : Prop :=
  ∀ s t, m s = some t → s.val = t.val

-- In a diagonal mapping, a target is free when the source at the same offset is unbound.
theorem diagonal_symm_eq_none {a b : ℕ} (m : Mapping a b) (hdiag : Diagonal m)
    (s : Fin a) (t : Fin b) (hst : s.val = t.val) (hs : m s = none) : m.symm t = none := by
  cases h : m.symm t with
  | none => rfl
  | some s' =>
    have hs't : m s' = some t := m.eq_some_iff.mp h
    have : s' = s := Fin.ext ((hdiag s' t hs't).trans hst.symm)
    subst this
    simp [hs] at hs't

-- Binding a slot to the target at the same offset keeps a mapping diagonal.
theorem diagonal_bind {a b : ℕ} (m : Mapping a b) (hdiag : Diagonal m)
    (s : Fin a) (t : Fin b) (hst : s.val = t.val) (hs : m s = none) (ht : m.symm t = none) :
    Diagonal (m.bind s t hs ht) := by
  intro i k h
  by_cases hi : i = s
  · subst hi
    simp at h
    subst h
    exact hst
  · rw [Mapping.bind_apply_of_ne m s t hs ht i hi] at h
    exact hdiag i k h

-- closestCopy only returns mappable copies.
theorem closestCopy_mappable (self : MappingBuilder) (targetOffset : Fin self.target.length)
    (location : CopyLocation) (copy : Fin self.source.length)
    (h : self.closestCopy targetOffset location = some copy) : self.mappable copy = true := by
  unfold closestCopy at h
  revert h
  generalize List.finRange self.source.length = l
  generalize hacc : (none : Option (Fin self.source.length)) = acc
  -- Invariant: the best copy found so far is mappable.
  have hinv : ∀ c, acc = some c → self.mappable c = true := by
    rintro c rfl
    cases hacc
  clear hacc
  induction l generalizing acc with
  | nil => exact hinv copy
  | cons i l ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    intro c hc
    split at hc
    · split at hc
      · simp_all
      · split at hc <;> simp_all
    · exact hinv c hc

-- closestSurplus only returns mappable slots.
theorem closestSurplus_mappable (self : MappingBuilder) (targetOffset : Fin self.target.length)
    (surplus : Fin self.source.length)
    (h : self.closestSurplus targetOffset = some surplus) : self.mappable surplus = true := by
  unfold closestSurplus at h
  revert h
  generalize List.finRange self.source.length = l
  generalize hacc : (none : Option (Fin self.source.length)) = acc
  -- Invariant: the best slot found so far is mappable.
  have hinv : ∀ c, acc = some c → self.mappable c = true := by
    rintro c rfl
    cases hacc
  clear hacc
  induction l generalizing acc with
  | nil => exact hinv surplus
  | cons i l ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    intro c hc
    split at hc
    · split at hc
      · simp_all
      · split at hc <;> simp_all
    · exact hinv c hc





------------------------ buildMapping (in the constructor in shuffler.cpp) ----------------------------------)

-- each loop in the C++ code corresponds to a foldl here, with the accumulator being the mapping so far
-- the third loop also carries a boolean indicating whether a copy in a wildcard slot was seen
-- at the end the created mapping is returned as part of a new mapping builder, which is returned
def buildMapping (_source : Stack) (_target : Stack) (_dropped : List (Fin (2 ^ 8)))
    (wildcard_slots_strategy : WildcardSlotsStrategy) (hsizes: _dropped.length =_source.length): MappingBuilder :=
    let initMappingBuilder : MappingBuilder := { source := _source, target := _target, dropped := _dropped, hdropped := hsizes, mapping := ⊥}
    let common := min _source.length _target.length
    -- slots already in place get mapped directly
    -- The accumulator carries the invariant that all bindings so far are diagonal (j ↦ j).
    let mapping1 := ((List.finRange common).foldl
      (fun (m : {m : Mapping _source.length _target.length // Diagonal m}) (j : Fin common) =>
        let mb := { initMappingBuilder with mapping := m.1 }
        let s : Fin _source.length := ⟨j.val, lt_of_lt_of_le j.isLt (min_le_left _ _)⟩
        let t : Fin _target.length := ⟨j.val, lt_of_lt_of_le j.isLt (min_le_right _ _)⟩
        if h : _source[s] = _target[t] ∧ mb.mappable s = true then
          have hs : m.1 s = none := by simp [mb, mappable] at h; exact h.2.2
          -- Target j is free: only source j could hold it, and source j is unbound.
          have ht : m.1.symm t = none := diagonal_symm_eq_none m.1 m.2 s t rfl hs
          ⟨(mb.map s t h.2 (by simp [mb, hasSourceAssigned, ht])).mapping,
            diagonal_bind m.1 m.2 s t rfl hs ht⟩
        else m
    ) ⟨⊥, by intro s t h; simp at h⟩).1
    -- the remaining target offsets take the closest unused copy, deepest first: what is left over is
    -- generated on top, where that is cheapest
    let mapping2 := (List.finRange _target.length).foldl
      (fun (m : Mapping _source.length _target.length) (t : Fin _target.length) =>
        let mb := { initMappingBuilder with mapping := m }
        if hfree : mb.hasSourceAssigned t = false ∧ mb.isWildcardTarget t = false then
          match hcopy : mb.closestCopy t .OutsideWildcardSlots with
          | some copy =>
            (mb.map copy t (closestCopy_mappable mb t _ copy hcopy) hfree.1).mapping
          | none => m
        else m
    ) mapping1
    -- copies sitting in wildcard slots are taken or left according to the strategy
    -- The accumulator pairs the mapping with whether a copy in a wildcard slot was seen.
    let (mapping3, _sawWildcardCopy) := (List.finRange _target.length).foldl
      (fun (acc : Mapping _source.length _target.length × Bool) (t : Fin _target.length) =>
        let mb := { initMappingBuilder with mapping := acc.1, sawWildcardCopy := acc.2 }
        if hfree : mb.hasSourceAssigned t = false ∧ mb.isWildcardTarget t = false then
          match hcopy : mb.closestCopy t .InWildcardSlots with
          | some copy =>
            let taken := (mb.map copy t (closestCopy_mappable mb t _ copy hcopy) hfree.1).mapping
            -- a function return label is always taken, can't be duped or pushed;
            if _target[t].isFunctionReturnLabel then
              (taken, acc.2)
            else if wildcard_slots_strategy == .Take then
              (taken, true)
            else (acc.1, true)
          | none => acc
        else acc
    ) (mapping2, initMappingBuilder.sawWildcardCopy)
    let constrMappingBuilder : MappingBuilder :=
      { initMappingBuilder with mapping := mapping3, sawWildcardCopy := _sawWildcardCopy }
    -- wildcards keep whatever sits there
    let mapping4 :=  (List.finRange common).foldl
      (fun (m : Mapping _source.length _target.length) (j : Fin common) =>
        let mb := { initMappingBuilder with mapping := m }
        let s : Fin _source.length := ⟨j.val, lt_of_lt_of_le j.isLt (min_le_left _ _)⟩
        let t : Fin _target.length := ⟨j.val, lt_of_lt_of_le j.isLt (min_le_right _ _)⟩
        if h : mb.isWildcardTarget t = true ∧ mb.hasSourceAssigned t = false ∧ mb.mappable s = true then
          (mb.map s t h.2.2 h.2.1).mapping
        else m
    ) constrMappingBuilder.mapping
    -- the remaining wildcards absorb the closest surplus slot instead of having it popped
    let mapping5 := (List.finRange _target.length).foldl
      (fun (m : Mapping _source.length _target.length) (t : Fin _target.length) =>
        let mb := { initMappingBuilder with mapping := m }
        if hfree : mb.hasSourceAssigned t = false ∧ mb.isWildcardTarget t = true then
          match hbest : mb.closestSurplus t with
          | some best =>
            (mb.map best t (closestSurplus_mappable mb t best hbest) hfree.1).mapping
          | none => m
        else m
    ) mapping4
    { constrMappingBuilder with mapping := mapping5 }


end MappingBuilder
