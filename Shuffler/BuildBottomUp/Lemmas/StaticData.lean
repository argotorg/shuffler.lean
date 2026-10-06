import Shuffler.BuildBottomUp.Lemmas.NecessityProofs
import Mathlib.Data.Finset.Sort

namespace Shuffler.BuildBottomUp

namespace Static

-- These data are computed once from the initial state.
def holes (initial : State source target spills) : Finset (Fin target.length) :=
  Finset.univ.filter (fun j => initial.mapping.symm j = none)

def holeList (initial : State source target spills) : List (Fin target.length) :=
  (holes initial).sort

def boundList (initial : State source target spills) : List (Fin target.length) :=
  (Finset.univ.filter (fun j => (initial.mapping.symm j).isSome)).sort

def augmentedStack (initial : State source target spills) : Stack :=
  initial.stack ++ (holeList initial).map (fun j => target[j])

def generatedBefore (initial : State source target spills) (cursor : Nat) : Nat :=
  ((holes initial).filter (fun j => j.val < cursor)).card

def prefixLength (initial : State source target spills) (cursor : Nat) : Nat :=
  initial.stack.length + generatedBefore initial cursor

def copyPositions (initial : State source target spills) (cursor : Nat) (value : Value) : Finset Nat :=
  (Finset.range (prefixLength initial cursor)).filter fun i =>
    prefixLength initial cursor ≤ i + (MAX_DUP_DEPTH + 1) ∧
      (augmentedStack initial)[i]? = some value

def copies (initial : State source target spills) (cursor : Nat) (value : Value) : Nat :=
  (copyPositions initial cursor value).card

def NeedsCopy (initial : State source target spills) (cursor : Nat) (value : Value) : Prop :=
  ¬value.can_be_freely_generated ∧ ¬spills.is_spilled value ∧
    ∃ j ∈ holes initial, cursor ≤ j.val ∧ target[j] = value

def Ready (initial : State source target spills) (cursor : Nat) : Prop :=
  ∀ j ∈ holes initial, cursor ≤ j.val →
    target[j].can_be_freely_generated ∨ spills.is_spilled target[j] ∨
      0 < copies initial cursor target[j]

-- Original source coordinates use the original assignment. The added coordinates
-- use the initially unassigned destinations, in increasing order.
def completedNext (initial : State source target spills) (i : Nat) : Nat :=
  if hi : i < initial.stack.length then
    ((initial.mapping ⟨i, hi⟩).map Fin.val).getD i
  else ((holeList initial)[i - initial.stack.length]?.map Fin.val).getD i

def CyclesReady (initial : State source target spills) (cursor : Nat) : Prop :=
  ∀ i, cursor ≤ i → i < target.length - (MAX_SWAP_DEPTH + 1) →
    ∀ k < target.length,
      (completedNext initial)^[k] i < cursor ∨ (completedNext initial)^[k] i = i

-- The bound destination that leaves seventeen slots is the (n - 16)-th one.
def boundary (initial : State source target spills) : Nat :=
  (((boundList initial)[initial.stack.length - (MAX_SWAP_DEPTH + 1)]?).map Fin.val).getD target.length

def generationEnd (initial : State source target spills) : Nat :=
  (holes initial).sup (fun j => j.val + 1)

def cutoff (initial : State source target spills) : Nat :=
  min (boundary initial) (generationEnd initial)

def BoundarySafe (initial : State source target spills) : Prop :=
  ∀ v, initial.expectedStack[boundary initial]? = some v →
    (augmentedStack initial)[boundary initial]? = some v ∨
      ¬NeedsCopy initial (boundary initial) v ∨ 2 ≤ copies initial (boundary initial) v

end Static

-- This predicate uses only initial values, initial assignments, finite counts,
-- and iterates of one fixed completed assignment. It does not call the builder.
def StaticSuccess (initial : State source target spills) : Prop :=
  if initial.stack.length ≤ MAX_DUP_DEPTH + 1 then Static.Ready initial 0
  else
    (∀ c < Static.cutoff initial,
      (Static.augmentedStack initial)[c]? = initial.expectedStack[c]?) ∧
    (∀ c ≤ Static.cutoff initial, Static.Ready initial c) ∧
    (if Static.generationEnd initial ≤ Static.boundary initial then
      Static.CyclesReady initial (Static.generationEnd initial)
    else Static.BoundarySafe initial)

namespace Static

@[simp] theorem mem_holes (initial : State source target spills) (j : Fin target.length) :
    j ∈ holes initial ↔ initial.mapping.symm j = none := by
  simp [holes]

@[simp] theorem length_holeList (initial : State source target spills) :
    (holeList initial).length = initial.mapping.unmapped_target_slots := by
  simp [holeList, holes, Mapping.unmapped_target_slots]

@[simp] theorem mem_holeList (initial : State source target spills) (j : Fin target.length) :
    j ∈ holeList initial ↔ initial.mapping.symm j = none := by
  simp [holeList]

@[simp] theorem generatedBefore_zero (initial : State source target spills) :
    generatedBefore initial 0 = 0 := by
  simp [generatedBefore]

@[simp] theorem prefixLength_zero (initial : State source target spills) :
    prefixLength initial 0 = initial.stack.length := by
  simp [prefixLength]

theorem augmentedStack_length (initial : State source target spills) (h : initial.Valid) :
    (augmentedStack initial).length = target.length := by
  simp only [augmentedStack, List.length_append, List.length_map, length_holeList, h.pending]
  exact h.size

theorem copies_pos_iff (initial : State source target spills) (cursor : Nat) (value : Value) :
    0 < copies initial cursor value ↔
      ∃ i < prefixLength initial cursor,
        prefixLength initial cursor ≤ i + (MAX_DUP_DEPTH + 1) ∧
          (augmentedStack initial)[i]? = some value := by
  simp only [copies, Finset.card_pos, Finset.Nonempty, copyPositions,
    Finset.mem_filter, Finset.mem_range]

theorem copies_zero_pos_iff (initial : State source target spills) (value : Value) :
    0 < copies initial 0 value ↔ HasCopy initial.stack value := by
  rw [copies_pos_iff]
  simp only [prefixLength_zero]
  constructor
  · rintro ⟨i, hi, hdepth, hvalue⟩
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · simpa [augmentedStack, List.getElem?_append, hi, List.getElem?_eq_getElem] using hvalue
    · exact (Stack.isDupReachable_iff_length _ _).mpr hdepth
  · rintro ⟨i, hvalue, hdepth⟩
    refine ⟨i.val, i.isLt, ?_, ?_⟩
    · exact (Stack.isDupReachable_iff_length _ _).mp hdepth
    · simpa [augmentedStack, List.getElem?_append, i.isLt, List.getElem?_eq_getElem] using hvalue

theorem ready_zero_iff (initial : State source target spills) :
    Ready initial 0 ↔ Reachable initial := by
  simp [Ready, Reachable, copies_zero_pos_iff]

end Static

-- The small-stack branch is exactly the existing reachable-copy condition.
theorem staticSuccess_iff_reachable_of_small (initial : State source target spills)
    (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1) :
    StaticSuccess initial ↔ Reachable initial := by
  simp only [StaticSuccess, hsmall, ↓reduceIte, Static.ready_zero_iff]

end Shuffler.BuildBottomUp
