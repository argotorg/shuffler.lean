import Shuffler.BuildBottomUp.Lemmas.NecessityProofs
import Mathlib.Data.Finset.Sort

namespace Shuffler.BuildBottomUp

namespace Success

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
    0 < copies initial 0 value ↔ Stack.hasCopy initial.stack value := by
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
    Ready initial 0 ↔ initial.reachable := by
  simp [Ready, State.reachable, State.isReachable, State.positionOf, copies_zero_pos_iff]

end Success

-- The small-stack branch is exactly the existing reachable-copy condition.
theorem staticSuccess_iff_reachable_of_small (initial : State source target spills)
    (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1) :
    StaticSuccess initial ↔ initial.reachable := by
  simp only [StaticSuccess, hsmall, ↓reduceIte, Success.ready_zero_iff]

end Shuffler.BuildBottomUp
