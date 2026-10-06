import Shuffler.BuildBottomUp.Lemmas.StaticCounts
import Shuffler.BuildBottomUp.Lemmas.StaticCycles

namespace Shuffler.BuildBottomUp

theorem Invariant.valid {state : State source target spills} (h : Invariant cursor state) :
    state.Valid := ⟨h.size, h.pending, h.available⟩

namespace Static

-- This relation is used in the proof only. The public predicate has no state
-- updates or execution history.
structure PrefixState (initial : State source target spills) (hvalid : initial.Valid)
    (cursor : Nat) (state : State source target spills) : Prop where
  invariant : Invariant cursor state
  stack_eq : state.stack = (augmentedStack initial).take (prefixLength initial cursor)
  unbound : ∀ j, state.mapping.symm j = none ↔
    initial.mapping.symm j = none ∧ cursor ≤ j.val
  expected : state.expectedStack = initial.expectedStack
  cycles : ContractsCycles (completedPermutation initial hvalid)
    (completedPermutation state invariant.valid) cursor

theorem PrefixState.initial (initial : State source target spills) (h : initial.Valid) :
    PrefixState initial h 0 initial where
  invariant := Invariant.initial h
  stack_eq := by simp [augmentedStack]
  unbound := by simp
  expected := rfl
  cycles := ContractsCycles.initial _

theorem PrefixState.length {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) : state.stack.length = prefixLength initial cursor := by
  rw [hp.stack_eq, List.length_take, augmentedStack_length initial h,
    Nat.min_eq_left (prefixLength_le initial h cursor)]

theorem hasCopy_iff_indices (stack : Stack) (value : Value) :
    HasCopy stack value ↔ ∃ i < stack.length,
      stack.length ≤ i + (MAX_DUP_DEPTH + 1) ∧ stack[i]? = some value := by
  constructor
  · rintro ⟨i, hv, hr⟩
    refine ⟨i.val, i.isLt, ?_, ?_⟩
    · exact (Stack.isDupReachable_iff_length _ _).mp hr
    · simpa [List.getElem?_eq_getElem i.isLt] using hv
  · rintro ⟨i, hi, hr, hv⟩
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · simpa [List.getElem?_eq_getElem hi] using hv
    · exact (Stack.isDupReachable_iff_length _ _).mpr hr

theorem PrefixState.copies_iff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (value : Value) :
    0 < copies initial cursor value ↔ HasCopy state.stack value := by
  rw [copies_pos_iff, hasCopy_iff_indices, hp.length]
  apply exists_congr
  intro i
  by_cases hi : i < prefixLength initial cursor
  · simp only [hi, true_and]
    rw [hp.stack_eq]
    simp [hi]
  · simp [hi]

theorem PrefixState.ready_iff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) : Ready initial cursor ↔ Reachable state := by
  simp only [Ready, Reachable, mem_holes, ← hp.copies_iff, hp.unbound]
  constructor
  · intro hs j ⟨hb, hc⟩
    exact hs j hb hc
  · intro hs j hb hc
    exact hs j ⟨hb, hc⟩

theorem PrefixState.value {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (i : Nat) (hi : i < prefixLength initial cursor) :
    state.stack[i]? = (augmentedStack initial)[i]? := by
  rw [hp.stack_eq]
  simp [hi]

theorem PrefixState.expected_value {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (dest : Fin target.length)
    (carrier : Fin state.stack.length) (hb : state.mapping.symm dest = some carrier) :
    initial.expectedStack[dest.val]? = some state.stack[carrier] := by
  rw [← hp.expected]
  simp [State.expectedStack, dest.isLt, hb]

end Static

end Shuffler.BuildBottomUp
