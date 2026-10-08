import Shuffler.BuildBottomUp.Lemmas.StaticInvariant
import Shuffler.BuildBottomUp.Lemmas.StaticBoundary

namespace Shuffler.BuildBottomUp.Success

theorem PrefixState.mem_copyPositions_iff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (value : Value) (i : Nat) :
    i ∈ copyPositions initial cursor value ↔ i < state.stack.length ∧
      state.stack.length ≤ i + (MAX_DUP_DEPTH + 1) ∧ state.stack[i]? = some value := by
  simp only [copyPositions, Finset.mem_filter, Finset.mem_range, hp.length]
  by_cases hi : i < prefixLength initial cursor
  · rw [hp.value i hi]
  · simp [hi]

theorem PrefixState.twoCopies_iff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (value : Value) :
    2 ≤ copies initial cursor value ↔ TwoCopies state.stack value := by
  rw [copies, show (2 : Nat) = 1 + 1 from rfl, Nat.succ_le_iff, Finset.one_lt_card]
  constructor
  · rintro ⟨i, hi, j, hj, hne⟩
    obtain ⟨hil, hir, hiv⟩ := (hp.mem_copyPositions_iff value i).mp hi
    obtain ⟨hjl, hjr, hjv⟩ := (hp.mem_copyPositions_iff value j).mp hj
    refine ⟨⟨i, hil⟩, ⟨j, hjl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro he; exact hne (congrArg Fin.val he)
    · simpa [List.getElem?_eq_getElem hil] using hiv
    · simpa [List.getElem?_eq_getElem hjl] using hjv
    · exact (Stack.isDupReachable_iff_length _ _).mpr hir
    · exact (Stack.isDupReachable_iff_length _ _).mpr hjr
  · rintro ⟨i, j, hne, hiv, hjv, hir, hjr⟩
    refine ⟨i.val, ?_, j.val, ?_, ?_⟩
    · apply (hp.mem_copyPositions_iff value i.val).mpr
      exact ⟨i.isLt, (Stack.isDupReachable_iff_length _ _).mp hir,
        by simpa [List.getElem?_eq_getElem i.isLt] using hiv⟩
    · apply (hp.mem_copyPositions_iff value j.val).mpr
      exact ⟨j.isLt, (Stack.isDupReachable_iff_length _ _).mp hjr,
        by simpa [List.getElem?_eq_getElem j.isLt] using hjv⟩
    · intro he; exact hne (Fin.ext he)

theorem PrefixState.needsDup_iff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (value : Value) :
    NeedsDup state value ↔ NeedsCopy initial cursor value := by
  simp only [NeedsDup, NeedsCopy, mem_holes, hp.unbound]
  aesop

theorem PrefixState.boundarySafe_iff {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h (boundary initial) state)
    (hc : boundary initial < target.length)
    (current carrier : Fin state.stack.length) (hcurrent : current.val = boundary initial)
    (hb : state.mapping.symm ⟨boundary initial, hc⟩ = some carrier) :
    BoundarySafe initial ↔
      state.stack[current] = state.stack[carrier] ∨
        ¬NeedsDup state state.stack[carrier] ∨ TwoCopies state.stack state.stack[carrier] := by
  have he := hp.expected_value ⟨boundary initial, hc⟩ carrier hb
  have hv := hp.value (boundary initial) (by rw [← hp.length, ← hcurrent]; exact current.isLt)
  have hs : state.stack[boundary initial]? = some state.stack[current] := by
    rw [← hcurrent, List.getElem?_eq_getElem current.isLt]
    rfl
  unfold BoundarySafe
  rw [he]
  simp only [Option.some.injEq]
  rw [← hv, hs]
  simp only [Option.some.injEq, hp.twoCopies_iff, ← hp.needsDup_iff]
  constructor
  · intro hall
    exact hall state.stack[carrier] rfl
  · intro hall v heq
    subst v
    exact hall

end Shuffler.BuildBottomUp.Success
