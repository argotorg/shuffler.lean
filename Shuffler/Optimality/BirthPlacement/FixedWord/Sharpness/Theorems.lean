import Shuffler.Optimality.BirthPlacement.FixedWord.Sharpness

namespace Shuffler.Optimality.BirthPlacement.Sharpness

@[simp] theorem word_length (count : Nat) : (word count).length = 2 * count := List.length_ofFn

@[simp] theorem target_length (count : Nat) : (target count).length = 2 * count := List.length_ofFn

theorem word_ne_target (count : Nat) (hk : 2 ≤ count) (index : Fin (2 * count)) :
    (word count)[index.val]'(by simpa only [word_length] using index.isLt) ≠
      (target count)[index.val]'(by simpa only [target_length] using index.isLt) := by
  intro he
  have hv := congrArg (fun v : Value => match v with | .Var id => id.val | _ => 0) he
  simp only [word, target, List.getElem_ofFn, value] at hv
  have hi := index.isLt
  split_ifs at hv <;> omega

-- Every occurrence assignment must move every position, even when equal
-- copies may be assigned to different target occurrences.
theorem assignment_support (count : Nat) (hk : 2 ≤ count)
    (assignment : Equiv.Perm (Fin (target count).length))
    (hword : birthWord (target count) assignment = word count) :
    assignment.support = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro index
  apply Equiv.Perm.mem_support.mpr
  intro he
  have hv := congrArg (fun values : Stack => values[index.val]?) hword
  simp only [birthWord, List.getElem?_ofFn, dite_eq_left index.isLt, he] at hv
  have hi : index.val < 2 * count := by simpa only [target_length] using index.isLt
  have hn := word_ne_target count hk ⟨index.val, hi⟩
  have hiw : index.val < (word count).length := by simpa only [word_length] using hi
  rw [List.getElem?_eq_getElem hiw] at hv
  simp only [Option.some.injEq] at hv
  exact hn hv.symm

-- This lower bound compares all legal no-POP traces with the same birth
-- values. It does not fix occurrence identities or direct/DUP methods.
theorem swaps_lower_bound (count : Nat) (hk : 2 ≤ count)
    (trace : Trace activeSpills [] (target count)) (hpop : trace.noPop)
    (hword : SwapRuns.births trace = word count) : count ≤ trace.swapCount := by
  have hw := traceAssignment_birthWord trace hpop
  simp only [List.nil_append, hword] at hw
  have he := assignment_support count hk (traceAssignment trace hpop) hw
  have hm := traceAssignment_moved_le trace hpop
  rw [he, Finset.card_univ, Fintype.card_fin, target_length] at hm
  omega

theorem gas_lower_bound (count : Nat) (hk : 2 ≤ count)
    (trace : Trace (spills count) [] (target count)) (hpop : trace.noPop)
    (hword : SwapRuns.births trace = word count) :
    baseline costs .gasOnly (spills count) [] (target count : Multiset Value) + 3 * count ≤
      (traceCost costs trace).gas := by
  have hb := baseline_add_swapCost_le_score costs .gasOnly trace hpop
  have hm := swaps_lower_bound count hk trace hpop hword
  have ha := trace.noPop_balance hpop
  simp only [Multiset.coe_nil, zero_add] at ha
  rw [← ha] at hb
  simp only [Cost.score_gasOnly] at hb
  change baseline costs .gasOnly (spills count) [] (target count : Multiset Value) +
    3 * trace.swapCount ≤ (traceCost costs trace).gas at hb
  omega

theorem bytes_lower_bound (count : Nat) (hk : 2 ≤ count)
    (trace : Trace (spills count) [] (target count)) (hpop : trace.noPop)
    (hword : SwapRuns.births trace = word count) :
    baseline costs .bytesOnly (spills count) [] (target count : Multiset Value) + count ≤
      (traceCost costs trace).bytes := by
  have hb := baseline_add_swapCost_le_score costs .bytesOnly trace hpop
  have hm := swaps_lower_bound count hk trace hpop hword
  have ha := trace.noPop_balance hpop
  simp only [Multiset.coe_nil, zero_add] at ha
  rw [← ha] at hb
  simp only [Cost.score_bytesOnly] at hb
  change baseline costs .bytesOnly (spills count) [] (target count : Multiset Value) +
    1 * trace.swapCount ≤ (traceCost costs trace).bytes at hb
  omega

end Shuffler.Optimality.BirthPlacement.Sharpness
