import Shuffler.Optimality.GapCount.Positions

namespace Shuffler.Optimality.GapCount

theorem potential_append_other (value added : Value) (stack : Stack) (hne : added ≠ value) :
    potential value (stack ++ [added]) = potential value stack := by
  simp only [potential, positions_append, hne, ite_false, List.append_nil]

theorem potential_append_dup (value : Value) (stack : Stack) (index : Nat)
    (hi : index < stack.length) (hv : stack[index] = value) (hreach : stack.length ≤ index + 16) :
    potential value (stack ++ [value]) = potential value stack := by
  simp only [potential, positions_append, ite_true]
  exact pathCost_append_near none (positions value stack) stack.length
    (positions_sorted value stack)
    (fun i hi => ((positions_mem value stack i).mp hi).1)
    ⟨index, (positions_mem value stack index).mpr ⟨hi, hv⟩, hreach⟩

theorem potential_swap (value : Value) (stack : Stack) (top lower : Nat)
    (ht : top + 1 = stack.length) (hl : lower < top) (hreach : top ≤ lower + 16) :
    potential value (stack.swap top lower) ≤ potential value stack +
      if stack[lower]'(by omega) = value then 1 else 0 := by
  by_cases hv : stack[lower]'(by omega) = value
  · simp only [hv, ite_true]
    by_cases htvalue : stack[top]'(by omega) = value
    · have he := positions_swap_same value stack top lower (by omega) (by omega)
        (by simp only [htvalue, hv])
      simp only [potential, he]
      omega
    · have he := positions_swap_up value stack top lower ht hl hv htvalue
      have hm := pathCost_move_last none (positions value stack) lower top
        (by simp [StartsAfter]) (positions_sorted value stack)
        ((positions_mem value stack lower).mpr ⟨by omega, hv⟩)
        (positions_before_top value stack top ht htvalue) hreach
      simpa only [potential, he] using hm.2
  · simp only [hv, ite_false, Nat.add_zero]
    by_cases htvalue : stack[top]'(by omega) = value
    · let changed := stack.swap top lower
      have hlen : changed.length = stack.length := List.length_swap
      have hlow : changed[lower]'(by omega) = value := by
        simpa only [changed, List.getElem_swap_right_of_lt (show top < stack.length by omega)] using htvalue
      have hhigh : changed[top]'(by omega) ≠ value := by
        simpa only [changed, List.getElem_swap_left_of_lt (show lower < stack.length by omega)] using hv
      have he := positions_swap_up value changed top lower (by omega) hl hlow hhigh
      have hm := pathCost_move_last none (positions value changed) lower top
        (by simp [StartsAfter]) (positions_sorted value changed)
        ((positions_mem value changed lower).mpr ⟨by omega, hlow⟩)
        (positions_before_top value changed top (by omega) hhigh) hreach
      have hback : changed.swap top lower = stack := by simp [changed]
      rw [← he, hback] at hm
      exact hm.1
    · have he := positions_swap_same value stack top lower (by omega) (by omega)
        (by simp only [htvalue, hv])
      exact le_of_eq (congrArg (pathCost none) he)

end Shuffler.Optimality.GapCount
