import Shuffler.Optimality.GapCost.Ordered
import Shuffler.Optimality.GapCount.Positions

namespace Shuffler.Optimality.GapCost

theorem measure_append_other (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (value added : Value) (stack : Stack) (hne : added ≠ value) :
    measure swapPrice premium leading value (stack ++ [added]) = measure swapPrice premium leading value stack := by
  simp only [measure, GapCount.positions_append, hne, ite_false, List.append_nil]

theorem measure_append_dup (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (value : Value) (stack : Stack) (index : Nat)
    (hi : index < stack.length) (hv : stack[index] = value) (hreach : stack.length ≤ index + 16) :
    measure swapPrice premium leading value (stack ++ [value]) = measure swapPrice premium leading value stack := by
  simp only [measure, GapCount.positions_append, ite_true]
  exact pathCost_append_near swapPrice premium leading none (GapCount.positions value stack) stack.length
    (GapCount.positions_sorted value stack)
    (fun i hi => ((GapCount.positions_mem value stack i).mp hi).1)
    ⟨index, (GapCount.positions_mem value stack index).mpr ⟨hi, hv⟩, hreach⟩

theorem measure_swap (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (value : Value) (stack : Stack) (top lower : Nat)
    (ht : top + 1 = stack.length) (hl : lower < top) (hreach : top ≤ lower + 16) :
    measure swapPrice premium leading value (stack.swap top lower) ≤
      measure swapPrice premium leading value stack + if stack[lower]'(by omega) = value then swapPrice else 0 := by
  by_cases hv : stack[lower]'(by omega) = value
  · simp only [hv, ite_true]
    by_cases htvalue : stack[top]'(by omega) = value
    · have he := GapCount.positions_swap_same value stack top lower (by omega) (by omega)
        (by simp only [htvalue, hv])
      simp only [measure, he]
      omega
    · have he := GapCount.positions_swap_up value stack top lower ht hl hv htvalue
      have hm := pathCost_move_last swapPrice premium leading none (GapCount.positions value stack) lower top
        (by simp [GapCount.StartsAfter]) (GapCount.positions_sorted value stack)
        ((GapCount.positions_mem value stack lower).mpr ⟨by omega, hv⟩)
        (GapCount.positions_before_top value stack top ht htvalue) hreach
      simpa only [measure, he] using hm.2
  · simp only [hv, ite_false, Nat.add_zero]
    by_cases htvalue : stack[top]'(by omega) = value
    · let changed := stack.swap top lower
      have hlen : changed.length = stack.length := List.length_swap
      have hlow : changed[lower]'(by omega) = value := by
        simpa only [changed, List.getElem_swap_right_of_lt (show top < stack.length by omega)] using htvalue
      have hhigh : changed[top]'(by omega) ≠ value := by
        simpa only [changed, List.getElem_swap_left_of_lt (show lower < stack.length by omega)] using hv
      have he := GapCount.positions_swap_up value changed top lower (by omega) hl hlow hhigh
      have hm := pathCost_move_last swapPrice premium leading none (GapCount.positions value changed) lower top
        (by simp [GapCount.StartsAfter]) (GapCount.positions_sorted value changed)
        ((GapCount.positions_mem value changed lower).mpr ⟨by omega, hlow⟩)
        (GapCount.positions_before_top value changed top (by omega) hhigh) hreach
      have hback : changed.swap top lower = stack := by simp [changed]
      rw [← he, hback] at hm
      exact hm.1
    · have he := GapCount.positions_swap_same value stack top lower (by omega) (by omega)
        (by simp only [htvalue, hv])
      exact le_of_eq (congrArg (pathCost swapPrice premium leading none) he)

theorem measure_append_cap (swapPrice cap : Nat) (leading : Bool) (value : Value) (stack : Stack) :
    measure swapPrice (some cap) leading value (stack ++ [value]) ≤
      measure swapPrice (some cap) leading value stack + cap := by
  simp only [measure, GapCount.positions_append, ite_true]
  exact pathCost_append_cap swapPrice cap leading none _ _

theorem positions_nil_of_not_mem (value : Value) (stack : Stack) (hn : value ∉ stack) :
    GapCount.positions value stack = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  obtain ⟨hb, hv⟩ := (GapCount.positions_mem value stack i).mp hi
  exact hn (hv ▸ List.getElem_mem hb)

theorem measure_append_first (swapPrice : Nat) (premium : Option Nat) (value : Value) (stack : Stack)
    (hn : value ∉ stack) :
    measure swapPrice premium false value (stack ++ [value]) =
      measure swapPrice premium false value stack := by
  simp only [measure, GapCount.positions_append, ite_true, positions_nil_of_not_mem value stack hn,
    List.nil_append, pathCost, stepCost, Bool.false_eq_true, ite_false, Nat.add_zero]

end Shuffler.Optimality.GapCost
