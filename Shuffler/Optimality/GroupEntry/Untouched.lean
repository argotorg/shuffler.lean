import Shuffler.Optimality.GroupEntry.Movement

namespace Shuffler.Optimality.GroupEntry

private theorem outside_append (positions : Finset Nat) (inside : Value → Prop)
    (current : Stack) (value : Value)
    (hcurrent : ∀ (i : Nat) (hi : i < current.length), i ∉ positions → ¬inside current[i])
    (hvalue : ¬inside value) :
    ∀ (i : Nat) (hi : i < (current ++ [value]).length), i ∉ positions →
      ¬inside (current ++ [value])[i] := by
  intro i hi hn
  by_cases hp : i < current.length
  · rw [List.getElem_append_left hp]
    exact hcurrent i hp hn
  · have he : i = current.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    subst i
    simpa only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] using hvalue

-- If a group has no new births and none of its original slots has been
-- selected, every occurrence of its values remains inside those slots.
theorem outside_of_zero (positions : Finset Nat) (inside : Value → Prop)
    (trace : Trace spills source current)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length)
    (hsource : ∀ (i : Nat) (hi : i < source.length), i ∉ positions → ¬inside source[i])
    (hpop : trace.noPop) (hzero : selections positions trace = 0)
    (hadded : ∀ value ∈ trace.additions, ¬inside value) :
    ∀ (i : Nat) (hi : i < current.length), i ∉ positions → ¬inside current[i] := by
  induction trace with
  | Lit => exact hsource
  | @Swap previous depth hd hlo hhi trace ih =>
      by_cases hselected : previous.length - 1 - depth ∈ positions
      · simp only [selections, hselected, ite_true] at hzero
        omega
      · have hz : selections positions trace = 0 := by
          simpa only [selections, hselected, ite_false, Nat.add_zero] using hzero
        have hp := ih hpop hz hadded
        have ht := top_notMem positions source previous hpositions (trace.noPop_length_le hpop)
        intro i hi hn
        have hip : i < previous.length := by simpa only [List.length_swap] using hi
        by_cases hitop : i = previous.length - 1
        · subst i
          rw [List.getElem_swap_left_of_lt (by omega)]
          exact hp _ (by omega) hselected
        · by_cases hilower : i = previous.length - 1 - depth
          · subst i
            rw [List.getElem_swap_right_of_lt (by omega)]
            exact hp _ (by omega) ht
          · rw [List.getElem_swap_of_ne hitop hilower]
            exact hp i hip hn
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      apply outside_append positions inside
      · apply ih hpop hzero
        intro value hv
        exact hadded value (Multiset.mem_add.mpr (Or.inl hv))
      · exact hadded _ (Multiset.mem_add.mpr (Or.inr (by simp)))
  | Pop _ _ => exact False.elim hpop

end Shuffler.Optimality.GroupEntry
