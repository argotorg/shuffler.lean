import Shuffler.Optimality.GroupEntry.Untouched

namespace Shuffler.Optimality.GroupEntry

-- After the first selection in a closed group, the number of selections
-- plus remaining wrong slots has a margin of one over its initial value.
-- The first selection cannot fix its lower slot: top is outside the group.
theorem selection_margin (positions : Finset Nat) (inside : Value → Prop)
    (wanted : Stack) (trace : Trace spills source current)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length)
    (hsource : ∀ (i : Nat) (hi : i < source.length), i ∉ positions → ¬inside source[i])
    (hwanted : ∀ i ∈ positions, ∃ hi : i < wanted.length, inside wanted[i])
    (hpop : trace.noPop) (hadded : ∀ value ∈ trace.additions, ¬inside value) :
    (differences positions wanted source).card + min 1 (selections positions trace) ≤
      selections positions trace + (differences positions wanted current).card := by
  induction trace with
  | Lit => simp [selections]
  | @Swap previous depth hd hlo hhi trace ih =>
      have hp := ih hpop hadded
      have ht := top_notMem positions source previous hpositions (trace.noPop_length_le hpop)
      by_cases hl : previous.length - 1 - depth ∈ positions
      · have hmin : min 1 (selections positions trace + 1) = 1 := min_eq_left (by omega)
        simp only [selections, hl, ite_true, hmin]
        by_cases hz : selections positions trace = 0
        · have hout := outside_of_zero positions inside trace hpositions hsource hpop hz hadded
          have htop : ¬inside previous[previous.length - 1] := hout _ (by omega) ht
          obtain ⟨hw, hwgroup⟩ := hwanted _ hl
          have hdifferent : wanted[previous.length - 1 - depth]? ≠
              (previous.swap (previous.length - 1) (previous.length - 1 - depth))[previous.length - 1 - depth]? := by
            rw [List.getElem?_eq_getElem hw,
              List.getElem?_eq_getElem (show previous.length - 1 - depth <
                (previous.swap (previous.length - 1) (previous.length - 1 - depth)).length by
                  simp only [List.length_swap]; omega),
              List.getElem_swap_right_of_lt (by omega)]
            intro he
            exact htop (Option.some.inj he ▸ hwgroup)
          have hm := Finset.card_le_card
            (differences_subset_swap positions wanted previous _ _ ht hl hdifferent)
          simp only [hz, Nat.min_zero, Nat.add_zero, Nat.zero_add] at hp
          omega
        · have hm := (Finset.card_le_card
            (differences_swap_subset positions wanted previous
              (previous.length - 1) (previous.length - 1 - depth) ht)).trans
            (Finset.card_insert_le _ _)
          have hprevmin : min 1 (selections positions trace) = 1 := min_eq_left (by omega)
          rw [hprevmin] at hp
          omega
      · rw [differences_swap_eq positions wanted previous _ _ ht hl]
        simpa only [selections, hl, ite_false, Nat.add_zero] using hp
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [differences_append positions wanted]
      · apply ih hpop
        intro value hv
        exact hadded value (Multiset.mem_add.mpr (Or.inl hv))
      · intro i hi
        have hp := hpositions i hi
        have hl := trace.noPop_length_le hpop
        omega
  | Pop _ _ => exact False.elim hpop

-- A nonempty mismatch group with no births needs one more selection than
-- its number of originally wrong slots. No assumption about the chosen
-- occurrence mapping or the planner's control flow is used.
theorem entry_lowerBound (positions : Finset Nat) (inside : Value → Prop)
    (trace : Trace spills source target)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length)
    (hsource : ∀ (i : Nat) (hi : i < source.length), i ∉ positions → ¬inside source[i])
    (htarget : ∀ i ∈ positions, ∃ hi : i < target.length, inside target[i])
    (hpop : trace.noPop) (hadded : ∀ value ∈ trace.additions, ¬inside value)
    (hwrong : 0 < (differences positions target source).card) :
    (differences positions target source).card + 1 ≤ selections positions trace := by
  have hm := selection_margin positions inside target trace hpositions hsource htarget hpop hadded
  have ht : differences positions target target = ∅ := by simp [differences]
  rw [ht, Finset.card_empty, Nat.add_zero] at hm
  have hs : 0 < selections positions trace := by omega
  rw [min_eq_left (show 1 ≤ selections positions trace by omega)] at hm
  exact hm

end Shuffler.Optimality.GroupEntry
