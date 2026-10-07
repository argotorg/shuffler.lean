import Shuffler.Optimality.GroupEntry.CorrectBoundaryDefs
import Shuffler.Optimality.GroupEntry.TopCut

namespace Shuffler.Optimality.GroupEntry

open Shuffler.Placement

-- A first visit to a value group leaves a wrong lower slot. Its visit and
-- later repair cost two selections when all group slots start correct.
theorem selected_group_repair_margin (positions : Finset Nat) (inside : Value → Prop)
    (wanted : Stack) (trace : Trace spills source current)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length)
    (hsource : ∀ (i : Nat) (hi : i < source.length), i ∉ positions → ¬inside source[i])
    (hwanted : ∀ i ∈ positions, ∃ hi : i < wanted.length, inside wanted[i])
    (hpop : trace.noPop) (hadded : ∀ value ∈ trace.additions, ¬inside value) :
    2 * min 1 (selections positions trace) ≤
      selections positions trace + (differences positions wanted current).card := by
  induction trace with
  | Lit => simp [selections]
  | @Swap previous depth hd hlo hhi trace ih =>
      have hp := ih hpop hadded
      have ht := top_notMem positions source previous hpositions (trace.noPop_length_le hpop)
      by_cases hl : previous.length - 1 - depth ∈ positions
      · have hmin : min 1 (selections positions trace + 1) = 1 := min_eq_left (by omega)
        simp only [selections, hl, ite_true, hmin, Nat.mul_one]
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
          have hm : 1 ≤ (differences positions wanted
              (previous.swap (previous.length - 1) (previous.length - 1 - depth))).card :=
            Finset.one_le_card.mpr ⟨_, Finset.mem_filter.mpr ⟨hl, hdifferent⟩⟩
          omega
        · have hm := (Finset.card_le_card
            (differences_swap_subset positions wanted previous
              (previous.length - 1) (previous.length - 1 - depth) ht)).trans
            (Finset.card_insert_le _ _)
          rw [min_eq_left (show 1 ≤ selections positions trace by omega)] at hp
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

theorem boundary_group_two_selections (positions : Finset Nat) (value : Value)
    (trace : Trace spills source target)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length)
    (hsource : ∀ (i : Nat) (hi : i < source.length), i ∉ positions → source[i] ≠ value)
    (hwanted : ∀ i ∈ positions, target[i]? = some value)
    (hboundary : target[frozen source]? = some value)
    (houtside : frozen source ∉ positions)
    (hlarge : 17 ≤ source.length) (hpop : trace.noPop) (hadded : trace.additions ≠ 0) :
    2 ≤ selections positions trace := by
  obtain ⟨middle, first, before, tail, hb, hz, ht, hc⟩ := firstBirth trace hpop hadded
  have hlen : middle.length = source.length := by
    simpa only [hz, Multiset.card_zero, Nat.add_zero] using before.noPop_length hb
  have hi : frozen source < middle.length := by unfold frozen MAX_SWAP_DEPTH; omega
  have hcut : frozen (middle ++ [first]) = frozen source + 1 := by
    simp only [frozen, List.length_append, List.length_singleton, hlen]
    unfold MAX_SWAP_DEPTH
    omega
  have hmiddle : middle[frozen source] = value := by
    have hf := tail.noPop_frozen ht
    rw [hcut, List.take_append_of_le_length (by omega)] at hf
    have hx := congrArg (fun stack : Stack => stack[frozen source]?) hf
    have hm : target[frozen source]? = some middle[frozen source] := by
      simpa [List.getElem?_eq_getElem hi] using hx
    rw [hboundary] at hm
    exact (Option.some.inj hm).symm
  have hnoBirth : ∀ other ∈ before.additions, ¬(other = value) := by simp [hz]
  have hpositive : 0 < selections positions before := by
    by_contra hn
    have hout := outside_of_zero positions (· = value) before hpositions hsource hb (by omega) hnoBirth
    exact hout _ hi houtside hmiddle
  have hw : ∀ i ∈ positions, ∃ hi : i < target.length, target[i] = value := by
    intro i hi
    have ht := hwanted i hi
    have hlt : i < target.length := List.getElem?_eq_some_iff.mp ht |>.1
    exact ⟨hlt, by simpa only [List.getElem?_eq_getElem hlt, Option.some.injEq] using ht⟩
  have hm := selected_group_repair_margin positions (· = value) target before
    hpositions hsource hw hb hnoBirth
  rw [min_eq_left (show 1 ≤ selections positions before by omega)] at hm
  have htCount := differences_le_selections positions tail
    (by intro i hi; have := hpositions i hi
        simp only [List.length_append, List.length_singleton]; omega) ht
  rw [differences_append positions target middle [first]
    (by intro i hi; have := hpositions i hi; omega)] at htCount
  have hcounts := hc positions
  omega

theorem selections_le_swapCount (positions : Finset Nat) (trace : Trace spills source target) :
    selections positions trace ≤ trace.swapCount := by
  induction trace with
  | Lit => exact Nat.le_refl _
  | Swap _ _ _ _ trace ih =>
      simp only [selections, Trace.swapCount]
      split <;> omega
  | Dup _ _ _ _ _ ih | Pop _ _ ih | Push _ _ _ ih | Load _ _ _ ih => exact ih

theorem CorrectBoundary.mismatches_add_two_le (value : Value)
    (hcondition : CorrectBoundary source target missing value)
    (trace : Trace spills source target) (he : Shuffler.Optimality.Eligible missing trace) :
    (OldPositions.mismatches source target).card + 2 ≤ trace.swapCount := by
  obtain ⟨hadded, hlarge, hboundary, hwrong, htop, hcorrect⟩ := hcondition
  let positions := (Finset.range source.length).filter fun i => source[i]? = some value
  have hpos : ∀ i ∈ positions, i + 1 < source.length := by
    intro i hi
    obtain ⟨hrange, hv⟩ := Finset.mem_filter.mp hi
    have hl := Finset.mem_range.mp hrange
    have hn : i ≠ source.length - 1 := by intro heq; exact htop (heq ▸ hv)
    omega
  have hout : ∀ (i : Nat) (hi : i < source.length), i ∉ positions → source[i] ≠ value := by
    intro i hi hn hv
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, by simpa [List.getElem?_eq_getElem hi] using hv⟩)
  have hwanted : ∀ i ∈ positions, target[i]? = some value := by
    intro i hi
    obtain ⟨hrange, hv⟩ := Finset.mem_filter.mp hi
    have hl := Finset.mem_range.mp hrange
    exact hcorrect ⟨i, hl⟩ (by simpa [List.getElem?_eq_getElem hl] using hv)
  have houtside : frozen source ∉ positions := by
    intro hm
    exact hwrong (Finset.mem_filter.mp hm).2
  have htwo := boundary_group_two_selections positions value trace hpos hout hwanted
    hboundary houtside hlarge he.1 (by rwa [he.2])
  let wrong := OldPositions.mismatches source target
  have hwrongPos : ∀ i ∈ wrong, i + 1 < source.length := by
    intro i hi
    have hr := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega
  have hbudget := differences_le_selections wrong trace hwrongPos he.1
  have hdifferences : differences wrong target source = wrong := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact Ne.symm (Finset.mem_filter.mp hi).2
  rw [hdifferences] at hbudget
  have hdisjoint : Disjoint wrong positions := by
    apply Finset.disjoint_left.mpr
    intro i hi hp
    have hn := (Finset.mem_filter.mp hi).2
    exact hn ((Finset.mem_filter.mp hp).2.trans (hwanted i hp).symm)
  have hc := selections_le_swapCount (wrong ∪ positions) trace
  rw [selections_union wrong positions hdisjoint trace] at hc
  dsimp only [wrong] at hbudget hc
  omega

theorem correctBoundaryBound_le_swapCount (trace : Trace spills source target)
    (he : Shuffler.Optimality.Eligible missing trace) :
    correctBoundaryBound source target missing ≤ trace.swapCount := by
  unfold correctBoundaryBound
  cases hc : checkedCorrectBoundary source target missing with
  | none => simp
  | some cert =>
      simp only [Option.isSome_some, ite_true]
      exact CorrectBoundary.mismatches_add_two_le cert.val cert.property trace he

end Shuffler.Optimality.GroupEntry
