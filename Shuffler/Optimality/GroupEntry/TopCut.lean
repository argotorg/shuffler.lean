import Shuffler.Optimality.GroupEntry.FirstBirth
import Shuffler.Optimality.GroupEntry.Invariant

namespace Shuffler.Optimality.GroupEntry

theorem selections_union (first second : Finset Nat) (hd : Disjoint first second)
    (trace : Trace spills source target) :
    selections (first ∪ second) trace = selections first trace + selections second trace := by
  induction trace with
  | Lit => rfl
  | @Swap previous depth _ _ _ trace ih =>
      by_cases hf : previous.length - 1 - depth ∈ first
      · have hs : previous.length - 1 - depth ∉ second :=
          fun hm => Finset.disjoint_left.mp hd hf hm
        simp only [selections, Finset.mem_union, hf, hs, true_or, ite_true, ite_false, ih]
        omega
      · by_cases hs : previous.length - 1 - depth ∈ second <;>
          simp only [selections, Finset.mem_union, hf, hs, false_or, ite_true, ite_false, ih] <;> omega
  | Dup _ _ _ _ _ ih | Pop _ _ ih | Push _ _ _ ih | Load _ _ _ ih => exact ih

theorem differences_union_card (first second : Finset Nat) (hd : Disjoint first second)
    (wanted current : Stack) :
    (differences (first ∪ second) wanted current).card =
      (differences first wanted current).card + (differences second wanted current).card := by
  unfold differences
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

-- A cut contains the wanted value at the original top, but not its source
-- value. A first entry must leave one old cut slot wrong. If the original
-- top is selected after a birth, that selection instead pays the extra one.
theorem topCut_lowerBound (positions : Finset Nat) (inside : Value → Prop)
    (trace : Trace spills source target)
    (hne : 0 < source.length)
    (hpositions : ∀ i ∈ positions, i + 1 < source.length)
    (hsource : ∀ (i : Nat) (hi : i < source.length), i ∉ positions → ¬inside source[i])
    (htarget : ∀ i ∈ positions, ∃ hi : i < target.length, inside target[i])
    (htop : ∃ hi : source.length - 1 < target.length, inside target[source.length - 1])
    (hpop : trace.noPop) :
    (differences positions target source).card + 1 ≤
      selections positions trace + selections {source.length - 1} trace := by
  have hnot : source.length - 1 ∉ positions := by
    intro hm
    have := hpositions _ hm
    omega
  by_cases hz : selections {source.length - 1} trace = 0
  · have hmargin : (differences positions target source).card + 1 ≤
        selections positions trace := by
      by_cases ha : trace.additions = 0
      · have hadded : ∀ value ∈ trace.additions, ¬inside value := by simp [ha]
        have hp : 0 < selections positions trace := by
          by_contra hn
          have hout := outside_of_zero positions inside trace hpositions hsource hpop
            (by omega) hadded
          obtain ⟨hi, ht⟩ := htop
          exact hout _ hi hnot ht
        have hm := selection_margin positions inside target trace hpositions hsource htarget hpop hadded
        simpa only [min_eq_left (show 1 ≤ selections positions trace by omega),
          differences, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
          Nat.add_zero] using hm
      · obtain ⟨middle, value, before, tail, hb, hzero, ht, hc⟩ := firstBirth trace hpop ha
        have hlength : middle.length = source.length := by
          simpa only [hzero, Multiset.card_zero, Nat.add_zero] using before.noPop_length hb
        have htailzero : selections {source.length - 1} tail = 0 := by
          have := hc {source.length - 1}
          omega
        have hsame := zero_selections_value tail ht (source.length - 1)
          (by simp only [List.length_append, List.length_singleton]; omega) htailzero
        have hinside : inside (middle[source.length - 1]'(by omega)) := by
          obtain ⟨hi, ht⟩ := htop
          rw [List.getElem?_append_left (show source.length - 1 < middle.length by omega),
            List.getElem?_eq_getElem (show source.length - 1 < middle.length by omega),
            List.getElem?_eq_getElem hi] at hsame
          exact (Option.some.inj hsame).symm ▸ ht
        have hadded : ∀ value ∈ before.additions, ¬inside value := by simp [hzero]
        have hp : 0 < selections positions before := by
          by_contra hn
          have hout := outside_of_zero positions inside before hpositions hsource hb
            (by omega) hadded
          exact hout _ (by omega) hnot hinside
        have hm := selection_margin positions inside target before hpositions hsource htarget hb hadded
        rw [min_eq_left (show 1 ≤ selections positions before by omega)] at hm
        have hbudget := differences_le_selections positions tail
          (by intro i hi; have := hpositions i hi
              simp only [List.length_append, List.length_singleton]; omega) ht
        rw [differences_append positions target middle [value]
          (by intro i hi; have := hpositions i hi; omega)] at hbudget
        have hcount := hc positions
        omega
    omega
  · have hm := differences_le_selections positions trace hpositions hpop
    omega

-- Positions outside the cut still pay for their original mismatches.
theorem topCut_lowerBound_superset (positions all : Finset Nat) (inside : Value → Prop)
    (trace : Trace spills source target)
    (hne : 0 < source.length) (hsub : positions ⊆ all)
    (hall : ∀ i ∈ all, i + 1 < source.length)
    (hsource : ∀ (i : Nat) (hi : i < source.length), i ∉ positions → ¬inside source[i])
    (htarget : ∀ i ∈ positions, ∃ hi : i < target.length, inside target[i])
    (htop : ∃ hi : source.length - 1 < target.length, inside target[source.length - 1])
    (hpop : trace.noPop) :
    (differences all target source).card + 1 ≤
      selections all trace + selections {source.length - 1} trace := by
  have hcut := topCut_lowerBound positions inside trace hne
    (fun i hi => hall i (hsub hi)) hsource htarget htop hpop
  have hrest := differences_le_selections (all \ positions) trace
    (fun i hi => hall i (Finset.mem_sdiff.mp hi).1) hpop
  have hd : Disjoint positions (all \ positions) :=
    Finset.disjoint_left.mpr (fun _ hi hj => (Finset.mem_sdiff.mp hj).2 hi)
  have hu : positions ∪ (all \ positions) = all := Finset.union_sdiff_of_subset hsub
  have hc := differences_union_card positions (all \ positions) hd target source
  have hs := selections_union positions (all \ positions) hd trace
  rw [hu] at hc hs
  omega

end Shuffler.Optimality.GroupEntry
