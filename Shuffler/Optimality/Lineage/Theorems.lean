import Shuffler.Optimality.Lineage
import Shuffler.Optimality.Baseline.Theorems

namespace Shuffler.Optimality.Lineage

theorem index_le_maxIndex (value : Value) (stack : Stack)
    (index : Nat) (hi : index < stack.length) (hv : stack[index] = value) :
    index ≤ maxIndex value stack := by
  have hget : stack[index]? = some value := by simp [hi, hv]
  have h := Finset.le_sup (s := Finset.range stack.length)
    (f := fun i => if stack[i]? = some value then i else 0) (Finset.mem_range.mpr hi)
  simpa [maxIndex, hget] using h

theorem maxIndex_le (value : Value) (stack : Stack) (bound : Nat)
    (h : ∀ index (hi : index < stack.length), stack[index] = value → index ≤ bound) :
    maxIndex value stack ≤ bound := by
  apply Finset.sup_le
  intro index hi
  split_ifs with hv
  · have hi' : index < stack.length := Finset.mem_range.mp hi
    exact h index hi' (by simpa [hi'] using hv)
  · exact Nat.zero_le _

theorem index_le_of_no_direct (value : Value) (trace : Trace spills source target)
    (bound : Nat)
    (hsource : ∀ index (hi : index < source.length), source[index] = value → index ≤ bound)
    (hno : directCount value trace = 0) :
    ∀ index (hi : index < target.length), target[index] = value →
      index ≤ bound + 16 * (dupCount value trace + upwardCount value trace) := by
  induction trace with
  | Lit =>
      intro index hi hv
      simpa [dupCount, upwardCount] using hsource index hi hv
  | @Swap prev depth hlen hlo hhi trace ih =>
      intro index hi hv
      have hprevious : directCount value trace = 0 := hno
      have htop : prev.length - 1 < prev.length := by omega
      have hlower : prev.length - 1 - depth < prev.length := by omega
      have hi' : index < prev.length := by simpa using hi
      by_cases he : index = prev.length - 1
      · have hvalue : prev[prev.length - 1 - depth] = value := by
          simpa only [he, List.getElem_swap_left_of_lt hlower] using hv
        have h := ih hprevious (prev.length - 1 - depth) hlower hvalue
        simp only [dupCount, upwardCount, hvalue, ite_true]
        dsimp [MAX_SWAP_DEPTH] at hhi
        omega
      · by_cases he' : index = prev.length - 1 - depth
        · have hvalue : prev[prev.length - 1] = value := by
            simpa only [he', List.getElem_swap_right_of_lt htop] using hv
          have h := ih hprevious (prev.length - 1) htop hvalue
          simp only [dupCount, upwardCount]
          split_ifs <;> omega
        · have hvalue : prev[index] = value := by
            simpa only [List.getElem_swap_of_ne he he'] using hv
          have h := ih hprevious index hi' hvalue
          simp only [dupCount, upwardCount]
          split_ifs <;> omega
  | @Dup prev depth hlen hlo hhi trace ih =>
      intro index hi hv
      have hprevious : directCount value trace = 0 := hno
      have hcopy : prev.length - depth < prev.length := by omega
      by_cases hi' : index < prev.length
      · have hvalue : prev[index] = value := by
          simpa only [List.getElem_append_left hi'] using hv
        have h := ih hprevious index hi' hvalue
        simp only [dupCount, upwardCount]
        split_ifs <;> omega
      · have he : index = prev.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        have hvalue : prev[prev.length - depth] = value := by simpa [he] using hv
        have h := ih hprevious (prev.length - depth) hcopy hvalue
        simp only [dupCount, upwardCount, hvalue, ite_true]
        dsimp [MAX_DUP_DEPTH] at hhi
        omega
  | @Pop prev hlen trace ih =>
      intro index hi hv
      have hi' : index < prev.length := by simp only [List.length_dropLast] at hi; omega
      have hvalue : prev[index] = value := by simpa using hv
      exact ih hno index hi' hvalue
  | @Push prev added hfree trace ih =>
      intro index hi hv
      have hprevious : directCount value trace = 0 := by
        dsimp [directCount] at hno
        omega
      by_cases hi' : index < prev.length
      · have hvalue : prev[index] = value := by
          simpa only [List.getElem_append_left hi'] using hv
        exact ih hprevious index hi' hvalue
      · have he : index = prev.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        have hvalue : added = value := by simpa [he] using hv
        simp [directCount, hvalue] at hno
  | @Load prev id hspilled trace ih =>
      intro index hi hv
      have hprevious : directCount value trace = 0 := by
        dsimp [directCount] at hno
        omega
      by_cases hi' : index < prev.length
      · have hvalue : prev[index] = value := by
          simpa only [List.getElem_append_left hi'] using hv
        exact ih hprevious index hi' hvalue
      · have he : index = prev.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        have hvalue : Value.Var id = value := by simpa [he] using hv
        simp [directCount, hvalue] at hno

theorem maxIndex_le_of_no_direct (value : Value) (trace : Trace spills source target)
    (hno : directCount value trace = 0) :
    maxIndex value target ≤ maxIndex value source +
      16 * (dupCount value trace + upwardCount value trace) := by
  apply maxIndex_le
  exact index_le_of_no_direct value trace (maxIndex value source)
    (index_le_maxIndex value source) hno

theorem additions_count_eq (value : Value) (trace : Trace spills source target) :
    trace.additions.count value = dupCount value trace + directCount value trace := by
  induction trace <;>
    simp_all [Trace.additions, dupCount, directCount, Multiset.count_add,
      Multiset.count_singleton, Nat.add_assoc, Nat.add_comm, eq_comm]

theorem sum_upwardCount_le (values : Finset Value) (trace : Trace spills source target) :
    values.sum (fun value => upwardCount value trace) ≤ trace.swapCount := by
  induction trace with
  | Lit => simp [upwardCount, Trace.swapCount]
  | @Swap prev index hlen hlo hhi trace ih =>
      simp only [upwardCount, Trace.swapCount, Finset.sum_add_distrib]
      apply Nat.add_le_add ih
      simp only [Finset.sum_ite_eq]
      split_ifs <;> omega
  | Dup _ _ _ _ _ ih | Pop _ _ ih | Push _ _ _ ih | Load _ _ _ ih =>
      exact ih

theorem requiredSwaps_le_upwardCount (value : Value) (trace : Trace spills source target)
    (hno : directCount value trace = 0) :
    requiredSwaps value source target trace.additions ≤ upwardCount value trace := by
  have hbound := maxIndex_le_of_no_direct value trace hno
  have hcount := additions_count_eq value trace
  simp only [hno, Nat.add_zero] at hcount
  unfold requiredSwaps
  rw [hcount]
  omega

theorem retainedBound_le_swapCount (values : Finset Value) (trace : Trace spills source target)
    (hno : ∀ value ∈ values, directCount value trace = 0) :
    retainedBound values source target trace.additions ≤ trace.swapCount := by
  apply (Finset.sum_le_sum fun value hv =>
    requiredSwaps_le_upwardCount value trace (hno value hv)).trans
  exact sum_upwardCount_le values trace

theorem baseline_add_retainedBound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (values : Finset Value) (trace : Trace spills source target) (he : Eligible missing trace)
    (hno : ∀ value ∈ values, directCount value trace = 0) :
    baseline costs weights spills source missing +
      costs.swap.score weights * retainedBound values source target missing ≤
        (traceCost costs trace).score weights := by
  have hbound := retainedBound_le_swapCount values trace hno
  rw [he.2] at hbound
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ hbound) _).trans
    (baseline_add_swapCost_le_score_of_eligible costs weights trace he)

theorem directCount_eq_zero_of_not_free (value : Value) (trace : Trace spills source target)
    (hfree : ¬Shuffler.Placement.Free spills value) : directCount value trace = 0 := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ _ ih | Dup _ _ _ _ _ ih | Pop _ _ ih => exact ih
  | Push added hf trace ih =>
      have hne : added ≠ value := by
        intro he
        exact hfree (Or.inl (he ▸ hf))
      simp [directCount, ih, hne]
  | Load id hs trace ih =>
      have hne : Value.Var id ≠ value := by
        intro he
        apply hfree
        rw [← he]
        exact Or.inr hs
      simp [directCount, ih, hne]

theorem weightedOptimal_of_score_eq_retainedBound
    (costs : PrimitiveCosts) (weights : Weights) (values : Finset Value)
    (hfree : ∀ value ∈ values, ¬Shuffler.Placement.Free spills value)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (heq : (traceCost costs trace).score weights = baseline costs weights spills source missing +
      costs.swap.score weights * retainedBound values source target missing) :
    WeightedOptimal costs weights missing trace := by
  refine ⟨he, fun other ho => ?_⟩
  rw [heq]
  apply baseline_add_retainedBound_le_score costs weights values other ho
  intro value hv
  exact directCount_eq_zero_of_not_free value other (hfree value hv)

end Shuffler.Optimality.Lineage
