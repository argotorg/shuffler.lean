import Shuffler.Placement.TraceInvariants
import Shuffler.Placement.Resources

namespace Shuffler.Placement

-- Split a trace at the first operation that increases its length.
private theorem firstGrowth (trace : Trace spills source target)
    (h : trace.noPop) (hne : trace.additions ≠ 0) :
    ∃ (middle : Stack) (value : Value) (before : Trace spills source middle)
      (tail : Trace spills (middle ++ [value]) target),
      before.noPop ∧ before.additions = 0 ∧
      Shuffler.Generate.Available spills middle value ∧ tail.noPop ∧
      trace.additions = {value} + tail.additions := by
  induction trace with
  | Lit => exact False.elim (hne rfl)
  | Pop _ _ => exact False.elim h
  | @Swap prev idx hlen hlo hhi trace ih =>
    obtain ⟨middle, value, before, tail, hp, hz, hv, ht, he⟩ := ih h hne
    exact ⟨middle, value, before, .Swap idx hlen hlo hhi tail, hp, hz, hv, ht, he⟩
  | @Dup prev idx hlen hlo hhi trace ih =>
    by_cases hz : trace.additions = 0
    · refine ⟨prev, prev[prev.length - idx]'(by omega), trace,
        .Lit _, h, hz, Or.inr (Or.inr ?_), by trivial, ?_⟩
      · refine ⟨⟨prev.length - idx, by omega⟩, rfl, ?_⟩
        rw [Stack.isDupReachable_iff_length]
        change prev.length ≤ prev.length - idx + (MAX_DUP_DEPTH + 1)
        omega
      · simp [Trace.additions, hz]
    · obtain ⟨middle, value, before, tail, hp, hzero, hv, ht, he⟩ := ih h hz
      refine ⟨middle, value, before, .Dup idx hlen hlo hhi tail,
        hp, hzero, hv, ht, ?_⟩
      simp only [Trace.additions, he, add_assoc]
  | Push value hfree trace ih =>
    by_cases hz : trace.additions = 0
    · exact ⟨_, value, trace, .Lit _, h, hz, Or.inl hfree, trivial,
        by simp [Trace.additions, hz]⟩
    · obtain ⟨middle, first, before, tail, hp, hzero, hv, ht, he⟩ := ih h hz
      refine ⟨middle, first, before, .Push value hfree tail,
        hp, hzero, hv, ht, ?_⟩
      simp only [Trace.additions, he, add_assoc]
  | Load id hspilled trace ih =>
    by_cases hz : trace.additions = 0
    · exact ⟨_, .Var id, trace, .Lit _, h, hz, Or.inr (Or.inl hspilled), trivial,
        by simp [Trace.additions, hz]⟩
    · obtain ⟨middle, first, before, tail, hp, hzero, hv, ht, he⟩ := ih h hz
      refine ⟨middle, first, before, .Load id hspilled tail,
        hp, hzero, hv, ht, ?_⟩
      simp only [Trace.additions, he, add_assoc]

theorem seeds_le_window (trace : Trace spills source target) (h : trace.noPop) :
    seeds spills trace.additions ≤ (window source : Multiset Value) := by
  apply (seeds_le_iff _ _ _).mpr
  intro value hv hf
  exact (addition_free_or_mem_window trace h hv).resolve_left hf

private theorem available_nonfree_mem_drop {stack : Stack} {value : Value}
    (h : Shuffler.Generate.Available spills stack value) (hf : ¬Free spills value) :
    value ∈ stack.drop (stack.length - (MAX_DUP_DEPTH + 1)) := by
  rcases h with hfree | hspill | ⟨pos, he, hr⟩
  · exact False.elim (hf (Or.inl hfree))
  · exact False.elim (hf (Or.inr hspill))
  · rw [← he]
    apply getElem_mem_drop_of_le
    rw [Stack.isDupReachable_iff_length] at hr
    omega

private theorem window_append (stack : Stack) (value : Value) :
    window (stack ++ [value]) =
      stack.drop (stack.length - (MAX_DUP_DEPTH + 1)) ++ [value] := by
  have hc : frozen (stack ++ [value]) = stack.length - (MAX_DUP_DEPTH + 1) := by
    simp only [frozen, List.length_append, List.length_singleton]
    unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH
    omega
  simp [window, hc, List.drop_append]

theorem CanPlace.reserve (h : CanPlace spills source target missing) :
    Reserve spills source target missing := by
  obtain ⟨trace, ht, rfl⟩ := h
  refine ⟨trace.noPop_balance ht, trace.noPop_frozen ht, ?_⟩
  by_cases hg : trace.additions ≠ 0 ∧ MAX_SWAP_DEPTH + 1 ≤ source.length
  · obtain ⟨middle, value, before, tail, hb, hz, hv, htail, he⟩ :=
      firstGrowth trace ht hg.1
    have hlen : middle.length = source.length := by
      simpa [hz] using before.noPop_length hb
    have hfixed := before.noPop_frozen hb
    have hbalance : (middle : Multiset Value) = (source : Multiset Value) := by
      simpa [hz] using before.noPop_balance hb
    have hi : frozen source < middle.length := by
      unfold frozen MAX_SWAP_DEPTH at *
      omega
    have hcut : frozen (middle ++ [value]) = frozen source + 1 := by
      simp only [frozen, List.length_append, List.length_singleton, hlen]
      unfold MAX_SWAP_DEPTH at *
      omega
    have hcutdup : middle.length - (MAX_DUP_DEPTH + 1) = frozen source + 1 := by
      unfold frozen MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    have htarget : target[frozen source]? = some middle[frozen source] := by
      have hp := tail.noPop_frozen htail
      rw [hcut, List.take_append_of_le_length (by omega)] at hp
      have hx := congrArg (fun stack : Stack => stack[frozen source]?) hp
      simpa [List.getElem?_eq_getElem hi] using hx
    have hfirst : ¬Free spills value → value ∈ middle.drop (frozen source + 1) := by
      intro hf
      simpa [hcutdup] using available_nonfree_mem_drop hv hf
    have hseeds : seeds spills trace.additions ≤
        (middle.drop (frozen source + 1) : Multiset Value) := by
      apply (seeds_le_iff _ _ _).mpr
      intro other ho hf
      rw [he] at ho
      rcases Multiset.mem_add.mp ho with ho | ho
      · have heq := Multiset.mem_singleton.mp ho
        subst other
        exact hfirst hf
      · have hm := (addition_free_or_mem_window tail htail ho).resolve_left hf
        rw [window_append, hcutdup] at hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hm
        · have heq : other = value := by simpa using hm
          subst other
          exact hfirst hf
    have hwindow : (middle.drop (frozen source) : Multiset Value) =
        (window source : Multiset Value) := by
      apply add_left_cancel (a := (source.take (frozen source) : Multiset Value))
      calc
        (source.take (frozen source) : Multiset Value) + middle.drop (frozen source) =
            (middle : Multiset Value) := by rw [← hfixed, Multiset.coe_add, List.take_append_drop]
        _ = (source : Multiset Value) := hbalance
        _ = (source.take (frozen source) : Multiset Value) + window source := by
          rw [Multiset.coe_add, window, List.take_append_drop]
    have hr : {middle[frozen source]} + seeds spills trace.additions ≤
        (middle.drop (frozen source) : Multiset Value) := by
      rw [List.drop_eq_getElem_cons hi]
      change middle[frozen source] ::ₘ seeds spills trace.additions ≤
        middle[frozen source] ::ₘ (middle.drop (frozen source + 1) : Multiset Value)
      exact Multiset.cons_le_cons _ hseeds
    rw [hwindow] at hr
    simpa [boundary, hg, htarget] using hr
  · simpa only [boundary, ite_eq_right hg, zero_add] using seeds_le_window trace ht

end Shuffler.Placement
