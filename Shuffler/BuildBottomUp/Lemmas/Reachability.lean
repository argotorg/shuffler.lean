import Shuffler.BuildBottomUp.Lemmas.HelperProofs

-- These equations do not depend on the order of the two subtractions in the
-- implementation of offsetToDepth.
theorem Stack.offsetToDepth_val (stack : Stack) (pos : Fin stack.length) :
    (stack.offsetToDepth pos).val = stack.length - 1 - pos.val := by
  simp only [Stack.offsetToDepth, Nat.sub_sub, Nat.add_comm]

theorem Stack.isDupReachable_iff_length (stack : Stack) (pos : Fin stack.length) :
    stack.isDupReachable pos ↔ stack.length ≤ pos.val + (MAX_DUP_DEPTH + 1) := by
  change (stack.offsetToDepth pos).val ≤ MAX_DUP_DEPTH ↔ _
  rw [Stack.offsetToDepth_val]
  have := pos.isLt
  omega

theorem Stack.isSwapReachable_iff_length (stack : Stack) (pos : Fin stack.length) :
    stack.isSwapReachable pos ↔ stack.length ≤ pos.val + (MAX_SWAP_DEPTH + 1) := by
  change (stack.offsetToDepth pos).val ≤ MAX_SWAP_DEPTH ↔ _
  rw [Stack.offsetToDepth_val]
  have := pos.isLt
  omega

namespace Shuffler.BuildBottomUp

theorem shallowestCopyPosition_ge (stack : Stack) (slot : Value)
    (copy pos : Fin stack.length) (hcopy : stack.shallowestCopyPosition slot = some copy)
    (hpos : stack[pos] = slot) : pos.val ≤ copy.val := by
  obtain ⟨_, i, hi, heq, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hcopy
  have hi' : i < stack.length := by simpa using hi
  have hval : stack.length - 1 - i = copy.val := by
    simpa using congrArg Fin.val heq
  by_contra hn
  have hj : stack.length - 1 - pos.val < i := by have := pos.isLt; omega
  have hb := hbefore (stack.length - 1 - pos.val) hj
  have hidx : stack.length - 1 - (stack.length - 1 - pos.val) = pos.val := by
    have := pos.isLt; omega
  simp [hidx, hpos] at hb

theorem _root_.Stack.hasCopy.shallowest {stack : Stack} {slot : Value} (h : Stack.hasCopy stack slot) :
    ∃ copy, stack.shallowestCopyPosition slot = some copy ∧ stack.isDupReachable copy := by
  obtain ⟨pos, hpos, hreach⟩ := h
  have hav : (stack.shallowestCopyPosition slot).isSome :=
    (Stack.shallowestCopyPosition_isSome stack slot).mpr (hpos ▸ List.getElem_mem pos.isLt)
  obtain ⟨copy, hcopy⟩ := Option.isSome_iff_exists.mp hav
  refine ⟨copy, hcopy, ?_⟩
  have hge := shallowestCopyPosition_ge stack slot copy pos hcopy hpos
  rw [Stack.isDupReachable_iff_length] at hreach ⊢
  omega

theorem State.withinReach.initial {state : State source target spills}
    (hvalid : state.Valid) (hsmall : state.stack.length ≤ MAX_DUP_DEPTH + 1) :
    state.withinReach 0 := by
  refine ⟨by simp only [Nat.sub_zero]; unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *; omega, ?_⟩
  intro dest _
  rcases hvalid.available dest with hfree | hspill | hcopy
  · exact Or.inl hfree
  · exact Or.inr (Or.inl hspill)
  · obtain ⟨copy, hcopy⟩ := Option.isSome_iff_exists.mp hcopy
    refine Or.inr (Or.inr ⟨copy, shallowestCopyPosition_value _ _ _ hcopy, ?_⟩)
    rw [Stack.isDupReachable_iff_length]
    omega

theorem _root_.Stack.hasCopy.swap {stack : Stack} {slot : Value} (h : Stack.hasCopy stack slot)
    (a b : Fin stack.length) (ha : stack.isDupReachable a) (hb : stack.isDupReachable b) :
    Stack.hasCopy (stack.swap a b) slot := by
  obtain ⟨pos, hvalue, hreach⟩ := h
  let pos' : Fin (stack.swap a b).length :=
    ⟨(Equiv.swap a b pos).val, by simp⟩
  refine ⟨pos', ?_, ?_⟩
  · by_cases hpa : pos = a
    · subst pos; simpa [pos', List.getElem_swap, a.isLt, b.isLt] using hvalue
    by_cases hpb : pos = b
    · subst pos; simpa [pos', List.getElem_swap, a.isLt, b.isLt] using hvalue
    simpa [pos', Equiv.swap_apply_of_ne_of_ne hpa hpb,
      List.getElem_swap, Fin.val_ne_of_ne hpa, Fin.val_ne_of_ne hpb] using hvalue
  · by_cases hpa : pos = a
    · subst pos; simpa [pos', Stack.isDupReachable, Stack.offsetToDepth] using hb
    by_cases hpb : pos = b
    · subst pos; simpa [pos', Stack.isDupReachable, Stack.offsetToDepth] using ha
    simpa [pos', Stack.isDupReachable, Stack.offsetToDepth,
      Equiv.swap_apply_of_ne_of_ne hpa hpb] using hreach

theorem State.withinReach.advance {state : State source target spills}
    (h : state.withinReach cursor) : state.withinReach (cursor + 1) :=
  ⟨by have := h.width; omega, h.copies⟩

theorem State.withinReach.retag {state : State source target spills}
    (h : state.withinReach cursor) (a b : Fin state.stack.length) :
    State.withinReach cursor { state with mapping := state.mapping.swapDestinations a b } := by
  refine ⟨h.width, ?_⟩
  intro dest hd
  apply h.copies dest
  simpa [State.positionOf] using hd

theorem State.withinReach.swap {state next : State source target spills}
    (h : state.withinReach cursor) (pos : Fin state.stack.length)
    (hpos : cursor ≤ pos.val) (hs : Swapped state next pos) : next.withinReach cursor := by
  refine ⟨by rw [hs.size]; exact h.width, ?_⟩
  intro dest hd
  rcases h.copies dest ((hs.unbound dest).mp hd) with hfree | hspill | hcopy
  · exact Or.inl hfree
  · exact Or.inr (Or.inl hspill)
  · apply Or.inr ∘ Or.inr
    rw [hs.stack_eq]
    apply hcopy.swap pos ⟨state.stack.length - 1, top_lt_length state.stack pos⟩
    · have := h.width
      rw [Stack.isDupReachable_iff_length]
      unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
      have := pos.isLt
      omega
    · rw [Stack.isDupReachable_iff_length]
      change state.stack.length ≤ state.stack.length - 1 + (MAX_DUP_DEPTH + 1)
      omega

theorem State.withinReach.swap_reachable {state : State source target spills}
    (h : state.withinReach cursor) (pos : Fin state.stack.length) (hpos : cursor ≤ pos.val) :
    state.stack.isSwapReachable pos := by
  have := h.width
  rw [Stack.isSwapReachable_iff_length]
  have := pos.isLt
  omega

theorem hasCopy_append_new (stack : Stack) (slot : Value) : Stack.hasCopy (stack ++ [slot]) slot := by
  refine ⟨⟨stack.length, by simp⟩, by simp, ?_⟩
  simp [Stack.isDupReachable, Stack.offsetToDepth]

theorem hasCopy_append_old (stack : Stack) (slot extra : Value) (pos : Fin stack.length)
    (hvalue : stack[pos] = slot) (hdepth : stack.length - pos.val ≤ MAX_DUP_DEPTH) :
    Stack.hasCopy (stack ++ [extra]) slot := by
  refine ⟨⟨pos.val, by have := pos.isLt; simp⟩, ?_, ?_⟩
  · simpa [List.getElem_append_left pos.isLt] using hvalue
  · simp only [Stack.isDupReachable, Stack.offsetToDepth, List.length_append, List.length_singleton]
    omega

theorem hasCopy_append_swap_moved (stack : Stack) (slot extra : Value) (pos : Fin stack.length)
    (hvalue : stack[pos] = slot) :
    Stack.hasCopy ((stack ++ [extra]).swap pos stack.length) slot := by
  refine ⟨⟨stack.length, by simp⟩, ?_, ?_⟩
  · simpa [List.getElem_swap, pos.isLt, Nat.ne_of_gt pos.isLt,
      Nat.ne_of_lt pos.isLt, List.getElem_append_left pos.isLt] using hvalue
  · simp [Stack.isDupReachable, Stack.offsetToDepth]

theorem hasCopy_append_swap_old (stack : Stack) (slot extra : Value) (pos : Fin stack.length)
    (dest : ℕ) (hvalue : stack[pos] = slot)
    (hdepth : stack.length - pos.val ≤ MAX_DUP_DEPTH) :
    Stack.hasCopy ((stack ++ [extra]).swap dest stack.length) slot := by
  by_cases heq : pos.val = dest
  · subst dest; exact hasCopy_append_swap_moved stack slot extra pos hvalue
  refine ⟨⟨pos.val, by have := pos.isLt; simp⟩, ?_, ?_⟩
  · simpa [List.getElem_swap, heq, Nat.ne_of_lt pos.isLt,
      List.getElem_append_left pos.isLt] using hvalue
  · simp only [Stack.isDupReachable, Stack.offsetToDepth, List.length_swap,
      List.length_append, List.length_singleton]
    omega

theorem hasCopy_append_swap_new (stack : Stack) (slot : Value) (dest : ℕ)
    (hdepth : stack.length - dest ≤ MAX_DUP_DEPTH) :
    Stack.hasCopy ((stack ++ [slot]).swap dest stack.length) slot := by
  by_cases hd : dest < (stack ++ [slot]).length
  · refine ⟨⟨dest, by simpa using hd⟩, ?_, ?_⟩
    · simp
    · simp only [Stack.isDupReachable, Stack.offsetToDepth, List.length_swap,
        List.length_append, List.length_singleton]
      omega
  · rw [List.swap_eq_of_ge_left (by omega)]
    exact hasCopy_append_new stack slot

theorem Generation.final_value {state next : State source target spills} {dest : Fin target.length}
    (h : Generation state next dest) (hbound : state.mapping.symm dest = none)
    (hfinal : ∃ h, next.isFinal ⟨dest, h⟩) :
    next.stack[dest.val]'(hfinal.1) = target[dest] := by
  have hb : next.mapping.symm dest = some ⟨dest.val, hfinal.1⟩ :=
    next.boundOfVal _ _ (by simpa [State.exists_isFinal_iff, dest.isLt] using hfinal)
  have he := congrArg (fun stack => stack[dest.val]?) h.expected
  simpa [State.expectedStack, dest.isLt, hb, hbound] using he

-- Before growth, protect a last reachable copy by moving it or making another copy.
def Ready (state : State source target spills) (dest : Fin target.length) : Prop :=
  ∀ j, state.mapping.symm j = none →
    ¬target[j].can_be_freely_generated → ¬spills.is_spilled target[j] →
    ∀ copy, state.stack.shallowestCopyPosition target[j] = some copy →
      (state.stack.offsetToDepth copy).val = MAX_DUP_DEPTH →
      copy.val = dest.val ∨ target[j] = target[dest]

theorem Generation.reachable {state next : State source target spills} {dest : Fin target.length}
    (h : Generation state next dest) (hr : state.withinReach cursor)
    (hcursor : cursor ≤ dest.val) (hready : Ready state dest)
    (hbound : state.mapping.symm dest = none)
    (hfinal : dest.val ≤ state.stack.length → ∃ h, next.isFinal ⟨dest, h⟩) : next.reachable := by
  intro j hj
  have hb := ((h.unbound j).mp hj).2
  by_cases hfree : target[j].can_be_freely_generated
  · exact Or.inl hfree
  by_cases hspill : spills.is_spilled target[j]
  · exact Or.inr (Or.inl hspill)
  apply Or.inr ∘ Or.inr
  have hc : Stack.hasCopy state.stack target[j] := by
    rcases hr.copies j hb with hf | hs | hc
    · contradiction
    · contradiction
    · exact hc
  obtain ⟨copy, hcopy, hreach⟩ := hc.shallowest
  have hv := shallowestCopyPosition_value state.stack target[j] copy hcopy
  have hclt := copy.isLt
  have hdepth : state.stack.length - 1 - copy.val ≤ MAX_DUP_DEPTH := by
    change (state.stack.offsetToDepth copy).val ≤ MAX_DUP_DEPTH at hreach
    rwa [Stack.offsetToDepth_val] at hreach
  by_cases hlast : (state.stack.offsetToDepth copy).val = MAX_DUP_DEPTH
  · have hlast' : state.stack.length - 1 - copy.val = MAX_DUP_DEPTH := by
      rwa [Stack.offsetToDepth_val] at hlast
    have hsafe := hready j hb hfree hspill copy hcopy hlast
    rcases h.stack_eq with hstack | hstack
    · have heq : target[j] = target[dest] := by
        rcases hsafe with hpos | heq
        · have hf := hfinal (by omega)
          have hvalue := h.final_value hbound hf
          have hvalue' : state.stack[copy] = target[dest] := by
            simpa [hstack, ← hpos, List.getElem_append_left copy.isLt] using hvalue
          exact hv.symm.trans hvalue'
        · exact heq
      rw [hstack, heq]
      exact hasCopy_append_new _ _
    · rw [hstack]
      rcases hsafe with hpos | heq
      · simpa only [hpos] using hasCopy_append_swap_moved _ _ target[dest] copy hv
      · by_cases hd : state.stack.length - dest.val ≤ MAX_DUP_DEPTH
        · rw [heq]
          exact hasCopy_append_swap_new _ _ _ hd
        · have hpos : copy.val = dest.val := by
            have := hr.width
            unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
            omega
          simpa only [hpos] using hasCopy_append_swap_moved _ _ target[dest] copy hv
  · have hd : state.stack.length - copy.val ≤ MAX_DUP_DEPTH := by
      rw [Stack.offsetToDepth_val] at hlast
      omega
    rcases h.stack_eq with hstack | hstack
    · rw [hstack]
      exact hasCopy_append_old _ _ _ copy hv hd
    · rw [hstack]
      exact hasCopy_append_swap_old _ _ _ copy _ hv hd

end Shuffler.BuildBottomUp
