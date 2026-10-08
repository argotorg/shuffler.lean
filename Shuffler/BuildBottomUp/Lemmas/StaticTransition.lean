import Shuffler.BuildBottomUp.Lemmas.StaticStepValues
import Shuffler.BuildBottomUp.Lemmas.StaticPreservation
import Shuffler.BuildBottomUp.Lemmas.StaticGrowth
import Shuffler.BuildBottomUp.Lemmas.StaticPrefix
import Shuffler.BuildBottomUp.Lemmas.StaticDeepBound

namespace Shuffler.BuildBottomUp.Success

-- One position before the fixed cutoff either advances by equal-value retagging,
-- or fails because the required value cannot be placed at that depth.
theorem PrefixState.step {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (hn : 16 < initial.stack.length)
    (hc : cursor < cutoff initial) (hr : state.reachable) :
    (((augmentedStack initial)[cursor]? = initial.expectedStack[cursor]?) →
      ∃ next, PrefixState initial h (cursor+1) next ∧
        buildBottomUp.loop cursor state = buildBottomUp.loop (cursor+1) next) ∧
    (((augmentedStack initial)[cursor]? ≠ initial.expectedStack[cursor]?) →
      ¬Succeeds (buildBottomUp.loop cursor state) (fun _ => True)) := by
  obtain ⟨hct, hcs, hpending, hwidth⟩ := hp.before_cutoff hn hc
  let dest : Fin target.length := ⟨cursor,hct⟩
  let current : Fin state.stack.length := ⟨cursor,hcs⟩
  have hsmall : MAX_SWAP_DEPTH ≤ state.stack.length - cursor := by unfold MAX_SWAP_DEPTH; omega
  cases hb : state.mapping.symm dest with
  | some carrier =>
    have hiff := hp.bound_value_iff hct current carrier rfl hb
    constructor
    · intro hequal
      have hv := hiff.mp hequal
      refine ⟨retagged state current carrier, hp.retag hct current carrier rfl hb hv, ?_⟩
      exact loop_equal_bound_eq cursor state hp.invariant hr hsmall hpending hct current rfl carrier hb hv
    · intro hunequal
      have hv : state.stack[current] ≠ state.stack[carrier] := fun he => hunequal (hiff.mpr he)
      have hbound := hp.original_bound hct (by simp [dest, hb])
      have hbefore : cursor < boundary initial := lt_of_lt_of_le hc (Nat.min_le_left _ _)
      have hdeep := prefixWidth_ge_eighteen_of_bound initial h hn dest hbefore hbound
      rw [← hp.length] at hdeep
      exact loop_bound_mismatch_deep_noSuccess cursor state hp.invariant hdeep hct current rfl carrier hb hv
  | none =>
    obtain ⟨produced, hproduce, hg, hm⟩ :=
      produce_success_exact state dest hb (hp.invariant.available dest) hr
    have hgsize := hg.size
    have hcproduced : cursor < produced.stack.length := by omega
    let current' : Fin produced.stack.length := ⟨cursor,hcproduced⟩
    let top : Fin produced.stack.length := ⟨state.stack.length, by omega⟩
    have htop : top.val = produced.stack.length - 1 := by dsimp [top]; omega
    have hbprod : produced.mapping.symm dest = some top := produced.boundOfVal dest top hg.bound
    have hbelow : current'.val + 1 < produced.stack.length := by dsimp [current']; omega
    have hcurrentValue : produced.stack[current'] = state.stack[current] := by
      have he := congrArg (fun stack : Stack => stack[cursor]?) hg.stack_eq
      have he' : some produced.stack[current'] = some state.stack[current] := by
        simpa [List.getElem?_append, hcs, hcproduced, List.getElem?_eq_getElem, current', current] using he
      exact Option.some.inj he'
    have htopValue : produced.stack[top] = target[cursor] := by
      have he := congrArg (fun stack : Stack => stack[state.stack.length]?) hg.stack_eq
      have htopLt : state.stack.length < produced.stack.length := by omega
      have he' : some produced.stack[top] = some target[cursor] := by
        simpa [List.getElem?_append, htopLt, List.getElem?_eq_getElem, top, dest] using he
      exact Option.some.inj he'
    have hiff := hp.hole_value_iff hct current rfl hb
    constructor
    · intro hequal
      have hv : produced.stack[current'] = produced.stack[top] :=
        hcurrentValue.trans ((hiff.mp hequal).trans htopValue.symm)
      let next := retagged produced current' top
      have hnext : PrefixState initial h (cursor+1) next :=
        hp.produced_retag hct hb hg hm current' top rfl hbprod hv
      have hgenerate : state.generate cursor = .ok next :=
        generate_eq_after_produce_equal state produced dest hproduce current' top rfl htop hbelow hbprod hv
      have hfinal : ∃ h, next.isFinal ⟨cursor, h⟩ := hnext.invariant.processed dest (by dsimp [dest]; omega)
      exact ⟨next, hnext, loop_hole_eq_of_generate_final cursor state next hr hsmall hpending hct hb hgenerate hfinal⟩
    · intro hunequal
      have hv : produced.stack[current'] ≠ produced.stack[top] := by
        intro he
        apply hunequal
        apply hiff.mpr
        exact hcurrentValue.symm.trans (he.trans htopValue)
      have hdeep : ¬produced.stack.isSwapReachable current' := by
        rw [Stack.isSwapReachable_iff_length]
        change ¬produced.stack.length ≤ cursor + (MAX_SWAP_DEPTH + 1)
        unfold MAX_SWAP_DEPTH
        omega
      have hgenerate := generate_eq_after_produce_unequal_deep state produced dest hproduce
        current' top rfl htop hbelow hbprod hv hdeep
      have hnf : ¬ ∃ h, produced.isFinal ⟨cursor, h⟩ := by
        rw [produced.isFinal_of_bound_iff dest top hbprod]
        dsimp [top, dest]
        omega
      exact loop_hole_blocks_of_generate_deep cursor state produced hr hsmall hpending hct hb
        hgenerate hnf current' rfl hbelow hdeep

end Shuffler.BuildBottomUp.Success
