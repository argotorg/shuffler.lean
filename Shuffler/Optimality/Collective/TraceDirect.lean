import Shuffler.Optimality.Collective.HeightRelations

namespace Shuffler.Optimality.Collective

open Shuffler.Placement
open Lineage

def TracePrefix.direct (value : Value) (part : TracePrefix spills source target) : Nat :=
  directCount value part.before

theorem takeHeight_direct_le (trace : Trace spills source target) (value : Value) :
    (takeHeight height trace).direct value ≤ directCount value trace := by
  induction trace with
  | Lit => exact Nat.le_refl _
  | Swap _ _ _ _ trace ih | Dup _ _ _ _ trace ih | Pop _ trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      · exact Nat.le_refl _
      · exact ih
  | Push _ _ trace ih | Load _ _ trace ih =>
      simp only [takeHeight]
      split_ifs with hh
      · exact Nat.le_refl _
      · exact ih.trans (Nat.le_add_right _ _)

theorem directBefore_le (trace : Trace spills source target) (value : Value) (cut : Nat) :
    directBefore value cut trace ≤ directCount value trace :=
  takeHeight_direct_le trace value

theorem directBefore_mono (trace : Trace spills source target) (value : Value)
    (horder : low ≤ high) : directBefore value low trace ≤ directBefore value high trace := by
  have he := congrArg (fun part : (current : Stack) × Trace spills source current =>
    directCount value part.2) (takeHeight_nested trace (Nat.add_le_add_right horder 16))
  have hl := takeHeight_direct_le (height := low + 16) (takeHeight (high + 16) trace).before value
  change directCount value (takeHeight (low + 16) (takeHeight (high + 16) trace).before).before =
    directBefore value low trace at he
  change directCount value (takeHeight (low + 16) (takeHeight (high + 16) trace).before).before ≤
    directBefore value high trace at hl
  omega

private theorem mem_drop_swap (stack : Stack) (cut a b : Nat)
    (ha : cut ≤ a) (hb : cut ≤ b) (value : Value) :
    value ∈ (stack.swap a b).drop cut ↔ value ∈ stack.drop cut := by
  have hp := congrArg (List.count value) (take_swap_of_le stack cut a b ha hb)
  have hc := (List.swap_perm stack a b).count_eq value
  have hfirst := congrArg (List.count value) (List.take_append_drop cut (stack.swap a b))
  have hsecond := congrArg (List.count value) (List.take_append_drop cut stack)
  simp only [List.count_append] at hfirst hsecond
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  omega

-- Once a value is absent above a frozen prefix, DUP and SWAP cannot recover
-- it from that prefix. A later occurrence requires a new PUSH or LOAD.
theorem directBefore_lt_of_absent (trace : Trace spills source target) (hpop : trace.noPop)
    (value : Value) (cut : Nat) (hmiss : value ∉ residual cut trace)
    (hfinal : value ∈ target.drop cut) :
    directBefore value cut trace < directCount value trace := by
  induction trace with
  | Lit => exact False.elim (hmiss hfinal)
  | Pop _ _ => exact False.elim hpop
  | @Swap previous depth hlen hlo hhi trace ih =>
      by_cases hh : previous.length ≤ cut + 16
      · have he : residual cut (.Swap depth hlen hlo hhi trace) =
            (previous.swap (previous.length - 1) (previous.length - 1 - depth)).drop cut := by
          simp only [residual, takeHeight, hh, dite_true, TracePrefix.whole]
        exact False.elim (hmiss (he ▸ hfinal))
      · have hprev : value ∈ previous.drop cut :=
          (mem_drop_swap previous cut _ _ (by omega)
            (by unfold MAX_SWAP_DEPTH at hhi; omega) value).mp hfinal
        have hr : residual cut (.Swap depth hlen hlo hhi trace) = residual cut trace := by
          simp only [residual, takeHeight, hh, dite_false]
        have hi := ih hpop (hr ▸ hmiss) hprev
        change (takeHeight (cut + 16) (.Swap depth hlen hlo hhi trace)).direct value < _
        simp only [takeHeight, hh, dite_false]
        exact hi
  | @Dup previous depth hlen hlo hhi trace ih =>
      by_cases hh : previous.length + 1 ≤ cut + 16
      · have he : residual cut (.Dup depth hlen hlo hhi trace) =
            (previous ++ [previous[previous.length - depth]'(by omega)]).drop cut := by
          simp only [residual, takeHeight, hh, dite_true, TracePrefix.whole]
        exact False.elim (hmiss (he ▸ hfinal))
      · have hprev : value ∈ previous.drop cut := by
          rw [List.drop_append_of_le_length (by omega), List.mem_append, List.mem_singleton] at hfinal
          rcases hfinal with hm | he
          · exact hm
          · rw [he]
            apply getElem_mem_drop_of_le previous ⟨previous.length - depth, by omega⟩ cut
            change cut ≤ previous.length - depth
            unfold MAX_DUP_DEPTH at hhi
            omega
        have hr : residual cut (.Dup depth hlen hlo hhi trace) = residual cut trace := by
          simp only [residual, takeHeight, hh, dite_false]
        have hi := ih hpop (hr ▸ hmiss) hprev
        change (takeHeight (cut + 16) (.Dup depth hlen hlo hhi trace)).direct value < _
        simp only [takeHeight, hh, dite_false]
        exact hi
  | @Push previous added hfree trace ih =>
      by_cases hh : previous.length + 1 ≤ cut + 16
      · have he : residual cut (.Push added hfree trace) = (previous ++ [added]).drop cut := by
          simp only [residual, takeHeight, hh, dite_true, TracePrefix.whole]
        exact False.elim (hmiss (he ▸ hfinal))
      · have hr : residual cut (.Push added hfree trace) = residual cut trace := by
          simp only [residual, takeHeight, hh, dite_false]
        change (takeHeight (cut + 16) (.Push added hfree trace)).direct value < _
        simp only [takeHeight, hh, dite_false]
        by_cases he : added = value
        · have hb := directBefore_le trace value cut
          simpa only [directBefore, TracePrefix.direct, directCount, he, ite_true] using Nat.lt_add_one_of_le hb
        · have hprev : value ∈ previous.drop cut := by
            have hc : cut ≤ previous.length := by omega
            simpa only [List.drop_append_of_le_length hc, List.mem_append,
              List.mem_singleton, Ne.symm he, or_false] using hfinal
          have hi := ih hpop (hr ▸ hmiss) hprev
          simpa only [directBefore, TracePrefix.direct, directCount, he, ite_false, Nat.add_zero] using hi
  | @Load previous id hspill trace ih =>
      by_cases hh : previous.length + 1 ≤ cut + 16
      · have he : residual cut (.Load id hspill trace) = (previous ++ [Value.Var id]).drop cut := by
          simp only [residual, takeHeight, hh, dite_true, TracePrefix.whole]
        exact False.elim (hmiss (he ▸ hfinal))
      · have hr : residual cut (.Load id hspill trace) = residual cut trace := by
          simp only [residual, takeHeight, hh, dite_false]
        change (takeHeight (cut + 16) (.Load id hspill trace)).direct value < _
        simp only [takeHeight, hh, dite_false]
        by_cases he : Value.Var id = value
        · have hb := directBefore_le trace value cut
          simpa only [directBefore, TracePrefix.direct, directCount, he, ite_true] using Nat.lt_add_one_of_le hb
        · have hprev : value ∈ previous.drop cut := by
            have hc : cut ≤ previous.length := by omega
            simpa only [List.drop_append_of_le_length hc, List.mem_append,
              List.mem_singleton, Ne.symm he, or_false] using hfinal
          have hi := ih hpop (hr ▸ hmiss) hprev
          simpa only [directBefore, TracePrefix.direct, directCount, he, ite_false, Nat.add_zero] using hi

theorem directBefore_lt_between (trace : Trace spills source target) (hpop : trace.noPop)
    (value : Value) (horder : low ≤ high) (hmiss : value ∉ residual low trace)
    (hfinal : value ∈ (target.take high).drop low) :
    directBefore value low trace < directBefore value high trace := by
  have hn := takeHeight_nested trace (Nat.add_le_add_right horder 16)
  have hc := congrArg Sigma.fst hn
  change (takeHeight (low + 16) (takeHeight (high + 16) trace).before).current =
    (takeHeight (low + 16) trace).current at hc
  have hd := congrArg (fun part : (current : Stack) × Trace spills source current =>
    directCount value part.2) hn
  change directBefore value low (takeHeight (high + 16) trace).before =
    directBefore value low trace at hd
  have hm : value ∉ residual low (takeHeight (high + 16) trace).before := by
    simpa only [residual, hc] using hmiss
  have hf : value ∈ (takeHeight (high + 16) trace).current.drop low := by
    rw [← takeHeight_take (cut := high) trace hpop, List.drop_take] at hfinal
    exact List.mem_of_mem_take hfinal
  have hi := directBefore_lt_of_absent (takeHeight (high + 16) trace).before
    (takeHeight_noPop trace hpop).1 value low hm hf
  change directBefore value low (takeHeight (high + 16) trace).before <
    directBefore value high trace at hi
  omega

end Shuffler.Optimality.Collective
