import Shuffler.BuildBottomUp.Lemmas.NecessityProofs
import Shuffler.BuildBottomUp.Lemmas.StaticPrefix

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Shuffler.BuildBottomUp

-- Both witnesses are copies in DUP reach, not merely copies somewhere on the stack.
def TwoCopies (stack : Stack) (slot : Value) : Prop :=
  ∃ i j : Fin stack.length, i ≠ j ∧ stack[i] = slot ∧ stack[j] = slot ∧
    stack.isDupReachable i ∧ stack.isDupReachable j

def NeedsDup (state : State source target spills) (slot : Value) : Prop :=
  ∃ dest, state.mapping.symm dest = none ∧ target[dest] = slot ∧
    ¬slot.can_be_freely_generated ∧ ¬spills.is_spilled slot

theorem TwoCopies.swap {stack : Stack} {slot : Value} (h : TwoCopies stack slot)
    (a b : Fin stack.length) (ha : stack.isDupReachable a) (hb : stack.isDupReachable b) :
    TwoCopies (stack.swap a b) slot := by
  let move (pos : Fin stack.length) : Fin (stack.swap a b).length :=
    ⟨(Equiv.swap a b pos).val, by simp⟩
  have value (pos : Fin stack.length) (hv : stack[pos] = slot) :
      (stack.swap a b)[move pos] = slot := by
    by_cases hpa : pos = a
    · subst pos; simpa [move, List.getElem_swap, a.isLt, b.isLt] using hv
    by_cases hpb : pos = b
    · subst pos; simpa [move, List.getElem_swap, a.isLt, b.isLt] using hv
    simpa [move, Equiv.swap_apply_of_ne_of_ne hpa hpb, List.getElem_swap,
      Fin.val_ne_of_ne hpa, Fin.val_ne_of_ne hpb] using hv
  have reach (pos : Fin stack.length) (hr : stack.isDupReachable pos) :
      Stack.isDupReachable (stack.swap a b) (move pos) := by
    by_cases hpa : pos = a
    · subst pos; simpa [move, Stack.isDupReachable, Stack.offsetToDepth] using hb
    by_cases hpb : pos = b
    · subst pos; simpa [move, Stack.isDupReachable, Stack.offsetToDepth] using ha
    simpa [move, Stack.isDupReachable, Stack.offsetToDepth,
      Equiv.swap_apply_of_ne_of_ne hpa hpb] using hr
  obtain ⟨i, j, hne, hi, hj, hri, hrj⟩ := h
  refine ⟨move i, move j, ?_, value i hi, value j hj, reach i hri, reach j hrj⟩
  intro heq
  apply hne
  apply (Equiv.swap a b).injective
  apply Fin.ext
  exact congrArg (fun p : Fin (stack.swap a b).length => p.val) heq

theorem twoCopies_swap_iff (stack : Stack) (slot : Value) (a b : Fin stack.length)
    (ha : stack.isDupReachable a) (hb : stack.isDupReachable b) :
    TwoCopies (stack.swap a b) slot ↔ TwoCopies stack slot := by
  constructor
  · intro hs
    have h := hs.swap (⟨a.val, by simp⟩) (⟨b.val, by simp⟩)
      (by simpa [Stack.isDupReachable, Stack.offsetToDepth] using ha)
      (by simpa [Stack.isDupReachable, Stack.offsetToDepth] using hb)
    simpa using h
  · intro hs; exact hs.swap a b ha hb

theorem hasCopy_swap_out_iff_twoCopies (stack : Stack) (bottom top : Fin stack.length)
    (hb : ¬stack.isDupReachable bottom) (ht : stack.isDupReachable top)
    (hv : stack[bottom] ≠ stack[top]) :
    HasCopy (stack.swap bottom top) stack[top] ↔ TwoCopies stack stack[top] := by
  have hbt : bottom ≠ top := by intro heq; subst top; exact hb ht
  constructor
  · rintro ⟨pos, hvalue, hreach⟩
    let old : Fin stack.length := ⟨pos.val, by simpa using pos.isLt⟩
    have hro : stack.isDupReachable old := by
      simpa [Stack.isDupReachable, Stack.offsetToDepth, old] using hreach
    have hob : old ≠ bottom := by intro heq; exact hb (heq ▸ hro)
    have hot : old ≠ top := by
      intro heq
      have hv' : stack[bottom] = stack[top] := by
        simpa [List.getElem_swap, ← heq, old, Fin.val_ne_of_ne hbt] using hvalue
      exact hv hv'
    have hvo : stack[old] = stack[top] := by
      simpa [List.getElem_swap, old, Fin.val_ne_of_ne hob, Fin.val_ne_of_ne hot] using hvalue
    exact ⟨old, top, hot, hvo, rfl, hro, ht⟩
  · rintro ⟨i, j, hij, hi, hj, hri, hrj⟩
    have witness : ∃ pos : Fin stack.length, pos ≠ top ∧ stack[pos] = stack[top] ∧
        stack.isDupReachable pos := by
      by_cases hit : i = top
      · exact ⟨j, by intro hjt; exact hij (hit.trans hjt.symm), hj, hrj⟩
      · exact ⟨i, hit, hi, hri⟩
    obtain ⟨pos, hpt, hpv, hpr⟩ := witness
    have hpb : pos ≠ bottom := by intro heq; subst pos; exact hb hpr
    refine ⟨⟨pos.val, by simp⟩, ?_, ?_⟩
    · simpa [List.getElem_swap, Fin.val_ne_of_ne hpb, Fin.val_ne_of_ne hpt] using hpv
    · simpa [Stack.isDupReachable, Stack.offsetToDepth] using hpr

theorem HasCopy.swap_out_other {stack : Stack} {slot : Value} (h : HasCopy stack slot)
    (bottom top : Fin stack.length) (hb : ¬stack.isDupReachable bottom)
    (hv : slot ≠ stack[top]) : HasCopy (stack.swap bottom top) slot := by
  obtain ⟨pos, hvalue, hreach⟩ := h
  have hpb : pos ≠ bottom := by intro heq; subst pos; exact hb hreach
  have hpt : pos ≠ top := by intro heq; subst pos; exact hv hvalue.symm
  refine ⟨⟨pos.val, by simp⟩, ?_, ?_⟩
  · simpa [List.getElem_swap, Fin.val_ne_of_ne hpb, Fin.val_ne_of_ne hpt] using hvalue
  · simpa [Stack.isDupReachable, Stack.offsetToDepth] using hreach

theorem Swapped.reachable_boundary_iff {state next : State source target spills}
    (bottom : Fin state.stack.length) (hs : Swapped state next bottom)
    (hr : Reachable state) (hb : ¬state.stack.isDupReachable bottom)
    (hv : state.stack[bottom] ≠ state.stack[state.stack.length - 1]'(by have := bottom.isLt; omega)) :
    Reachable next ↔
      ¬NeedsDup state (state.stack[state.stack.length - 1]'(by have := bottom.isLt; omega)) ∨
      TwoCopies state.stack (state.stack[state.stack.length - 1]'(by have := bottom.isLt; omega)) := by
  let top : Fin state.stack.length := ⟨state.stack.length - 1, by have := bottom.isLt; omega⟩
  have ht : state.stack.isDupReachable top := by
    simp [Stack.isDupReachable, Stack.offsetToDepth_val, top]
  have hcopy : HasCopy next.stack state.stack[top] ↔ TwoCopies state.stack state.stack[top] := by
    rw [hs.stack_eq]
    exact hasCopy_swap_out_iff_twoCopies state.stack bottom top hb ht hv
  constructor
  · intro hn
    by_cases hneed : NeedsDup state state.stack[top]
    · apply Or.inr
      apply hcopy.mp
      obtain ⟨dest, hd, hvalue, hfree, hspill⟩ := hneed
      have hrn := hn dest ((hs.unbound dest).mpr hd)
      rw [hvalue] at hrn
      exact hrn.resolve_left hfree |>.resolve_left hspill
    · exact Or.inl hneed
  · intro hsafe dest hd
    have hd' := (hs.unbound dest).mp hd
    by_cases hfree : target[dest].can_be_freely_generated
    · exact Or.inl hfree
    by_cases hspill : spills.is_spilled target[dest]
    · exact Or.inr (Or.inl hspill)
    apply Or.inr ∘ Or.inr
    by_cases heq : target[dest] = state.stack[top]
    · rw [heq]
      apply hcopy.mpr
      rcases hsafe with hnone | htwo
      · exact False.elim (hnone ⟨dest, hd', heq, heq ▸ hfree, heq ▸ hspill⟩)
      · exact htwo
    · have hc : HasCopy state.stack target[dest] :=
        (hr dest hd').resolve_left hfree |>.resolve_left hspill
      rw [hs.stack_eq]
      exact hc.swap_out_other bottom top hb heq

theorem NeedsDup.retag_iff (state : State source target spills)
    (a b : Fin state.stack.length) (slot : Value) :
    NeedsDup { state with mapping := state.mapping.swapDestinations a b } slot ↔
      NeedsDup state slot := by
  simp [NeedsDup]

theorem Swapped.needsDup_iff {state next : State source target spills}
    {pos : Fin state.stack.length} (hs : Swapped state next pos) (slot : Value) :
    NeedsDup next slot ↔ NeedsDup state slot := by
  unfold NeedsDup
  simp only [hs.unbound]

theorem Swapped.twoCopies_iff {state next : State source target spills}
    {pos : Fin state.stack.length} (hs : Swapped state next pos)
    (hp : state.stack.isDupReachable pos) (slot : Value) :
    TwoCopies next.stack slot ↔ TwoCopies state.stack slot := by
  rw [hs.stack_eq]
  apply twoCopies_swap_iff state.stack slot pos
    ⟨state.stack.length - 1, top_lt_length state.stack pos⟩ hp
  simp [Stack.isDupReachable, Stack.offsetToDepth_val]

theorem Placement.boundary_finish_success_iff {state : State source target spills}
    {dest : Fin target.length} (h : Placement dest state) (hr : Reachable state)
    (hw : state.stack.length - dest.val = MAX_SWAP_DEPTH + 1)
    (hnfinal : ¬state.isFinal dest)
    (hv : state.stack[dest.val]'h.in_bounds ≠
      state.stack[state.stack.length - 1]'(by have := h.in_bounds; omega)) :
    Success ((swapWith dest.val).exec state >>= fun next =>
      buildBottomUp.loop (dest.val + 1) next) (fun _ => True) ↔
      ¬NeedsDup state (state.stack[state.stack.length - 1]'(by have := h.in_bounds; omega)) ∨
      TwoCopies state.stack (state.stack[state.stack.length - 1]'(by have := h.in_bounds; omega)) := by
  let bottom : Fin state.stack.length := ⟨dest.val, h.in_bounds⟩
  have hbelow : bottom.val + 1 < state.stack.length := by
    dsimp [bottom]
    unfold MAX_SWAP_DEPTH at hw
    omega
  have hswap : state.stack.isSwapReachable bottom := by
    rw [Stack.isSwapReachable_iff_length]
    dsimp [bottom]
    omega
  have hdup : ¬state.stack.isDupReachable bottom := by
    rw [Stack.isDupReachable_iff_length]
    dsimp [bottom]
    unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
    omega
  obtain ⟨next, heq, hs⟩ := swap_success state bottom hbelow hswap hnfinal
  have hi := (hs.invariant h.toInvariant le_rfl).advance
    (hs.final dest rfl (h.position.resolve_left hnfinal))
  have hw' : next.stack.length - (dest.val + 1) ≤ MAX_SWAP_DEPTH := by
    rw [hs.size]
    omega
  rw [heq, except_ok_bind, loop_success_iff_reachable_within_width _ _ hi hw']
  exact hs.reachable_boundary_iff bottom hr hdup hv

macro "finish_boundary " c:term ", " st:term ", " hp:term ", " hn:term ", " hr:term ", " hw:term ", " hv:term ", " hc:term : tactic => `(tactic| (
  try simp_action
  try rw [ensure_of_true _ $hn]
  try simp only [not_false_eq_true, ensure_of_true True True.intro, except_ok_bind,
    except_error_bind, pure_bind, bind_assoc]
  have hnotTop : $c ≠ ($st).stack.length - 1 := by
    have hwidth := $hw
    unfold MAX_SWAP_DEPTH at hwidth
    omega
  try dsimp +zetaDelta only at hnotTop
  try simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
  let bottom : Fin ($st).stack.length := ⟨$c, ($hp).in_bounds⟩
  try simp_action
  rw [isSwapReachable_index $st bottom]
  have hreach : ($st).stack.isSwapReachable bottom := by
    rw [Stack.isSwapReachable_iff_length]
    change ($st).stack.length ≤ $c + (MAX_SWAP_DEPTH + 1)
    have hwidth := $hw
    omega
  simp only [hreach, decide_true, not_true_eq_false, ↓reduceIte, except_ok_bind]
  try simp_action
  exact (($hp).boundary_finish_success_iff $hr $hw $hn $hv).trans $hc))

theorem loop_bound_mismatch_boundary_success_iff (cursor : Nat)
    (state : State source target spills) (inv : Invariant cursor state) (hr : Reachable state)
    (hw : state.stack.length - cursor = MAX_SWAP_DEPTH + 1)
    (hpending : state.pending_generations ≠ 0) (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (carrier : Fin state.stack.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier)
    (hv : state.stack[current] ≠ state.stack[carrier]) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) ↔
      ¬NeedsDup state state.stack[carrier] ∨ TwoCopies state.stack state.stack[carrier] := by
  let dest : Fin target.length := ⟨cursor, hc⟩
  have hge := inv.processed.bound_ge dest carrier hb le_rfl
  have hnfinal : ¬state.isFinal cursor := by
    intro hf
    have hv' := (state.isFinal_of_bound_iff dest carrier hb).mp hf
    have heq : carrier = current := Fin.ext (hv'.trans hcurrent.symm)
    exact hv (heq ▸ rfl)
  have hnotearly : ¬state.stack.length - cursor < MAX_SWAP_DEPTH := by omega
  rw [buildBottomUp.loop.eq_def]
  try simp_action
  simp only [hc, ↓reduceIte, hnfinal, and_false, hpending]
  rw [StateT.run_bind]
  have hscan := Success.of_triple _ _ _ (urgentScan_success cursor state hr)
  simp only [bind_pure] at hscan
  obtain ⟨⟨urgent, next⟩, heq, _, hnext⟩ := hscan
  dsimp only at hnext
  subst next
  simp only [StateT.run] at heq ⊢
  erw [heq]
  simp only [except_ok_bind, hnotearly, and_false, ↓reduceDIte, ↓reduceIte]
  have hposition : state.positionOf cursor = some carrier.val := by
    simp [State.positionOf, hc, hb]
  rw [hposition]
  change Success (StateT.run (s := state) _) _ ↔ _
  try simp_action
  rw [ensure_of_true _ hge]
  simp only [except_ok_bind]
  have hslot : slotAt state.stack cursor = .ok state.stack[current] :=
    hcurrent ▸ slotAt_index state.stack current
  rw [hslot, slotAt_index state.stack carrier]
  try simp_action
  simp only [hv, ↓reduceIte]
  rw [depthOf_index state carrier]
  simp only [except_ok_bind]
  have hcopies := Success.of_triple _ _ _ (copyScan_success state carrier carrier.val
    ⟨carrier, rfl, rfl, state.boundNotFinal_of_not_final dest carrier hb hnfinal⟩)
  simp only [bind_pure, slotAt_index state.stack carrier] at hcopies
  rw [StateT.run_bind]
  obtain ⟨⟨selected, next⟩, heq, hselected, hnext⟩ := hcopies
  dsimp only at hselected hnext
  subst next
  simp only [StateT.run] at heq ⊢
  erw [heq]
  simp only [except_ok_bind]
  obtain ⟨pos, rfl, hequal, hmovable⟩ := hselected
  change Success (StateT.run (s := state) _) _ ↔ _
  rw [slotAt_index state.stack pos]
  try simp_action
  rw [ensure_of_true _ hequal]
  try simp_action
  rw [swapDestinations_result state pos carrier]
  try simp_action
  let retag := { state with mapping := state.mapping.swapDestinations pos carrier }
  have hip : Invariant cursor retag := inv.retag pos carrier
    (inv.not_final_ge pos hmovable) hge
  have hd : retag.mapping.symm dest = some pos := by simp [retag, dest, hb]
  have hnotcurrent : pos.val ≠ cursor := by
    intro heq
    have hpos : pos = current := Fin.ext (heq.trans hcurrent.symm)
    exact hv (hpos ▸ hequal)
  simp only [hnotcurrent, ↓reduceIte]
  have hposreach : retag.stack.isDupReachable pos := by
    have := inv.not_final_ge pos hmovable
    rw [Stack.isDupReachable_iff_length]
    change state.stack.length ≤ pos.val + (MAX_DUP_DEPTH + 1)
    unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
    omega
  have hrr : WithinReach (cursor + 1) retag := by
    refine ⟨?_, ?_⟩
    · change state.stack.length - (cursor + 1) ≤ MAX_SWAP_DEPTH
      omega
    · intro j hj
      exact hr j (by simpa [retag] using hj)
  by_cases hnotTop : pos.val ≠ retag.stack.length - 1
  · dsimp +zetaDelta only at hnotTop
    simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    rw [isSwapReachable_index retag pos]
    have hreach : retag.stack.isSwapReachable pos := by
      rw [Stack.isSwapReachable_iff_length]
      rw [Stack.isDupReachable_iff_length] at hposreach
      unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
      omega
    simp only [hreach, decide_true, not_true_eq_false, ↓reduceIte, except_ok_bind]
    try simp_action
    have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
    obtain ⟨next, heq, hs⟩ := swap_success retag pos hbelow hreach
      (retag.boundNotFinal dest pos hd hnotcurrent)
    rw [heq, except_ok_bind]
    have hgepos : cursor ≤ pos.val := inv.not_final_ge pos hmovable
    have htop := hs.bound_top dest hd
    have hp : Placement dest next := ⟨hs.invariant hip hgepos,
      by
        change cursor < next.stack.length
        have hlen := hs.size
        have := current.isLt
        dsimp [retag] at hlen
        omega, Or.inr htop⟩
    have hwidth : next.stack.length - cursor = MAX_SWAP_DEPTH + 1 := by
      rw [hs.size]; exact hw
    have hnf : ¬next.isFinal dest := by
      apply (next.isFinal_of_bound_val_iff dest _ htop).not.mpr
      dsimp [dest]
      unfold MAX_SWAP_DEPTH at hwidth
      omega
    have hcopy : Reachable next := (hrr.swap pos (by omega) hs).copies
    have htopvalue : next.stack[next.stack.length - 1]'(by have := hp.in_bounds; omega) =
        state.stack[carrier] := by
      simp only [hs.stack_eq, List.length_swap]
      simpa using hequal
    have hbottomvalue : next.stack[dest.val]'hp.in_bounds = state.stack[current] := by
      simp only [hs.stack_eq]
      have hct : cursor ≠ retag.stack.length - 1 := by
        change cursor ≠ state.stack.length - 1
        unfold MAX_SWAP_DEPTH at hw
        omega
      have hcp : current.val ≠ pos.val := by omega
      have hct' : current.val ≠ state.stack.length - 1 := by simpa [retag, hcurrent] using hct
      simp [retag, dest, ← hcurrent, hcp, hct']
    have hneq : next.stack[dest.val]'hp.in_bounds ≠
        next.stack[next.stack.length - 1]'(by have := hp.in_bounds; omega) := by
      rw [hbottomvalue, htopvalue]
      exact hv
    have hcondition :
        (¬NeedsDup next (next.stack[next.stack.length - 1]'(by have := hp.in_bounds; omega)) ∨
          TwoCopies next.stack (next.stack[next.stack.length - 1]'(by have := hp.in_bounds; omega))) ↔
        (¬NeedsDup state state.stack[carrier] ∨ TwoCopies state.stack state.stack[carrier]) := by
      rw [htopvalue, hs.needsDup_iff, hs.twoCopies_iff hposreach, NeedsDup.retag_iff]
    finish_boundary cursor, next, hp, hnf, hcopy, hwidth, hneq, hcondition
  · dsimp +zetaDelta only at hnotTop
    simp only [ne_eq, hnotTop, ↓reduceIte]
    have hp := hip.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hnotcurrent
    have hwidth : retag.stack.length - cursor = MAX_SWAP_DEPTH + 1 := hw
    have htopvalue : retag.stack[retag.stack.length - 1]'(by have := current.isLt; dsimp [retag] at *; omega) =
        state.stack[carrier] := by
      have hpos := not_not.mp hnotTop
      change state.stack[state.stack.length - 1] = state.stack[carrier]
      simpa only [← hpos, Fin.getElem_fin] using hequal
    have hneq : retag.stack[dest.val]'hp.1.in_bounds ≠
        retag.stack[retag.stack.length - 1]'(by have := hp.1.in_bounds; omega) := by
      rw [htopvalue]
      simpa [dest, ← hcurrent] using hv
    have hcondition :
        (¬NeedsDup retag (retag.stack[retag.stack.length - 1]'(by have := hp.1.in_bounds; omega)) ∨
          TwoCopies retag.stack (retag.stack[retag.stack.length - 1]'(by have := hp.1.in_bounds; omega))) ↔
        (¬NeedsDup state state.stack[carrier] ∨ TwoCopies state.stack state.stack[carrier]) := by
      rw [htopvalue, NeedsDup.retag_iff]
    finish_boundary cursor, retag, hp.1, hp.2, hrr.copies, hwidth, hneq, hcondition

theorem loop_bound_boundary_success_iff (cursor : Nat)
    (state : State source target spills) (inv : Invariant cursor state)
    (hw : state.stack.length - cursor = MAX_SWAP_DEPTH + 1)
    (hpending : state.pending_generations ≠ 0) (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (carrier : Fin state.stack.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) ↔
      Reachable state ∧ (state.stack[current] = state.stack[carrier] ∨
        ¬NeedsDup state state.stack[carrier] ∨ TwoCopies state.stack state.stack[carrier]) := by
  constructor
  · intro hs
    have hr := loop_success_requires_reachable cursor state inv hs
    refine ⟨hr, ?_⟩
    by_cases hv : state.stack[current] = state.stack[carrier]
    · exact Or.inl hv
    · exact Or.inr ((loop_bound_mismatch_boundary_success_iff cursor state inv hr hw
        hpending hc current hcurrent carrier hb hv).mp hs)
  · rintro ⟨hr, hsafe⟩
    by_cases hv : state.stack[current] = state.stack[carrier]
    · rw [loop_equal_bound_eq cursor state inv hr (by omega) hpending hc
        current hcurrent carrier hb hv]
      let next := { state with mapping := state.mapping.swapDestinations current carrier }
      have hge := inv.processed.bound_ge ⟨cursor, hc⟩ carrier hb le_rfl
      have hi : Invariant cursor next := inv.retag current carrier (by omega) hge
      have hd : next.mapping.symm ⟨cursor, hc⟩ = some current := by simp [next, hb]
      have hf : next.isFinal cursor :=
        (next.isFinal_of_bound_iff ⟨cursor, hc⟩ current hd).mpr hcurrent
      apply loop_success (cursor + 1) next (hi.advance hf)
      refine ⟨?_, ?_⟩
      · change state.stack.length - (cursor + 1) ≤ MAX_SWAP_DEPTH
        omega
      · intro j hj
        exact hr j (by simpa [next] using hj)
    · exact (loop_bound_mismatch_boundary_success_iff cursor state inv hr hw
        hpending hc current hcurrent carrier hb hv).mpr (hsafe.resolve_left hv)

end Shuffler.BuildBottomUp
