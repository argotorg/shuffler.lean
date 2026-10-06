import Shuffler.BuildBottomUp.Lemmas.StaticBoundary
import Shuffler.BuildBottomUp.Lemmas.StaticTerminal

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Shuffler.BuildBottomUp

macro "finish_deep_bound " c:term ", " st:term ", " hw:term : tactic => `(tactic| (
  try simp_action
  by_cases hnfinal : ¬($st).isFinal $c
  · rw [ensure_of_true _ hnfinal]
    try simp_action
    have hnotTop : $c ≠ ($st).stack.length - 1 := by
      have hwidth := $hw
      unfold MAX_SWAP_DEPTH at hwidth
      omega
    try dsimp +zetaDelta only at hnotTop
    try simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    let bottom : Fin ($st).stack.length := ⟨$c, by
      have hwidth := $hw
      unfold MAX_SWAP_DEPTH at hwidth
      omega⟩
    try simp_action
    rw [isSwapReachable_index $st bottom]
    have hreach : ¬($st).stack.isSwapReachable bottom := by
      rw [Stack.isSwapReachable_iff_length]
      change ¬($st).stack.length ≤ $c + (MAX_SWAP_DEPTH + 1)
      have hwidth := $hw
      omega
    simp only [hreach, decide_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, except_ok_bind]
    try simp_action
    rw [depthOf_index $st bottom]
    try simp_action
    simp [Success]
  · have he : ensure (¬($st).isFinal $c) "target slot is already final" =
        .error (.assertion "target slot is already final") := by
      unfold ensure requires
      simp only [hnfinal, ↓reduceDIte]
      rfl
    rw [he]
    try simp_action
    simp [Success]))

theorem loop_bound_mismatch_deep_noSuccess_of_reachable (cursor : Nat)
    (state : State source target spills) (inv : Invariant cursor state) (hr : Reachable state)
    (hw : MAX_SWAP_DEPTH + 2 ≤ state.stack.length - cursor)
    (hpending : state.pending_generations ≠ 0) (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (carrier : Fin state.stack.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier)
    (hv : state.stack[current] ≠ state.stack[carrier]) :
    ¬Success (buildBottomUp.loop cursor state) (fun _ => True) := by
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
  change ¬Success (StateT.run (s := state) _) _
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
  change ¬Success (StateT.run (s := state) _) _
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
  by_cases hnotTop : pos.val ≠ retag.stack.length - 1
  · dsimp +zetaDelta only at hnotTop
    simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    rw [isSwapReachable_index retag pos]
    by_cases hreach : retag.stack.isSwapReachable pos
    · simp only [hreach, decide_true, not_true_eq_false, ↓reduceIte, except_ok_bind]
      try simp_action
      have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
      obtain ⟨next, heq, hs⟩ := swap_success retag pos hbelow hreach
        (retag.boundNotFinal dest pos hd hnotcurrent)
      rw [heq, except_ok_bind]
      have hwidth : MAX_SWAP_DEPTH + 2 ≤ next.stack.length - cursor := by
        rw [hs.size]; exact hw
      finish_deep_bound cursor, next, hwidth
    · simp only [hreach, decide_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, except_ok_bind]
      try simp_action
      rw [depthOf_index retag pos]
      try simp_action
      simp [Success]
  · dsimp +zetaDelta only at hnotTop
    simp only [ne_eq, hnotTop, ↓reduceIte]
    have hwidth : MAX_SWAP_DEPTH + 2 ≤ retag.stack.length - cursor := hw
    finish_deep_bound cursor, retag, hwidth

theorem loop_bound_mismatch_deep_noSuccess_of_pending (cursor : Nat)
    (state : State source target spills) (inv : Invariant cursor state)
    (hw : MAX_SWAP_DEPTH + 2 ≤ state.stack.length - cursor)
    (hpending : state.pending_generations ≠ 0) (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (carrier : Fin state.stack.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier)
    (hv : state.stack[current] ≠ state.stack[carrier]) :
    ¬Success (buildBottomUp.loop cursor state) (fun _ => True) := by
  intro hs
  have hr := loop_success_requires_reachable cursor state inv hs
  exact loop_bound_mismatch_deep_noSuccess_of_reachable cursor state inv hr hw hpending hc
    current hcurrent carrier hb hv hs

theorem loop_bound_mismatch_deep_noSuccess (cursor : Nat)
    (state : State source target spills) (inv : Invariant cursor state)
    (hw : MAX_SWAP_DEPTH + 2 ≤ state.stack.length - cursor)
    (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (carrier : Fin state.stack.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier)
    (hv : state.stack[current] ≠ state.stack[carrier]) :
    ¬Success (buildBottomUp.loop cursor state) (fun _ => True) := by
  by_cases hpending : state.pending_generations = 0
  · intro hs
    have ht : ∀ j, (state.mapping.symm j).isSome :=
      (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hpending)
    have hlen : state.stack.length = target.length := by
      have := inv.size
      omega
    have hsource := (state.mapping.complete_of_target_total hlen.le ht).2
    have hperm := (loop_success_iff_permutation cursor state inv hpending hlen hsource).mp hs
    have hnotfixed : state.mapping.toPermutation hlen hsource current ≠ current := by
      intro hfixed
      have hmap := (Mapping.toPermutation_apply state.mapping hlen hsource current).symm
      rw [hfixed] at hmap
      have hcast : Fin.cast hlen current = (⟨cursor, hc⟩ : Fin target.length) := Fin.ext hcurrent
      rw [hcast] at hmap
      have hbcurrent := state.mapping.eq_some_iff.mpr hmap
      have heq : current = carrier := Option.some.inj (hbcurrent.symm.trans hb)
      exact hv (heq ▸ rfl)
    have hdepth := hperm current (by simpa using hnotfixed)
    dsimp [Fin.rev] at hdepth
    omega
  · exact loop_bound_mismatch_deep_noSuccess_of_pending cursor state inv hw hpending hc
      current hcurrent carrier hb hv

end Shuffler.BuildBottomUp
