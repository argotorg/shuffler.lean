import Shuffler.BuildBottomUp.Lemmas.StaticPermutation

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Shuffler.BuildBottomUp

-- A deep equal-value placement changes only the destinations. The scan cannot
-- select either early-generation branch when at least sixteen slots remain.
theorem loop_equal_bound_eq (cursor : Nat) (state : State source target spills)
    (inv : Invariant cursor state) (hr : Reachable state)
    (hw : MAX_SWAP_DEPTH ≤ state.stack.length - cursor)
    (hp : state.pending_generations ≠ 0)
    (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (carrier : Fin state.stack.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier)
    (hv : state.stack[current] = state.stack[carrier]) :
    buildBottomUp.loop cursor state = buildBottomUp.loop (cursor + 1)
      { state with mapping := state.mapping.swapDestinations current carrier } := by
  have hge := inv.processed.bound_ge ⟨cursor, hc⟩ carrier hb le_rfl
  have hnotearly : ¬state.stack.length - cursor < MAX_SWAP_DEPTH := by omega
  rw [buildBottomUp.loop.eq_def]
  simp_action
  simp only [hc, ↓reduceIte]
  by_cases hskip : cursor < state.stack.length ∧ state.isFinal cursor
  · rw [ite_eq_left hskip]
    have heq : current = carrier := by
      apply Fin.ext
      have hb' := (state.isFinal_of_bound_iff ⟨cursor, hc⟩ carrier hb).mp hskip.2
      exact hcurrent.trans hb'.symm
    subst carrier
    simp only [Mapping.swapDestinations_self]
    rfl
  · rw [ite_eq_right hskip, ite_eq_right hp]
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
    change StateT.run (s := state) _ = _
    try simp_action
    rw [ensure_of_true _ hge]
    try simp only [except_ok_bind]
    have hslot : slotAt state.stack cursor = .ok state.stack[current] :=
      hcurrent ▸ slotAt_index state.stack current
    rw [hslot, slotAt_index state.stack carrier]
    try simp_action
    simp only [hv, ↓reduceIte]
    rw [ensure_of_true True trivial]
    try simp_action
    rw [← hcurrent, swapDestinations_result state current carrier]
    try simp_action
    rfl

theorem loop_equal_bound_success_iff (cursor : Nat) (state : State source target spills)
    (inv : Invariant cursor state)
    (hw : MAX_SWAP_DEPTH ≤ state.stack.length - cursor)
    (hp : state.pending_generations ≠ 0)
    (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (carrier : Fin state.stack.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier)
    (hv : state.stack[current] = state.stack[carrier]) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) ↔
      Reachable state ∧ Success (buildBottomUp.loop (cursor + 1)
        { state with mapping := state.mapping.swapDestinations current carrier }) (fun _ => True) := by
  constructor
  · intro hs
    have hr := loop_success_requires_reachable cursor state inv hs
    exact ⟨hr, (loop_equal_bound_eq cursor state inv hr hw hp hc current hcurrent carrier hb hv) ▸ hs⟩
  · rintro ⟨hr, hs⟩
    rwa [loop_equal_bound_eq cursor state inv hr hw hp hc current hcurrent carrier hb hv]

theorem loop_hole_eq_of_generate_final (cursor : Nat) (state next : State source target spills)
    (hr : Reachable state) (hw : MAX_SWAP_DEPTH ≤ state.stack.length - cursor)
    (hp : state.pending_generations ≠ 0) (hc : cursor < target.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = none)
    (hg : (generate cursor).exec state = .ok next) (hf : next.isFinal cursor) :
    buildBottomUp.loop cursor state = buildBottomUp.loop (cursor + 1) next := by
  have hn : ¬state.isFinal cursor := by simp [State.isFinal, hc, hb]
  have hskip : ¬(cursor < state.stack.length ∧ state.isFinal cursor) := fun h => hn h.2
  have hnotearly : ¬state.stack.length - cursor < MAX_SWAP_DEPTH := by omega
  rw [buildBottomUp.loop.eq_def]
  simp_action
  rw [ite_eq_left hc, ite_eq_right hskip, ite_eq_right hp]
  rw [StateT.run_bind]
  have hscan := Success.of_triple _ _ _ (urgentScan_success cursor state hr)
  simp only [bind_pure] at hscan
  obtain ⟨⟨urgent, state'⟩, heq, _, hnext⟩ := hscan
  dsimp only at hnext
  subst state'
  simp only [StateT.run] at heq ⊢
  erw [heq]
  simp only [except_ok_bind, hnotearly, and_false, ↓reduceDIte, ↓reduceIte]
  have hposition : state.positionOf cursor = none := by
    simp [State.positionOf, hc, hb]
  rw [hposition]
  change StateT.run (s := state) _ = _
  simp_action
  rw [hg]
  simp_action
  rw [ite_eq_left hf]
  rfl

theorem loop_hole_blocks_of_generate_deep (cursor : Nat) (state next : State source target spills)
    (hr : Reachable state) (hw : MAX_SWAP_DEPTH ≤ state.stack.length - cursor)
    (hp : state.pending_generations ≠ 0) (hc : cursor < target.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = none)
    (hg : (generate cursor).exec state = .ok next) (hnf : ¬next.isFinal cursor)
    (pos : Fin next.stack.length) (hpos : pos.val = cursor)
    (hbelow : pos.val + 1 < next.stack.length) (hdeep : ¬next.stack.isSwapReachable pos) :
    ¬Success (buildBottomUp.loop cursor state) (fun _ => True) := by
  have hn : ¬state.isFinal cursor := by simp [State.isFinal, hc, hb]
  have hskip : ¬(cursor < state.stack.length ∧ state.isFinal cursor) := fun h => hn h.2
  have hnotearly : ¬state.stack.length - cursor < MAX_SWAP_DEPTH := by omega
  rw [buildBottomUp.loop.eq_def]
  simp_action
  rw [ite_eq_left hc, ite_eq_right hskip, ite_eq_right hp]
  rw [StateT.run_bind]
  have hscan := Success.of_triple _ _ _ (urgentScan_success cursor state hr)
  simp only [bind_pure] at hscan
  obtain ⟨⟨urgent, state'⟩, heq, _, hnext⟩ := hscan
  dsimp only at hnext
  subst state'
  simp only [StateT.run] at heq ⊢
  erw [heq]
  simp only [except_ok_bind, hnotearly, and_false, ↓reduceDIte, ↓reduceIte]
  have hposition : state.positionOf cursor = none := by
    simp [State.positionOf, hc, hb]
  rw [hposition]
  change ¬Success (StateT.run (s := state) _) _
  simp_action
  rw [hg]
  simp_action
  rw [ite_eq_right hnf]
  try simp_action
  rw [ensure_of_true _ hnf]
  simp_action
  have hnt : cursor ≠ next.stack.length - 1 := by omega
  rw [ite_eq_left hnt]
  try simp_action
  rw [← hpos, isSwapReachable_index next pos]
  simp only [hdeep, decide_false]
  simp_action
  rw [depthOf_index next pos]
  simp_action
  simp [Success]

end Shuffler.BuildBottomUp
