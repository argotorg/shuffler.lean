import Shuffler.BuildBottomUp.Lemmas.StaticPermutation

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Shuffler.BuildBottomUp

-- A deep equal-value placement changes only the destinations. The scan cannot
-- select either early-generation branch when at least sixteen slots remain.
theorem loop_equal_bound_eq (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor) (hr : state.reachable)
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
  simp_loop
  simp only [show ¬ cursor ≥ target.length by omega, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    have heq : current = carrier := by
      apply Fin.ext
      have hb' := (state.isFinal_of_bound_iff ⟨cursor, hc⟩ carrier hb).mp hfinal
      exact hcurrent.trans hb'.symm
    subst carrier
    simp only [Mapping.swapDestinations_self]
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  simp only [hp, ↓reduceIte]
  have hscan := Succeeds.of_triple _ _ (urgentScan_success cursor state hr)
  simp only [bind_pure] at hscan
  obtain ⟨urgent, heq, _⟩ := hscan
  erw [heq, except_ok_bind]
  simp only [hnotearly, and_false, ↓reduceDIte]
  rw [ite_index_eq_rest (fun hA => hA.2.2) (fun _ hB => hB),
    index_eq ⟨cursor, hc⟩, except_ok_bind]
  have hposition : state.positionOf ⟨cursor, hc⟩ = some carrier := hb
  simp only [hposition]
  subst hcurrent
  rw [requires_of_true _ hge, except_ok_bind, slotAt_index state.stack current,
    slotAt_index state.stack carrier]
  simp only [except_ok_bind]
  rw [ite_eq_left hv]
  try simp only [except_ok_bind]
  rw [requires_of_true _ hv, except_ok_bind, swapDestinations_result state current carrier,
    except_ok_bind]

theorem loop_equal_bound_success_iff (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor)
    (hw : MAX_SWAP_DEPTH ≤ state.stack.length - cursor)
    (hp : state.pending_generations ≠ 0)
    (hc : cursor < target.length)
    (current : Fin state.stack.length) (hcurrent : current.val = cursor)
    (carrier : Fin state.stack.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier)
    (hv : state.stack[current] = state.stack[carrier]) :
    Succeeds (buildBottomUp.loop cursor state) (fun _ => True) ↔
      state.reachable ∧ Succeeds (buildBottomUp.loop (cursor + 1)
        { state with mapping := state.mapping.swapDestinations current carrier }) (fun _ => True) := by
  constructor
  · intro hs
    have hr := loop_success_requires_reachable cursor state inv hs
    exact ⟨hr, (loop_equal_bound_eq cursor state inv hr hw hp hc current hcurrent carrier hb hv) ▸ hs⟩
  · rintro ⟨hr, hs⟩
    rwa [loop_equal_bound_eq cursor state inv hr hw hp hc current hcurrent carrier hb hv]

theorem loop_hole_eq_of_generate_final (cursor : Nat) (state next : State source target spills)
    (hr : state.reachable) (hw : MAX_SWAP_DEPTH ≤ state.stack.length - cursor)
    (hp : state.pending_generations ≠ 0) (hc : cursor < target.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = none)
    (hg : state.generate cursor = .ok next) (hf : ∃ h, next.isFinal ⟨cursor, h⟩) :
    buildBottomUp.loop cursor state = buildBottomUp.loop (cursor + 1) next := by
  have hn : ¬ ∃ h, state.isFinal ⟨cursor, h⟩ := by simp [State.exists_isFinal_iff, hc, hb]
  have hnotearly : ¬state.stack.length - cursor < MAX_SWAP_DEPTH := by omega
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  simp only [show ¬ cursor ≥ target.length by omega, ↓reduceIte]
  rw [skip_unless_final (fun hlt => (state.isFinal_iff ⟨cursor, hlt⟩).not.mpr hn)]
  simp only [hp, ↓reduceIte]
  have hscan := Succeeds.of_triple _ _ (urgentScan_success cursor state hr)
  simp only [bind_pure] at hscan
  obtain ⟨urgent, heq, _⟩ := hscan
  erw [heq, except_ok_bind]
  simp only [hnotearly, and_false, ↓reduceDIte]
  rw [ite_index_eq_rest (fun hA => hA.2.2) (fun _ hB => hB), index_eq ⟨cursor, hc⟩, except_ok_bind]
  have hposition : state.positionOf ⟨cursor, hc⟩ = none := hb
  simp only [hposition]
  rw [hg, except_ok_bind]
  have hlt := hf.1
  rw [index_eq ⟨cursor, hlt⟩, except_ok_bind, ite_eq_left ((next.isFinal_iff ⟨cursor, hlt⟩).mpr hf)]

theorem loop_hole_blocks_of_generate_deep (cursor : Nat) (state next : State source target spills)
    (hr : state.reachable) (hw : MAX_SWAP_DEPTH ≤ state.stack.length - cursor)
    (hp : state.pending_generations ≠ 0) (hc : cursor < target.length)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = none)
    (hg : state.generate cursor = .ok next) (hnf : ¬ ∃ h, next.isFinal ⟨cursor, h⟩)
    (pos : Fin next.stack.length) (hpos : pos.val = cursor)
    (hbelow : pos.val + 1 < next.stack.length) (hdeep : ¬next.stack.isSwapReachable pos) :
    ¬Succeeds (buildBottomUp.loop cursor state) (fun _ => True) := by
  have hn : ¬ ∃ h, state.isFinal ⟨cursor, h⟩ := by simp [State.exists_isFinal_iff, hc, hb]
  have hnotearly : ¬state.stack.length - cursor < MAX_SWAP_DEPTH := by omega
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  simp only [show ¬ cursor ≥ target.length by omega, ↓reduceIte]
  rw [skip_unless_final (fun hlt => (state.isFinal_iff ⟨cursor, hlt⟩).not.mpr hn)]
  simp only [hp, ↓reduceIte]
  have hscan := Succeeds.of_triple _ _ (urgentScan_success cursor state hr)
  simp only [bind_pure] at hscan
  obtain ⟨urgent, heq, _⟩ := hscan
  erw [heq, except_ok_bind]
  simp only [hnotearly, and_false, ↓reduceDIte]
  rw [ite_index_eq_rest (fun hA => hA.2.2) (fun _ hB => hB), index_eq ⟨cursor, hc⟩, except_ok_bind]
  have hposition : state.positionOf ⟨cursor, hc⟩ = none := hb
  simp only [hposition]
  rw [hg, except_ok_bind]
  subst hpos
  have hnt : pos.val ≠ next.stack.length - 1 := by omega
  rw [index_eq pos]
  simp only [except_ok_bind]
  rw [ite_eq_right ((next.isFinal_iff pos).not.mpr hnf), requires_of_true _ ((next.isFinal_iff pos).not.mpr hnf)]
  simp only [except_ok_bind]
  rw [ite_eq_left hnt, ite_eq_left (show ¬ next.isSwapReachable pos from hdeep)]
  rintro ⟨_, h, _⟩
  cases h

end Shuffler.BuildBottomUp
