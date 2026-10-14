import Shuffler.BuildBottomUp.Lemmas.StaticPermutation

namespace Shuffler.BuildBottomUp

private theorem permute_success_iff (spills : SpillSet) (stack : Stack)
    (perm : Shuffler.Permute.Permutation stack) :
    (∃ result, Shuffler.Permute.permute spills stack perm = .ok result) ↔
      Shuffler.Permute.all_swaps_reachable perm := by
  constructor
  · rintro ⟨result, hs⟩
    by_contra hn
    obtain ⟨_, he, _⟩ := Shuffler.Permute.permute_blocks_unreachable spills stack perm hn
    rw [hs] at he
    contradiction
  · intro hr
    obtain ⟨res, trace, he, _⟩ := Shuffler.Permute.permute_applies_permutation_reachable spills stack perm hr
    exact ⟨⟨res, trace⟩, he⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem loop_success_iff_permutation (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor) (hp : state.pending_generations = 0)
    (hlen : state.stack.length = target.length)
    (hsource : ∀ i, (state.mapping i).isSome) :
    Succeeds (buildBottomUp.loop cursor state) (fun _ => True) ↔
      Shuffler.Permute.all_swaps_reachable (state.mapping.toPermutation hlen hsource) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    have hr : state.reachable := by
      intro j hb
      have ht := (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hp)
      simp only [State.positionOf] at hb
      simpa [hb] using ht j
    have hw : state.stack.length - cursor ≤ MAX_SWAP_DEPTH := by omega
    have hperm := inv.permutation_reachable ⟨hw, hr⟩ hlen hsource
    exact ⟨fun _ => hperm, fun _ => ⟨_, rfl, trivial⟩⟩
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact loop_success_iff_permutation (cursor + 1) state (inv.advance hfinal) hp hlen hsource
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  simp only [hp, ↓reduceIte, requires_of_true _ hlen, except_ok_bind]
  rw [requires_of_true (∀ i, (state.destinationOf i).isSome) hsource, except_ok_bind]
  rw [← permute_success_iff spills state.stack (state.mapping.toPermutation hlen hsource)]
  cases heq : Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hlen hsource) with
  | error err => simp [Except.mapError, Succeeds]
  | ok result =>
    obtain ⟨res, trace⟩ := result
    simp [Except.mapError, Succeeds]
termination_by target.length - cursor

end Shuffler.BuildBottomUp
