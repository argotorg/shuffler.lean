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
    (inv : Invariant cursor state) (hp : state.pending_generations = 0)
    (hlen : state.stack.length = target.length)
    (hsource : ∀ i, (state.mapping i).isSome) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) ↔
      Shuffler.Permute.all_swaps_reachable (state.mapping.toPermutation hlen hsource) := by
  rw [buildBottomUp.loop.eq_def]
  simp_action
  by_cases hc : cursor < target.length
  · simp only [hc, ↓reduceIte]
    by_cases hskip : cursor < state.stack.length ∧ state.isFinal cursor
    · rw [ite_eq_left hskip]
      exact loop_success_iff_permutation (cursor + 1) state (inv.advance hskip.2) hp hlen hsource
    · rw [ite_eq_right hskip, ite_eq_left hp]
      have hcomplete : state.stack.length = target.length ∧ ∀ i, (state.mapping i).isSome :=
        ⟨hlen, hsource⟩
      simp only [requires, dite_eq_left hcomplete, pure_bind]
      split
      simp_action
      rw [← permute_success_iff spills state.stack (state.mapping.toPermutation hlen hsource)]
      cases heq : Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hlen hsource) with
      | error err => simp [Except.mapError, Success]
      | ok result =>
        obtain ⟨res, trace⟩ := result
        simp [Except.mapError, Success]
  · simp only [hc, ↓reduceIte]
    rw [ensure_of_true _ hlen]
    simp_action
    have hr : Reachable state := by
      intro j hb
      have ht := (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hp)
      simpa [hb] using ht j
    have hw : state.stack.length - cursor ≤ MAX_SWAP_DEPTH := by omega
    have hperm := inv.permutation_reachable ⟨hw, hr⟩ hlen hsource
    exact ⟨fun _ => hperm, fun _ => ⟨_, rfl, trivial⟩⟩
termination_by target.length - cursor

end Shuffler.BuildBottomUp
