module

public import Shuffler.BuildBottomUp.Lemmas.ReachActions
import Shuffler.BuildBottomUp.Lemmas.Invariants
import Shuffler.BuildBottomUp.Lemmas.LoopProofs
import Shuffler.BuildBottomUp.Lemmas.SuccessProofs
import Shuffler.Permute.Theorems
import Shuffler.Permute.Normalization

@[expose] public section

namespace Shuffler.Emission

private theorem permute_success_iff (spills : SpillSet) (state : State source target spills)
    (perm : Shuffler.Permute.Permutation state.stack) :
    (∃ result, ((((Shuffler.Permute.permute state perm) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) = .ok result) ↔
      Shuffler.Permute.values_reachable perm := by
  constructor
  · rintro ⟨result, hs⟩
    obtain ⟨next, hrun, _⟩ := completedTrace_ok_inversion hs
    by_contra hn
    obtain ⟨_, _, _, he, _⟩ := Shuffler.Permute.permute_blocks_unreachable spills state perm hn
    rw [hrun] at he
    cases he
  · intro hr
    obtain ⟨result, he, _⟩ := Shuffler.Permute.permute_applies_permutation_reachable spills state perm hr
    exact ⟨_, completedTrace_of_ok he⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem loop_success_iff_permutation (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor) (hp : state.pending_generations = 0)
    (hlen : state.stack.length = target.length)
    (hsource : ∀ i, (state.mapping i).isSome) :
    Succeeds (((((buildBottomUp.loop cursor state) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack))) (fun _ => True) ↔
      Shuffler.Permute.values_reachable (state.mapping.toPermutation hlen hsource) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    have hr : state.reachable := by
      intro j hb
      have ht := (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hp)
      simp only [Mapping.positionOf] at hb
      simpa [hb] using ht j
    have hw : state.stack.length - cursor ≤ MAX_SWAP_DEPTH := by omega
    have hperm := inv.permutation_reachable ⟨hw, hr⟩ hlen hsource
    exact ⟨fun _ => hperm.values, fun _ => ⟨_, rfl, trivial⟩⟩
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact loop_success_iff_permutation (cursor + 1) state (inv.advance hfinal) hp hlen hsource
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  simp only [hp, ↓reduceIte, requires_of_true _ hlen, except_ok_bind]
  rw [requires_of_true (∀ i, (state.mapping.destinationOf i).isSome) hsource, except_ok_bind]
  simpa only [Succeeds, and_true] using
    (permute_success_iff spills state (state.mapping.toPermutation hlen hsource))
termination_by target.length - cursor

end Shuffler.Emission
