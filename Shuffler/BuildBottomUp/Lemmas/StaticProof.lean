import Shuffler.BuildBottomUp.Lemmas.StaticTransition
import Shuffler.BuildBottomUp.Lemmas.StaticTerminalCondition

namespace Shuffler.BuildBottomUp

namespace Static

-- Induction is used to prove the condition. The condition itself consists only
-- of finite tests on data fixed by the initial state.
theorem loop_success_iff_suffix (initial : State source target spills) (h : initial.Valid)
    (hn : 16 < initial.stack.length) (cursor : Nat) (state : State source target spills)
    (hc : cursor ≤ cutoff initial) (hp : PrefixState initial h cursor state) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) ↔ Suffix initial cursor := by
  by_cases he : cursor = cutoff initial
  · subst cursor
    rw [terminal_success_iff initial h hn state hp]
    exact (suffix_cutoff initial).symm
  have hlt : cursor < cutoff initial := by omega
  by_cases hr : Reachable state
  · obtain ⟨hstep, hblock⟩ := hp.step hn hlt hr
    have hready : Ready initial cursor := hp.ready_iff.mpr hr
    by_cases hv : (augmentedStack initial)[cursor]? = initial.expectedStack[cursor]?
    · obtain ⟨next, hnext, heq⟩ := hstep hv
      rw [heq, suffix_step initial cursor hlt]
      simp only [hv, hready, true_and]
      exact loop_success_iff_suffix initial h hn (cursor + 1) next (by omega) hnext
    · have hnrun := hblock hv
      have hnsuffix : ¬Suffix initial cursor := fun hs => hv (hs.1 cursor le_rfl hlt)
      exact iff_of_false hnrun hnsuffix
  · have hnrun : ¬Success (buildBottomUp.loop cursor state) (fun _ => True) :=
      fun hs => hr (loop_success_requires_reachable cursor state hp.invariant hs)
    have hnsuffix : ¬Suffix initial cursor :=
      fun hs => hr (hp.ready_iff.mp (hs.2.1 cursor le_rfl hlt.le))
    exact iff_of_false hnrun hnsuffix
termination_by cutoff initial - cursor

end Static

theorem success_map_iff (result : Except Error α) (f : α → β) :
    Success (f <$> result) (fun _ => True) ↔ Success result (fun _ => True) := by
  cases result <;> simp [Success]

theorem buildBottomUp_static_success_iff (initial : State source target spills)
    (h : initial.Valid) :
    Success (buildBottomUp initial) (fun _ => True) ↔ StaticSuccess initial := by
  by_cases hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1
  · exact iff_of_true (buildBottomUp_success initial h hsmall)
      ((staticSuccess_iff_reachable_of_small initial hsmall).mpr
        (WithinReach.initial h hsmall).copies)
  · have hn : 16 < initial.stack.length := by unfold MAX_DUP_DEPTH at hsmall; omega
    unfold buildBottomUp
    rw [StateT.run'_eq]
    change Success ((fun result => result.1) <$> buildBottomUp.loop 0 initial) _ ↔ _
    rw [success_map_iff]
    exact (Static.loop_success_iff_suffix initial h hn 0 initial (Nat.zero_le _)
      (Static.PrefixState.initial initial h)).trans
        (Static.staticSuccess_iff_suffix_of_large initial (by unfold MAX_DUP_DEPTH; omega)).symm

end Shuffler.BuildBottomUp
