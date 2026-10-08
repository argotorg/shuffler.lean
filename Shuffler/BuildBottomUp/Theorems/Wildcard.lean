import Shuffler.Stack
import Shuffler.BuildBottomUp.Theorems.Static

namespace Shuffler.BuildBottomUp

theorem expectedStack_matches (state : State source target spills)
    (hmapped : ∀ i j, state.mapping i = some j → SlotMatches state.stack[i] target[j]) :
    StackMatches state.expectedStack target := by
  apply List.forall₂_of_length_eq_of_get
  · simp [State.expectedStack]
  · intro i hi hj
    simp only [List.get_eq_getElem, State.expectedStack, List.getElem_ofFn]
    split
    · rename_i pos hp
      exact hmapped pos ⟨i, hj⟩ (state.mapping.eq_some_iff.mp hp)
    · exact SlotMatches.refl _

theorem buildBottomUp_matches_of_ok (initial : State source target spills)
    (h : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → SlotMatches initial.stack[i] target[j])
    {res : Stack} {trace : Trace spills source res}
    (hrun : buildBottomUp initial h = .ok ⟨res, trace⟩) : StackMatches res target := by
  rw [buildBottomUp_expected_of_ok initial h hrun]
  exact expectedStack_matches initial hmapped

theorem buildBottomUp_matches_iff_static (initial : State source target spills)
    (h : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → SlotMatches initial.stack[i] target[j]) :
    (∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial h = .ok ⟨res, trace⟩ ∧ StackMatches res target) ↔
      StaticSuccess initial := by
  constructor
  · rintro ⟨res, trace, hrun, _⟩
    exact (buildBottomUp_succeeds_iff_static initial h).mp ⟨res, trace, hrun⟩
  · intro hs
    obtain ⟨res, trace, hrun⟩ := (buildBottomUp_succeeds_iff_static initial h).mpr hs
    exact ⟨res, trace, hrun, buildBottomUp_matches_of_ok initial h hmapped hrun⟩

end Shuffler.BuildBottomUp
