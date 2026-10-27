import Shuffler.ExactBuild.Build
import Shuffler.BuildBottomUp.Theorems.Wildcard

namespace Shuffler.BuildBottomUp

-- The target values of all unbound destinations, in target order.
def State.missingValues (state : State source target spills) : Stack :=
  ((List.finRange target.length).filter fun dest => (state.mapping.symm dest).isNone).map
    (fun dest => target[dest])

-- Plan from the saved entry stack. The certificate for no POP and exact
-- additions applies to this new suffix; initial.trace may contain earlier POPs.
def buildComplete (initial : State source target spills) :
    Option ((result : Stack) × Trace spills source result) :=
  (ExactBuild.build spills initial.stack initial.expectedStack
    (initial.missingValues : Multiset Value)).map fun built =>
      ⟨initial.expectedStack, initial.trace.concat built.trace⟩

theorem buildComplete_succeeds_iff_reserve (initial : State source target spills) :
    (buildComplete initial).isSome ↔
      Placement.Reserve spills initial.stack initial.expectedStack
        (initial.missingValues : Multiset Value) := by
  simpa only [buildComplete, Option.isSome_map] using
    ExactBuild.build_succeeds_iff_reserve spills initial.stack initial.expectedStack
      (initial.missingValues : Multiset Value)

theorem buildComplete_expected_of_some (initial : State source target spills)
    {result : (res : Stack) × Trace spills source res}
    (h : buildComplete initial = some result) : result.1 = initial.expectedStack := by
  obtain ⟨built, _, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

theorem buildComplete_matches_of_some (initial : State source target spills)
    (hmapped : ∀ i j, initial.mapping i = some j → SlotMatches initial.stack[i] target[j])
    {result : (res : Stack) × Trace spills source res}
    (h : buildComplete initial = some result) : StackMatches result.1 target := by
  rw [buildComplete_expected_of_some initial h]
  exact expectedStack_matches initial hmapped

end Shuffler.BuildBottomUp
