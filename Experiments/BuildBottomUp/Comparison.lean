import Experiments.BuildBottomUp.Equivalence
import Experiments.BuildBottomUp.Deferred

namespace BuildBottomUpExperiments

inductive Operation where
  | swap (depth : ℕ) | dup (index : ℕ) | pop | push (value : Value) | load (id : VarId)
  deriving DecidableEq

-- Include every trace operation and operand, in order.
def operations : Trace spills source result → List Operation
  | .Lit _ => []
  | .Swap depth _ _ _ trace => operations trace ++ [.swap depth]
  | .Dup index _ _ _ trace => operations trace ++ [.dup index]
  | .Pop _ trace => operations trace ++ [.pop]
  | .Push value _ trace => operations trace ++ [.push value]
  | .Load id _ trace => operations trace ++ [.load id]

def observe (result : Checked.M (Checked.Result source spills)) :
    Except Checked.Error (Stack × List Operation) :=
  result.map fun ⟨stack, trace⟩ => (stack, operations trace)

-- Used by the existing branch fixtures. A difference, including a new assertion
-- error, makes both their success checks and their Blocked checks fail.
def compareAndRun (cursor : ℕ) (state : State source target spills)
    (hinv : LoopInvariant cursor state)
    (hsize : state.stack.length + state.pending_generations = target.length)
    (hpending : state.mapping.unmapped_target_slots = state.pending_generations)
    (havailable : ∀ i, state.is_available i) : Checked.M (Checked.Result source spills) :=
  let original := Checked.liftResult (build_bottom_up cursor state hinv hsize hpending havailable)
  let deferred := Checked.liftResult (Deferred.buildBottomUp cursor state ⟨hinv, hsize, hpending, havailable⟩)
  let checked := Checked.buildBottomUp cursor state
  let verified := Checked.liftResult
    (Checked.buildBottomUpVerified cursor state ⟨hinv, hsize, hpending, havailable⟩)
  if observe original == observe deferred && observe original == observe checked &&
      observe original == observe verified then checked
  else .error (.assertion .permutation)

end BuildBottomUpExperiments
