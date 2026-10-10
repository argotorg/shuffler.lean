import Shuffler.BuildMapping
import Shuffler.BuildBottomUp.Optimality.Theorems
import Tests.BuildBottomUpObservations

open Shuffler.Optimality.BBU Shuffler.BuildBottomUp BuildBottomUpTestSupport

namespace OptimalityLiftTests

private def v (i : Nat) : Value := .Var ⟨i⟩

-- Result stack and SWAP count of the production BBU call. A failed call or a state that is not
-- Valid gives none.
private def outcome (s : State source target spills) : Option (Stack × Nat) :=
  ((runIfValid s).map fun r => (r.1, r.2.swapCount)).toOption

-- The three fields of State.Valid.
private def valid (s : State source target spills) : Bool :=
  decide (s.stack.length + s.pending_generations = target.length) &&
    decide (s.mapping.unmapped_target_slots = s.pending_generations) &&
    decide (∀ i, s.isAvailable i)

-- The claim of lift_succeeds: the lift is Valid, keeps the start count, and BBU puts pre
-- below the same result with the same count.
private def lifts (pre : Stack) (s : State source target spills) : Bool :=
  valid (liftState pre s) &&
    (liftState pre s).trace.swapCount == s.trace.swapCount &&
    (liftState pre s).pending_generations == s.pending_generations &&
    (liftState pre s).stack.length == pre.length + s.stack.length &&
    outcome (liftState pre s) == (outcome s).map fun (st, c) => (pre ++ st, c)

-- Values that occur nowhere in the families below.
private def fresh (b : Nat) : Stack := (List.range b).map fun i => v (1000 + i)

-- pre is not required to be fresh: copies of source values, and one value repeated.
private def pres (b : Nat) (source : Stack) : List Stack :=
  [fresh b, List.replicate b (v 0), source.take b, (source.take b).reverse]

#guard fresh 0 = [] ∧ pres 0 [v 1] = [[], [], [], []]

-- Family W at n = 17: 2k + 30 for k ≥ 3, and the k < 3 counts.
#guard [0, 1, 2, 3, 4, 5, 10, 19, 20].all fun k => [0, 1, 2, 7, 17].all fun b =>
  (pres b (winSource 0 k)).all fun pre => lifts pre (windowState 17 k)
#guard [3, 4, 10, 20].all fun k => [1, 5, 30].all fun b =>
  (outcome (liftState (fresh b) (windowState 17 k))).map (·.2) == some (2 * k + 30)

-- Family F1.
#guard [0, 1, 2, 10].all fun k => [0, 1, 2, 7].all fun b =>
  (pres b f1Source).all fun pre => lifts pre (f1State k)

-- b = 0: the lift has the same outcome.
#guard [0, 3, 10].all fun k =>
  outcome (liftState [] (windowState 17 k)) == outcome (windowState 17 k)

-- The lift of family W for n = 17 + b, as in swapCounts_isGreatest.
#guard [0, 1, 6].all fun b => [3, 7].all fun k =>
  let s := liftState (List.replicate b (Value.Var ⟨0⟩)) (windowState 17 k)
  valid s && s.pending_generations == k && s.stack.length == 17 + b &&
    (outcome s).map (·.2) == some (s.trace.swapCount + (2 * k + 30))

--- Negative cases --------------------------------------------------------------------------------

-- The production mapping builder, with spills empty.
private def initial (source target : Stack) : State source target ∅ :=
  let mapping := (MappingBuilder.buildMapping source target
    (List.replicate source.length 0) .Leave (by simp)).mapping
  { planned_mapping := mapping, stack := source, trace := .Lit source, mapping
    pending_generations := target.length - source.length }

-- The converse fails: v 0 is not available in s, so s is not Valid and BBU cannot run on it.
-- The lift is Valid and BBU succeeds on it.
#guard !valid (initial [v 1] [v 1, v 0])
#guard outcome (initial [v 1] [v 1, v 0]) = none
#guard outcome (liftState [v 0] (initial [v 1] [v 1, v 0])) = some ([v 0, v 1, v 0], 0)

-- pre at the bottom of the stack but not at its own destination changes the count.
#guard outcome (initial [v 1, v 2] [v 2, v 1]) = some ([v 2, v 1], 1)
#guard outcome (liftState [v 0, v 3] (initial [v 1, v 2] [v 2, v 1])) =
  some ([v 0, v 3, v 2, v 1], 1)
#guard outcome (initial [v 0, v 3, v 1, v 2] [v 3, v 0, v 2, v 1]) =
  some ([v 3, v 0, v 2, v 1], 4)

-- The count is exact.
#guard (outcome (liftState (fresh 3) (windowState 17 10))).map (·.2) ≠ some 49
#guard (outcome (liftState (fresh 3) (windowState 17 10))).map (·.2) ≠ some 51

end OptimalityLiftTests
