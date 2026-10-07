import Shuffler.Optimality.Schedule.Defs
import Shuffler.Optimality.Replay.Theorems

namespace Shuffler.Optimality.Schedule

@[simp] theorem simulate_nil (spills : SpillSet) (stack : Stack) :
    simulate spills stack [] = some stack := rfl

theorem simulate_singleton (spills : SpillSet) (stack : Stack) (op : Op) :
    simulate spills stack [op] =
      (replayStep spills stack op).map (fun result => result.target) := by
  unfold simulate replay
  simp only [replayFrom, ReplayResult.nil]
  cases h : replayStep spills stack op <;> rfl

theorem simulate_append (spills : SpillSet) (stack : Stack) (first second : List Op) :
    simulate spills stack (first ++ second) =
      (simulate spills stack first).bind (fun middle => simulate spills middle second) :=
  replay_target_append spills stack first second

theorem simulate_swapPosition (spills : SpillSet) (stack : Stack) (position : Nat)
    (hpos : position < stack.length) (hreach : stack.length ≤ position + (MAX_SWAP_DEPTH + 1)) :
    simulate spills stack (swapPosition stack position) =
      some (stack.swap (stack.length - 1) position) := by
  unfold swapPosition
  split
  next h =>
    have hd : stack.length - 1 - position < stack.length ∧
        1 ≤ stack.length - 1 - position ∧ stack.length - 1 - position ≤ MAX_SWAP_DEPTH := by omega
    have hi : stack.length - 1 - (stack.length - 1 - position) = position := by omega
    rw [simulate_singleton]
    simp only [replayStep, dite_eq_left hd, Option.map_some, hi]
  next h =>
    have hi : position = stack.length - 1 := by omega
    simp [hi]

-- The two swaps place the selected occurrence and preserve all counts.
theorem simulate_placement (spills : SpillSet) (stack : Stack) (position index : Nat)
    (hpos : position < stack.length) (hindex : index < stack.length)
    (hreach : stack.length ≤ position + (MAX_SWAP_DEPTH + 1)) (horder : position ≤ index) :
    simulate spills stack (if index = position then []
      else swapPosition stack index ++ swapPosition stack position) =
    some (if index = position then stack else
      (stack.swap (stack.length - 1) index).swap (stack.length - 1) position) := by
  split
  · rfl
  · rw [simulate_append, simulate_swapPosition spills stack index hindex (by omega)]
    simp only [Option.bind_some]
    have hlen : (stack.swap (stack.length - 1) index).length = stack.length := List.length_swap
    have he : swapPosition stack position = swapPosition
        (stack.swap (stack.length - 1) index) position := by simp only [swapPosition, hlen]
    rw [he, simulate_swapPosition _ _ _ (by omega) (by omega), hlen]

end Shuffler.Optimality.Schedule
