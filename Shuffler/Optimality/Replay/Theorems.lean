import Shuffler.Optimality.Replay

namespace Shuffler.Optimality

theorem replayFrom_append (state : ReplayResult spills source) (first second : List Op) :
    replayFrom state (first ++ second) =
      (replayFrom state first).bind (fun middle => replayFrom middle second) := by
  induction first generalizing state with
  | nil => rfl
  | cons op rest ih =>
      simp only [List.cons_append, replayFrom]
      cases hs : replayStep spills state.target op with
      | none => rfl
      | some step => exact ih (state.append step)

-- Earlier proof terms do not affect the stack produced by later operations.
theorem replayFrom_target_eq (left : ReplayResult spills source)
    (right : ReplayResult spills other) (h : left.target = right.target) (ops : List Op) :
    (replayFrom left ops).map (fun result => result.target) =
      (replayFrom right ops).map (fun result => result.target) := by
  induction ops generalizing left right with
  | nil => simpa only [replayFrom, Option.map_some] using congrArg some h
  | cons op rest ih =>
      cases left with
      | mk leftTarget leftAdded leftBuilt =>
          cases right with
          | mk rightTarget rightAdded rightBuilt =>
              change leftTarget = rightTarget at h
              subst rightTarget
              simp only [replayFrom]
              cases hs : replayStep spills leftTarget op with
              | none => rfl
              | some step => exact ih _ _ rfl

-- Simulation composes without inspecting dependent trace proofs.
theorem replay_target_append (spills : SpillSet) (source : Stack) (first second : List Op) :
    (replay spills source (first ++ second)).map (fun result => result.target) =
      ((replay spills source first).map (fun result => result.target)).bind
        (fun middle => (replay spills middle second).map (fun result => result.target)) := by
  simp only [replay]
  rw [replayFrom_append]
  cases hm : replayFrom (ReplayResult.nil spills source) first with
  | none => rfl
  | some middle =>
      simpa only [replay, hm, Option.bind_some, Option.map_some] using
        replayFrom_target_eq middle (ReplayResult.nil spills middle.target) rfl second

end Shuffler.Optimality
