import Shuffler.Optimality.Replay

namespace Shuffler.Optimality

theorem replayStep_cost (costs : PrimitiveCosts) (spills : SpillSet) (source : Stack)
    (op : Op) (result : ReplayResult spills source)
    (h : replayStep spills source op = some result) :
    traceCost costs result.built.trace = op.cost costs := by
  cases op <;> simp only [replayStep] at h
  all_goals try contradiction
  all_goals split at h
  all_goals try contradiction
  all_goals cases h
  all_goals simp [traceCost, Op.cost]

theorem replayFrom_cost (costs : PrimitiveCosts) (state : ReplayResult spills source)
    (ops : List Op) (result : ReplayResult spills source)
    (h : replayFrom state ops = some result) :
    traceCost costs result.built.trace =
      (traceCost costs state.built.trace).add (opsCost costs ops) := by
  induction ops generalizing state with
  | nil =>
      cases h
      simp [opsCost]
  | cons op rest ih =>
      cases hs : replayStep spills state.target op with
      | none => simp [replayFrom, hs] at h
      | some step =>
          simp only [replayFrom, hs] at h
          rw [ih _ h]
          simp only [ReplayResult.append, Shuffler.Placement.BuiltTrace.trans,
            traceCost_concat, replayStep_cost costs spills state.target op step hs,
            opsCost, Cost.add_assoc]

theorem replay_cost (costs : PrimitiveCosts) (spills : SpillSet) (source : Stack)
    (ops : List Op) (result : ReplayResult spills source)
    (h : replay spills source ops = some result) :
    traceCost costs result.built.trace = opsCost costs ops := by
  simpa [ReplayResult.nil, traceCost] using
    replayFrom_cost costs (ReplayResult.nil spills source) ops result h

theorem replayExact_cost (costs : PrimitiveCosts) (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) (ops : List Op)
    (result : Shuffler.Placement.BuiltTrace spills source target missing)
    (h : replayExact spills source target missing ops = some result) :
    traceCost costs result.trace = opsCost costs ops := by
  cases hr : replay spills source ops with
  | none => simp [replayExact, hr] at h
  | some replayed =>
      by_cases ht : replayed.target = target
      · by_cases hm : replayed.added = missing
        · simp [replayExact, hr, ht, hm] at h
          rw [← h]
          subst target missing
          exact replay_cost costs spills source ops replayed hr
        · simp [replayExact, hr, ht, hm] at h
      · simp [replayExact, hr, ht] at h

end Shuffler.Optimality
