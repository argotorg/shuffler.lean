import Experiments.BuildBottomUp.CheckedSupport

namespace BuildBottomUpExperiments.Checked

def urgentScan (cursor : ℕ) (state : State source target spills) : M (Option ℕ) :=
  forIn [cursor : target.length] none fun offset urgent => do
    if (positionOf state offset).isSome then
      return .yield urgent
    let slot ← slotAt target offset
    if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
      return .yield urgent
    if let some copy := state.stack.shallowestCopyPosition slot then
      if ¬ state.stack.isDupReachable copy then
        throw (.blocked (depthOf state copy - MAX_DUP_DEPTH))
      if depthOf state copy = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
        return .yield (some offset)
    return .yield urgent

def copyScan (state : State source target spills) (copy initial : ℕ) : M ℕ :=
  forIn ((List.range state.stack.length).reverse.take (depthOf state copy)) initial fun candidate pos => do
    if (← slotAt state.stack candidate) = (← slotAt state.stack copy) ∧ ¬ state.isFinal candidate then
      return .done candidate
    return .yield pos


end BuildBottomUpExperiments.Checked
