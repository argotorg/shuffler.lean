module

public import FlatShuffler.Unit.Plan.PlannerRunDataFrame
import all FlatShuffler.Unit.Plan.PlannerRunDataFrame
public import FlatShuffler.Unit.Run.Model
import all FlatShuffler.Unit.Run.Model

@[expose] public section

namespace FlatShuffler.Flat

theorem restoreData_unmappedFrom (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (o count : Word) :
    unmappedFrom (restoreData cap old st) o count = unmappedFrom st o count := by
  conv => lhs; rw [unmappedFrom]
  conv => rhs; rw [unmappedFrom]
  simp only [restoreData_targetSize, restoreData_pos]
  split
  · exact restoreData_unmappedFrom cap old st _ _
  · rfl
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

theorem restoreData_isAvailable (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (o : Word) (hs : st.size.toNat ≤ cap) :
    isAvailable (restoreData cap old st) o = isAvailable st o := by
  simp only [isAvailable, restoreData_target, isSpilled, restoreData_spills,
    restoreData_shallowestCopyPosition cap old st _ hs]

theorem restoreData_availableFrom (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (o : Word) (hs : st.size.toNat ≤ cap) :
    availableFrom (restoreData cap old st) o = availableFrom st o := by
  conv => lhs; rw [availableFrom]
  conv => rhs; rw [availableFrom]
  simp only [restoreData_targetSize, restoreData_isAvailable cap old st _ hs]
  split
  · rw [restoreData_availableFrom cap old st _ hs]
  · rfl
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

theorem restoreData_labelsFrom (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (o : Word) :
    labelsFrom (restoreData cap old st) o = labelsFrom st o := by
  conv => lhs; rw [labelsFrom]
  conv => rhs; rw [labelsFrom]
  simp only [restoreData_targetSize, restoreData_target, restoreData_pos]
  split
  · rw [restoreData_labelsFrom cap old st _]
  · rfl
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

end FlatShuffler.Flat
