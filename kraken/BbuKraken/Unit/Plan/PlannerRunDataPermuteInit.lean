import BbuKraken.Unit.Plan.PlannerRunDataFrame
import BbuKraken.Unit.PermuteModel

namespace Bbu.Flat

set_option maxRecDepth 4096

section
variable (cap : Nat) (old : Vector StackSlot MAX_N) (st : St)

theorem restoreData_readDestinations (pos : Word) (p : Vector Word MAX_N) :
    readDestinations (restoreData cap old st) pos p = readDestinations st pos p := by
  conv => lhs; rw [readDestinations]
  conv => rhs; rw [readDestinations]
  simp only [restoreData_size, restoreData_dest]
  split
  · split
    · rfl
    · exact restoreData_readDestinations _ _
  · rfl
termination_by (st.size - pos).toNat
decreasing_by bv_omega

theorem restoreData_clearDesired (pos : Word) (p : Vector Word MAX_N) :
    clearDesired (restoreData cap old st) pos p = clearDesired st pos p := by
  conv => lhs; rw [clearDesired]
  conv => rhs; rw [clearDesired]
  simp only [restoreData_size]
  split
  · exact restoreData_clearDesired _ _
  · rfl
termination_by (st.size - pos).toNat
decreasing_by bv_omega

theorem restoreData_markDesired (leader : Word) (hl : leader < st.size) (slot : StackSlot)
    (p : Vector Word MAX_N) (pos : Word) (d : Vector Word MAX_N)
    (hs : st.size.toNat ≤ cap) :
    markDesired (restoreData cap old st) leader (by simpa only [restoreData_size] using hl) slot p pos d =
      markDesired st leader hl slot p pos d := by
  conv => lhs; rw [markDesired]
  conv => rhs; rw [markDesired]
  split
  · rename_i hp
    have hpc : pos.toNat < cap := by
      have hp' := BitVec.le_def.mp hp
      have hl' := BitVec.lt_def.mp hl
      omega
    rw [restoreData_get cap old st pos hpc]
    exact restoreData_markDesired leader hl slot p _ _ hs
  · rfl
termination_by (leader + 1#64 - pos).toNat
decreasing_by
  have hleader := hl
  bv_omega

theorem restoreData_nextVacant (leader : Word) (slot : StackSlot)
    (d : Vector Word MAX_N) (vacant : Word) (hs : st.size.toNat ≤ cap) :
    nextVacant (restoreData cap old st) leader slot d vacant =
      nextVacant st leader slot d vacant := by
  conv => lhs; rw [nextVacant]
  conv => rhs; rw [nextVacant]
  simp only [restoreData_size]
  by_cases hv : vacant < st.size
  · have hvc : vacant.toNat < cap := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hv) hs
    rw [restoreData_get cap old st vacant hvc]
    split
    · exact restoreData_nextVacant leader slot d _ hs
    · rfl
  · simp only [hv, false_and, ↓reduceDIte]
termination_by (st.size - vacant).toNat
decreasing_by bv_omega

theorem restoreData_placeGroup (leader : Word) (hl : leader < st.size) (slot : StackSlot)
    (d : Vector Word MAX_N) (pos vacant : Word) (p : Vector Word MAX_N)
    (hs : st.size.toNat ≤ cap) :
    placeGroup (restoreData cap old st) leader (by simpa only [restoreData_size] using hl) slot d pos vacant p =
      placeGroup st leader hl slot d pos vacant p := by
  conv => lhs; rw [placeGroup]
  conv => rhs; rw [placeGroup]
  simp only [restoreData_size]
  split
  · rename_i hp
    have hpc : pos.toNat < cap := by
      have hp' := BitVec.le_def.mp hp
      have hl' := BitVec.lt_def.mp hl
      omega
    rw [restoreData_get cap old st pos hpc]
    split
    · exact restoreData_placeGroup leader hl slot d _ _ _ hs
    · split
      · exact restoreData_placeGroup leader hl slot d _ _ _ hs
      · rw [restoreData_nextVacant cap old st leader slot d vacant hs]
        split
        · rfl
        · exact restoreData_placeGroup leader hl slot d _ _ _ hs
  · rfl
termination_by (leader + 1#64 - pos).toNat
decreasing_by all_goals
  have hleader := hl
  bv_omega

theorem restoreData_regroup (leader : Word) (p d : Vector Word MAX_N)
    (hs : st.size.toNat ≤ cap) :
    regroup (restoreData cap old st) leader p d = regroup st leader p d := by
  conv => lhs; rw [regroup]
  conv => rhs; rw [regroup]
  simp only [restoreData_size]
  split
  · rename_i hl
    have hlc : leader.toNat < cap := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hl) hs
    rw [restoreData_get cap old st leader hlc,
      restoreData_shallowestCopyPosition cap old st _ hs]
    split
    · exact restoreData_regroup _ _ _ hs
    · simp only [restoreData_markDesired cap old st leader hl _ p 0 d hs,
        restoreData_placeGroup cap old st leader hl _ _ 0 0 p hs]
      cases he : placeGroup st leader hl (get st.data leader)
          (markDesired st leader hl (get st.data leader) p 0 d) 0 0 p with
      | none => rfl
      | some q =>
        exact restoreData_regroup _ _ _ hs
  · rfl
termination_by (st.size - leader).toNat
decreasing_by all_goals exact sub_succ_lt (by assumption)

theorem restoreData_scanStep (planned : Vector Word MAX_N) (pos destination : Word)
    (sc : Scan) :
    scanStep planned (restoreData cap old st) pos destination sc =
      scanStep planned st pos destination sc := by
  unfold scanStep
  simp only [restoreData_size]

theorem restoreData_scan (planned : Vector Word MAX_N) (pos : Word) (sc : Scan) :
    scan planned (restoreData cap old st) pos sc = scan planned st pos sc := by
  conv => lhs; rw [scan]
  conv => rhs; rw [scan]
  simp only [restoreData_size, restoreData_targetSize, restoreData_dest]
  split
  · split
    · rfl
    · split
      · rfl
      · rw [restoreData_scanStep]
        exact restoreData_scan planned _ _
  · rfl
termination_by (st.size - pos).toNat
decreasing_by bv_omega

end
end Bbu.Flat
