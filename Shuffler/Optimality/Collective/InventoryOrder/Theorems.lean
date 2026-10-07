import Shuffler.Optimality.Collective.InventoryOrder
import Shuffler.Optimality.Collective.UnitSchedule.Theorems
import Shuffler.Optimality.Collective.InventoryBound
import Shuffler.Optimality.Collective.DeadlineCounts

namespace Shuffler.Optimality.Collective

theorem birthJobs_toFinset (source target : Stack) :
    (birthJobs source target).toFinset = newPositions source target := by
  ext index
  simp [birthJobs]

theorem birthJobs_nodup (source target : Stack) : (birthJobs source target).Nodup :=
  (List.nodup_finRange _).filter _

theorem deadlineOrigin_le (selected : Finset (Interval target)) (index : Fin target.length) :
    deadlineOrigin selected index ≤ index.val := by
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem FeasiblePaidIntervals.unitCapacity
    (hfeasible : FeasiblePaidIntervals source target selected) :
    UnitCapacity (birthJobs source target) (birthDeadline 16 source.length selected) := by
  apply (unitCapacity_iff_jobBounds _ _).mpr
  intro index _
  let cut := deadlineOrigin selected index + 1
  have hcut : cut ≤ target.length := by
    have := deadlineOrigin_le selected index
    have := index.isLt
    omega
  have hpaid : ∀ gap ∈ selected, gap.Paid source := by
    intro gap hg
    exact (Finset.mem_filter.mp (hfeasible.1 hg)).2
  have hc := hfeasible.2 ⟨cut, by omega⟩ (Nat.succ_pos _)
  have hb := (deadline_capacity_iff source target selected hpaid cut 16 hcut).mpr hc
  have he : (birthJobs source target).toFinset.filter
      (fun other => birthDeadline 16 source.length selected other ≤
        birthDeadline 16 source.length selected index) = dueBefore source target selected cut := by
    rw [birthJobs_toFinset]
    ext other
    rw [mem_dueBefore_iff_deadline source target selected cut 16 other]
    constructor
    · intro hh
      obtain ⟨hmem, hbound⟩ := Finset.mem_filter.mp hh
      refine ⟨hmem, ?_⟩
      dsimp [birthDeadline, cut] at hbound ⊢
      omega
    · rintro ⟨hmem, hbound⟩
      apply Finset.mem_filter.mpr
      refine ⟨hmem, ?_⟩
      dsimp [birthDeadline, cut] at hbound ⊢
      omega
  rw [he]
  unfold birthDeadline
  dsimp [cut] at hb ⊢
  omega

-- This is a deadline schedule. A stack realization must also establish
-- where the parent copies are and account for its SWAP operations.
theorem birthOrder_meetsDeadlines (source target : Stack)
    (selected : Finset (Interval target))
    (hfeasible : FeasiblePaidIntervals source target selected) :
    MeetsDeadlines (birthDeadline 16 source.length selected) (birthOrder source target selected) :=
  unitOrder_meetsDeadlines _ _ (birthJobs_nodup source target) hfeasible.unitCapacity

theorem birthOrder_perm (source target : Stack) (selected : Finset (Interval target)) :
    (birthOrder source target selected).Perm (birthJobs source target) := unitOrder_perm _ _

end Shuffler.Optimality.Collective
