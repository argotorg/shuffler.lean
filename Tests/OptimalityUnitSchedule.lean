import Shuffler.Optimality.Collective.InventoryOrder.Theorems

namespace Tests.OptimalityUnitSchedule

open Shuffler.Optimality.Collective

private def deadline : Nat → Int
  | 0 => 3
  | 1 => 1
  | _ => 2

#guard unitOrder [0, 1, 2] deadline = [1, 2, 0]
#guard MeetsDeadlines deadline (unitOrder [0, 1, 2] deadline)
#guard ¬MeetsDeadlines deadline [0, 1, 2]
#guard unitOrder ([] : List Nat) deadline = []
#guard MeetsDeadlines deadline []
#guard ¬MeetsDeadlines (fun _ : Nat => 0) [0]
#guard ¬MeetsDeadlines (fun _ : Nat => -1) [0]
#guard ¬MeetsDeadlines (fun _ : Nat => 1) [0, 1]

example : UnitCapacity [0, 1, 2] deadline :=
  unitCapacity_of_meetsDeadlines [0, 1, 2] [1, 2, 0] deadline (by decide) (by decide)

example : ¬UnitCapacity [0, 1] (fun _ : Nat => 1) := by
  intro h
  have hm := unitOrder_meetsDeadlines [0, 1] (fun _ : Nat => 1) (by decide) h
  have he : unitOrder [0, 1] (fun _ : Nat => 1) = [0, 1] :=
    List.mergeSort_of_pairwise (by simp)
  rw [he] at hm
  exact (by decide : ¬MeetsDeadlines (fun _ : Nat => 1) [0, 1]) hm

example : UnitCapacity [0, 1, 2] deadline ↔
    ∃ order, order.Perm [0, 1, 2] ∧ MeetsDeadlines deadline order :=
  unitCapacity_iff_exists_order [0, 1, 2] deadline (by decide)

private def old : Value := .Lit 0
private def a : Value := .Lit 1
private def b : Value := .Lit 2
private def source : Stack := List.replicate 15 old
private def target : Stack := [a, b, a, b] ++ source
private def selected : Finset (Interval target) :=
  (paidIntervals source target).filter fun gap => gap.value = b

#guard FeasiblePaidIntervals source target selected
#guard ¬FeasiblePaidIntervals source target (paidIntervals source target)
#guard (birthJobs source target).map Fin.val = [0, 1, 2, 3]
#guard (birthOrder source target selected).map Fin.val = [0, 1, 3, 2]

example : MeetsDeadlines (birthDeadline 16 source.length selected)
    (birthOrder source target selected) :=
  birthOrder_meetsDeadlines source target selected (by decide)

end Tests.OptimalityUnitSchedule
