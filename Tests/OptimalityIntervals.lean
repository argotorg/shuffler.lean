import Shuffler.Optimality.Collective.Intervals

open Shuffler.Optimality.Collective

namespace OptimalityIntervalsTests

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def fresh : Stack := [a,b,a,b]
private def premium (value : Value) : Nat := if value = a then 3 else 5
private def direct (value : Value) : Nat := if value = a then 2 else 1
private def selected : Finset (Interval fresh) := Finset.univ.filter fun gap => gap.value = b

#guard (Finset.univ : Finset (Interval fresh)).card = 2
#guard intervalWeight premium (Finset.univ : Finset (Interval fresh)) = 8
#guard !FeasibleIntervals (Finset.univ : Finset (Interval fresh)) 1
#guard FeasibleIntervals selected 1
#guard capacityMaximum fresh premium 0 = 0
#guard capacityMaximum fresh premium 1 = 5
#guard capacityMaximum fresh premium 2 = 8
#guard capacityMaximum [] premium 0 = 0
#guard laterDirectPremium fresh premium direct = 3

-- One seed slot keeps the weight-5 interval. The other kind needs one
-- later direct introduction, with premium 3.
example : intervalWeight premium (Finset.univ : Finset (Interval fresh)) -
      capacityMaximum fresh premium 1 ≤ laterDirectPremium fresh premium direct := by
  apply maximum_floor_le_later_direct fresh premium direct selected 1 (by decide)
  · intro value _
    unfold direct
    split <;> decide
  · intro value hv
    simp only [fresh, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide

end OptimalityIntervalsTests
