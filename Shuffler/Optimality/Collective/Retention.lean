import Shuffler.Optimality.Collective.Inventory.Theorems
import Shuffler.Optimality.Collective.TraceDirect

namespace Shuffler.Optimality.Collective

open Shuffler.Placement

theorem Interval.count_take_eq (gap : Interval target) (hcross : gap.Crosses cut) :
    (target.take (gap.start.val + 1)).count gap.value = (target.take cut).count gap.value := by
  have hz : ((target.take cut).drop (gap.start.val + 1)).count gap.value = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hm
    obtain ⟨offset, hi, hv⟩ := List.mem_drop_iff_getElem.mp hm
    have hidx : gap.start.val + 1 + offset < target.length := by
      simp only [List.length_take] at hi
      omega
    have hne := gap.property.2.2 ⟨gap.start.val + 1 + offset, hidx⟩
      (by change gap.start.val < gap.start.val + 1 + offset; omega)
      (by change gap.start.val + 1 + offset < gap.stop.val
          simp only [List.length_take] at hi
          have := hcross.2
          omega)
    apply hne
    change target[gap.start.val + 1 + offset] = gap.value
    simpa only [List.getElem_take] using hv
  have he := congrArg (List.count gap.value)
    (List.take_append_drop (gap.start.val + 1) (target.take cut))
  simp only [List.count_append, List.take_take,
    Nat.min_eq_left (show gap.start.val + 1 ≤ cut by have := hcross.1; omega), hz,
    Nat.add_zero] at he
  exact he

-- The selection is read from one trace. It does not run a second scheduler.
def retained (trace : Trace spills source target) : Finset (Interval target) :=
  Finset.univ.filter fun gap => gap.Paid source ∧
    gap.value ∈ residual (gap.start.val + 1) trace

theorem retained_paid (trace : Trace spills source target) (gap : Interval target)
    (hgap : gap ∈ retained trace) : gap.Paid source :=
  (Finset.mem_filter.mp hgap).2.1

theorem retained_resident (trace : Trace spills source target) (hpop : trace.noPop)
    (gap : Interval target) (hgap : gap ∈ retained trace) (hcross : gap.Crosses cut) :
    gap.value ∈ residual cut trace := by
  apply residual_mem_of_mem trace hpop
    (show gap.start.val + 1 ≤ cut by have := hcross.1; omega) gap.value
    (gap.count_take_eq hcross)
  exact (Finset.mem_filter.mp hgap).2.2

theorem retained_capacity (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (hcut : 0 < cut) :
    (mandatory source target cut).card +
      ((retained trace).filter fun gap => gap.Crosses cut).card ≤ 16 :=
  paid_crossing_capacity trace hpop hsource hcut (retained trace)
    (retained_paid trace) (retained_resident trace hpop)

theorem unretained_direct_increase (trace : Trace spills source target) (hpop : trace.noPop)
    (gap : Interval target) (hpaid : gap.Paid source) (hgap : gap ∉ retained trace) :
    directBefore gap.value (gap.start.val + 1) trace <
      directBefore gap.value (gap.stop.val + 1) trace := by
  apply directBefore_lt_between trace hpop gap.value
    (show gap.start.val + 1 ≤ gap.stop.val + 1 by
      have hlt : gap.start.val < gap.stop.val := gap.property.1
      omega)
  · intro hm
    exact hgap (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpaid, hm⟩)
  · have hi : gap.stop.val < (target.take (gap.stop.val + 1)).length := by
      simp only [List.length_take]
      have := gap.stop.isLt
      omega
    have hm := getElem_mem_drop_of_le (target.take (gap.stop.val + 1))
      ⟨gap.stop.val, hi⟩ (gap.start.val + 1)
      (by change gap.start.val + 1 ≤ gap.stop.val
          have hlt : gap.start.val < gap.stop.val := gap.property.1
          omega)
    change (target.take (gap.stop.val + 1))[gap.stop.val] ∈
      (target.take (gap.stop.val + 1)).drop (gap.start.val + 1) at hm
    rw [List.getElem_take] at hm
    have hv : target[gap.stop.val] = gap.value := gap.property.2.1.symm
    rwa [hv] at hm

end Shuffler.Optimality.Collective
