import Shuffler.Optimality.Collective.Inventory
import Shuffler.Optimality.Collective.HeightCut

namespace Shuffler.Optimality.Collective

open Shuffler.Placement

theorem mandatory_count (source target : Stack) (cut : Nat) (value : Value) :
    (mandatory source target cut).count value = source.count value - (target.take cut).count value := by
  unfold mandatory
  rw [Multiset.count_sub]
  simp only [Multiset.coe_count]

theorem residual_length_le (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (hcut : 0 < cut) :
    (residual cut trace).length ≤ 16 := by
  have hh := takeHeight_length (height := cut + 16) trace hpop (by omega)
  simp only [residual, List.length_drop]
  omega

theorem mandatory_le_residual (trace : Trace spills source target) (hpop : trace.noPop) :
    mandatory source target cut ≤ (residual cut trace : Multiset Value) := by
  let split := takeHeight (cut + 16) trace
  have hp := (takeHeight_noPop (height := cut + 16) trace hpop).1
  have hb := split.before.noPop_balance hp
  have hs : (source : Multiset Value) ≤ (split.current : Multiset Value) := by
    rw [hb]
    exact Multiset.le_add_right _ _
  have hfixed := takeHeight_take (cut := cut) trace hpop
  unfold mandatory
  apply Multiset.sub_le_iff_le_add'.mpr
  change (source : Multiset Value) ≤ (target.take cut : Multiset Value) +
    (split.current.drop cut : Multiset Value)
  rw [← hfixed, Multiset.coe_add, List.take_append_drop]
  exact hs

theorem mandatory_card_le (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (hcut : 0 < cut) :
    (mandatory source target cut).card ≤ 16 := by
  have hh := Multiset.card_le_card (mandatory_le_residual (cut := cut) trace hpop)
  simpa only [Multiset.coe_card] using hh.trans (residual_length_le trace hpop hsource hcut)

theorem Interval.Paid.count_zero (gap : Interval target) (hpaid : gap.Paid source)
    (hcross : gap.Crosses cut) : (mandatory source target cut).count gap.value = 0 := by
  rw [mandatory_count]
  have hh : (target.take (gap.start.val + 1)).count gap.value ≤
      (target.take cut).count gap.value :=
    (List.take_sublist_take_left (by have := hcross.1; omega)).count_le _
  unfold Interval.Paid at hpaid
  omega

-- Each crossing paid interval has a different value, and each such value
-- uses a slot beyond the mandatory old inventory.
theorem paid_crossing_capacity (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (hcut : 0 < cut)
    (selected : Finset (Interval target))
    (hpaid : ∀ gap ∈ selected, gap.Paid source)
    (hresident : ∀ gap ∈ selected, gap.Crosses cut → gap.value ∈ residual cut trace) :
    (mandatory source target cut).card +
      (selected.filter fun gap => gap.Crosses cut).card ≤ 16 := by
  let crossed := selected.filter fun gap => gap.Crosses cut
  let kinds := crossed.image Interval.value
  have hinj : Set.InjOn (Interval.value (fresh := target)) (crossed : Set (Interval target)) := by
    intro left hl right hr he
    exact Interval.eq_of_crosses_of_value_eq left right cut
      (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hr).2 he
  have hk : kinds.card = crossed.card := Finset.card_image_iff.mpr hinj
  have hresources : mandatory source target cut + kinds.val ≤
      (residual cut trace : Multiset Value) := by
    apply Multiset.le_iff_count.mpr
    intro value
    rw [Multiset.count_add]
    by_cases hv : value ∈ kinds
    · obtain ⟨gap, hg, he⟩ := Finset.mem_image.mp hv
      have hselected := (Finset.mem_filter.mp hg).1
      have hcross := (Finset.mem_filter.mp hg).2
      have hz := Interval.Paid.count_zero gap (hpaid gap hselected) hcross
      rw [he] at hz
      have hr : value ∈ residual cut trace := he ▸ hresident gap hselected hcross
      have hc : kinds.val.count value = 1 := Multiset.count_eq_one_of_mem kinds.nodup hv
      rw [hz, hc, Nat.zero_add]
      exact Multiset.one_le_count_iff_mem.mpr hr
    · have hc : kinds.val.count value = 0 := Multiset.count_eq_zero_of_notMem hv
      rw [hc, Nat.add_zero]
      exact Multiset.count_le_of_le value (mandatory_le_residual trace hpop)
  have hh := Multiset.card_le_card hresources
  simp only [Multiset.card_add, Finset.card_val, Multiset.coe_card, hk] at hh
  exact hh.trans (residual_length_le trace hpop hsource hcut)

end Shuffler.Optimality.Collective
