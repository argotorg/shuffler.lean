import Shuffler.Optimality.Baseline
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Shuffler.Optimality.Collective

def IsInterval (fresh : Stack) (pair : Fin fresh.length × Fin fresh.length) : Prop :=
  pair.1 < pair.2 ∧ fresh[pair.1] = fresh[pair.2] ∧
    ∀ index : Fin fresh.length, pair.1 < index → index < pair.2 →
      fresh[index] ≠ fresh[pair.1]

instance (fresh : Stack) (pair : Fin fresh.length × Fin fresh.length) :
    Decidable (IsInterval fresh pair) := by unfold IsInterval; infer_instance

abbrev Interval (fresh : Stack) :=
  {pair : Fin fresh.length × Fin fresh.length // IsInterval fresh pair}

def Interval.start (gap : Interval fresh) : Fin fresh.length := gap.val.1
def Interval.stop (gap : Interval fresh) : Fin fresh.length := gap.val.2
def Interval.value (gap : Interval fresh) : Value := fresh[gap.start]

-- A cut counts outputs already consumed. The interval from positions i to j
-- crosses cuts i+1 through j, including j and excluding i.
def Interval.Crosses (gap : Interval fresh) (cut : Nat) : Prop :=
  gap.start.val < cut ∧ cut ≤ gap.stop.val

instance (gap : Interval fresh) (cut : Nat) : Decidable (gap.Crosses cut) := by
  unfold Interval.Crosses; infer_instance

def FeasibleIntervals (selected : Finset (Interval fresh)) (capacity : Nat) : Prop :=
  ∀ cut : Fin (fresh.length + 1),
    (selected.filter fun gap => gap.Crosses cut.val).card ≤ capacity

instance (selected : Finset (Interval fresh)) (capacity : Nat) :
    Decidable (FeasibleIntervals selected capacity) := by
  unfold FeasibleIntervals; infer_instance

def intervalCount (selected : Finset (Interval fresh)) (value : Value) : Nat :=
  (selected.filter fun gap => gap.value = value).card

def intervalWeight (premium : Value → Nat) (selected : Finset (Interval fresh)) : Nat :=
  selected.sum fun gap => premium gap.value

def UpperCapacityWeight (fresh : Stack) (premium : Value → Nat) (capacity bound : Nat) : Prop :=
  ∀ selected : Finset (Interval fresh), FeasibleIntervals selected capacity →
    intervalWeight premium selected ≤ bound

-- This finite maximum is a specification. Production planning does not
-- import or evaluate it. The lower-bound theorem also accepts any checked
-- UpperCapacityWeight certificate, without enumerating subsets.
def capacityMaximum (fresh : Stack) (premium : Value → Nat) (capacity : Nat) : Nat :=
  ((Finset.univ : Finset (Interval fresh)).powerset.filter fun selected =>
    FeasibleIntervals selected capacity).sup (intervalWeight premium)

theorem capacityMaximum_upper (fresh : Stack) (premium : Value → Nat) (capacity : Nat) :
    UpperCapacityWeight fresh premium capacity (capacityMaximum fresh premium capacity) := by
  intro selected hf
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  exact hf

theorem capacityMaximum_le_of_upper (h : UpperCapacityWeight fresh premium capacity bound) :
    capacityMaximum fresh premium capacity ≤ bound := by
  apply Finset.sup_le
  intro selected hs
  exact h selected (Finset.mem_filter.mp hs).2

theorem Interval.value_mem (gap : Interval fresh) : gap.value ∈ fresh :=
  List.getElem_mem gap.start.isLt

theorem Interval.start_injective : Function.Injective (Interval.start (fresh := fresh)) := by
  intro left right hs
  have hs' : left.val.1 = right.val.1 := hs
  have he : left.val.2 = right.val.2 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hne := right.property.2.2 left.val.2
        (by rw [← hs']; exact left.property.1) hlt
      exact hne (left.property.2.1.symm.trans (congrArg (fun index => fresh[index]) hs'))
    · have hne := left.property.2.2 right.val.2
        (by rw [hs']; exact right.property.1) hgt
      exact hne (right.property.2.1.symm.trans (congrArg (fun index => fresh[index]) hs'.symm))
  exact Subtype.ext (Prod.ext hs' he)

theorem Interval.eq_of_crosses_of_value_eq (left right : Interval fresh) (cut : Nat)
    (hl : left.Crosses cut) (hr : right.Crosses cut) (hv : left.value = right.value) :
    left = right := by
  apply Interval.start_injective
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hstop : right.start < left.stop := by
      change right.start.val < left.stop.val
      exact Nat.lt_of_lt_of_le hr.1 hl.2
    exact left.property.2.2 right.start hlt hstop hv.symm
  · have hstop : left.start < right.stop := by
      change left.start.val < right.stop.val
      exact Nat.lt_of_lt_of_le hl.1 hr.2
    exact right.property.2.2 left.start hgt hstop hv

def occurrencePositions (fresh : Stack) (value : Value) : Finset (Fin fresh.length) :=
  Finset.univ.filter fun index => fresh[index] = value

theorem occurrencePositions_card (fresh : Stack) (value : Value) :
    (occurrencePositions fresh value).card = fresh.count value := by
  exact Fin.card_filter_univ_eq_vector_get_eq_count value ⟨fresh, rfl⟩

theorem all_intervalCount_le (fresh : Stack) (value : Value) :
    intervalCount (Finset.univ : Finset (Interval fresh)) value ≤ fresh.count value - 1 := by
  let gaps : Finset (Interval fresh) := Finset.univ.filter fun gap => gap.value = value
  let starts := gaps.image Interval.start
  let positions := occurrencePositions fresh value
  have hcard : starts.card = gaps.card := Finset.card_image_of_injective _ Interval.start_injective
  have hsub : starts ⊆ positions := by
    intro index hi
    obtain ⟨gap, hg, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hg).2⟩
  by_cases hp : positions.Nonempty
  · let last := positions.max' hp
    have hlast : last ∈ positions := Finset.max'_mem positions hp
    have hn : last ∉ starts := by
      intro hl
      obtain ⟨gap, hg, hs⟩ := Finset.mem_image.mp hl
      have hstop : gap.stop ∈ positions := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact gap.property.2.1.symm.trans (Finset.mem_filter.mp hg).2
      have hle : gap.stop ≤ last := Finset.le_max' positions gap.stop hstop
      have hlt : gap.start < gap.stop := gap.property.1
      rw [hs] at hlt
      exact (not_lt_of_ge hle) hlt
    have hstrict : starts ⊂ positions := Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, by intro he; exact hn (he.symm ▸ hlast)⟩
    have hlt := Finset.card_lt_card hstrict
    change gaps.card ≤ fresh.count value - 1
    rw [← hcard]
    have hcount := occurrencePositions_card fresh value
    change positions.card = fresh.count value at hcount
    omega
  · have hz : positions = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    have hs : starts = ∅ := Finset.subset_empty.mp (hz ▸ hsub)
    change gaps.card ≤ fresh.count value - 1
    rw [← hcard, hs, Finset.card_empty]
    exact Nat.zero_le _

theorem intervalWeight_eq_sum_counts (premium : Value → Nat)
    (selected : Finset (Interval fresh)) :
    intervalWeight premium selected =
      fresh.toFinset.sum (fun value => intervalCount selected value * premium value) := by
  have hmem : ∀ gap ∈ selected, gap.value ∈ fresh.toFinset := by
    intro gap _
    exact List.mem_toFinset.mpr gap.value_mem
  unfold intervalWeight
  rw [← Finset.sum_fiberwise_of_maps_to hmem]
  apply Finset.sum_congr rfl
  intro value _
  apply Finset.sum_const_nat
  intro gap hg
  rw [(Finset.mem_filter.mp hg).2]

def laterDirectPremium (fresh : Stack) (premium directCount : Value → Nat) : Nat :=
  fresh.toFinset.sum fun value => (directCount value - 1) * premium value

-- A selected interval can save one later direct introduction. This theorem
-- is independent of any trace or planner. A trace proof must supply the
-- capacity condition and the per-value introduction counts explicitly.
theorem interval_floor_le_later_direct (fresh : Stack) (premium directCount : Value → Nat)
    (selected : Finset (Interval fresh)) (capacity bound : Nat)
    (hcapacity : FeasibleIntervals selected capacity)
    (hbound : UpperCapacityWeight fresh premium capacity bound)
    (hpositive : ∀ value ∈ fresh, 0 < directCount value)
    (hcount : ∀ value ∈ fresh,
      fresh.count value - directCount value ≤ intervalCount selected value) :
    intervalWeight premium (Finset.univ : Finset (Interval fresh)) - bound ≤
      laterDirectPremium fresh premium directCount := by
  have hsaved := hbound selected hcapacity
  have htotal : intervalWeight premium (Finset.univ : Finset (Interval fresh)) ≤
      laterDirectPremium fresh premium directCount + intervalWeight premium selected := by
    rw [intervalWeight_eq_sum_counts, intervalWeight_eq_sum_counts, laterDirectPremium,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro value hv
    have hm := List.mem_toFinset.mp hv
    have hp := hpositive value hm
    have hc := hcount value hm
    have ha := all_intervalCount_le fresh value
    have hl : intervalCount (Finset.univ : Finset (Interval fresh)) value ≤
        directCount value - 1 + intervalCount selected value := by omega
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right (premium value) hl
  omega

theorem maximum_floor_le_later_direct (fresh : Stack) (premium directCount : Value → Nat)
    (selected : Finset (Interval fresh)) (capacity : Nat)
    (hcapacity : FeasibleIntervals selected capacity)
    (hpositive : ∀ value ∈ fresh, 0 < directCount value)
    (hcount : ∀ value ∈ fresh,
      fresh.count value - directCount value ≤ intervalCount selected value) :
    intervalWeight premium (Finset.univ : Finset (Interval fresh)) -
        capacityMaximum fresh premium capacity ≤ laterDirectPremium fresh premium directCount :=
  interval_floor_le_later_direct fresh premium directCount selected capacity _ hcapacity
    (capacityMaximum_upper fresh premium capacity) hpositive hcount

end Shuffler.Optimality.Collective
