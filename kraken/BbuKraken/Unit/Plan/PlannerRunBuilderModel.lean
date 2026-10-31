import BbuKraken.Unit.Plan.PlannerRunMapping

namespace Bbu.Unit.PlannerRunU
open Flat

section
variable (b : Flat.Builder) (d : Vector (BitVec 8) MAX_N)
  (hd : ∀ p, p < b.m → get d p = get b.dropped p)

private theorem common_dropped : Flat.commonSize { b with dropped := d } = Flat.commonSize b := rfl
private theorem wildcard_dropped (p : Word) :
    Flat.isWildcardTarget { b with dropped := d } p = Flat.isWildcardTarget b p := rfl
private theorem inWildcard_dropped (p : Word) :
    Flat.inWildcardSlot { b with dropped := d } p = Flat.inWildcardSlot b p := rfl

include hd

theorem mappable_dropped (M : Flat.Mapping) {p : Word} (hp : p < b.m) :
    Flat.mappable { b with dropped := d } M p = Flat.mappable b M p := by
  simp only [Flat.mappable, hd p hp]

theorem mbMap_dropped (M : Flat.Mapping) {p : Word} (hp : p = NONE ∨ p < b.m)
    (t : Word) : Flat.mbMap { b with dropped := d } M p t = Flat.mbMap b M p t := by
  rcases hp with rfl | hp
  · rw [mbMap_none, mbMap_none]
  · simp only [Flat.mbMap, mappable_dropped b d hd M hp]

theorem closestFrom_dropped (M : Flat.Mapping) (t : Word) (inW : Bool) (i best : Word) :
    Flat.closestFrom { b with dropped := d } M t inW i best =
      Flat.closestFrom b M t inW i best := by
  conv => lhs; rw [Flat.closestFrom]
  conv => rhs; rw [Flat.closestFrom]
  try dsimp only
  by_cases hi : i < b.m
  · have ih (best' : Word) := closestFrom_dropped M t inW (i + 1) best'
    simp only [hi, ↓reduceDIte, mappable_dropped b d hd M hi, inWildcard_dropped, ih]
  · simp only [hi, ↓reduceDIte]
termination_by (b.m - i).toNat
decreasing_by exact Flat.sub_succ_lt ‹i < b.m›

theorem closestCopy_dropped (M : Flat.Mapping) (t : Word) (inW : Bool) :
    Flat.closestCopy { b with dropped := d } M t inW = Flat.closestCopy b M t inW :=
  closestFrom_dropped b d hd M t inW 0 NONE

theorem inPlaceFrom_dropped (M : Flat.Mapping) (j : Word) :
    Flat.inPlaceFrom { b with dropped := d } M j = Flat.inPlaceFrom b M j := by
  conv => lhs; rw [Flat.inPlaceFrom]
  conv => rhs; rw [Flat.inPlaceFrom]
  simp only [common_dropped]
  try dsimp only
  by_cases hj : j < Flat.commonSize b
  · have hjm : j < b.m := by have hm := common_le_m b; bv_omega
    have ih (M' : Flat.Mapping) := inPlaceFrom_dropped M' (j + 1)
    simp only [hj, ↓reduceDIte, mappable_dropped b d hd M hjm,
      mbMap_dropped b d hd M (Or.inr hjm), ih]
  · simp only [hj, ↓reduceDIte]
termination_by (Flat.commonSize b - j).toNat
decreasing_by exact Flat.sub_succ_lt ‹j < Flat.commonSize b›

theorem closestCopiesFrom_dropped (M : Flat.Mapping) (j : Word) :
    Flat.closestCopiesFrom { b with dropped := d } M j = Flat.closestCopiesFrom b M j := by
  conv => lhs; rw [Flat.closestCopiesFrom]
  conv => rhs; rw [Flat.closestCopiesFrom]
  simp only [wildcard_dropped]
  try dsimp only
  by_cases hj : j < b.n
  · have ih (M' : Flat.Mapping) := closestCopiesFrom_dropped M' (j + 1)
    simp only [hj, ↓reduceDIte, closestCopy_dropped b d hd,
      mbMap_dropped b d hd M (closestCopy_bound b M j false), ih]
  · simp only [hj, ↓reduceDIte]
termination_by (b.n - j).toNat
decreasing_by exact Flat.sub_succ_lt ‹j < b.n›

theorem wildcardFrom_dropped (M : Flat.Mapping) (saw : Bool) (j : Word) :
    Flat.wildcardFrom { b with dropped := d } M saw j = Flat.wildcardFrom b M saw j := by
  conv => lhs; rw [Flat.wildcardFrom]
  conv => rhs; rw [Flat.wildcardFrom]
  simp only [wildcard_dropped]
  try dsimp only
  by_cases hj : j < b.n
  · have ih (M' : Flat.Mapping) (saw' : Bool) := wildcardFrom_dropped M' saw' (j + 1)
    simp only [hj, ↓reduceDIte, closestCopy_dropped b d hd,
      mbMap_dropped b d hd M (closestCopy_bound b M j true), ih]
  · simp only [hj, ↓reduceDIte]
termination_by (b.n - j).toNat
decreasing_by exact Flat.sub_succ_lt ‹j < b.n›

theorem keepFrom_dropped (M : Flat.Mapping) (j : Word) :
    Flat.keepFrom { b with dropped := d } M j = Flat.keepFrom b M j := by
  conv => lhs; rw [Flat.keepFrom]
  conv => rhs; rw [Flat.keepFrom]
  simp only [common_dropped, wildcard_dropped]
  try dsimp only
  by_cases hj : j < Flat.commonSize b
  · have hjm : j < b.m := by have hm := common_le_m b; bv_omega
    have ih (M' : Flat.Mapping) := keepFrom_dropped M' (j + 1)
    simp only [hj, ↓reduceDIte, mappable_dropped b d hd M hjm,
      mbMap_dropped b d hd M (Or.inr hjm), ih]
  · simp only [hj, ↓reduceDIte]
termination_by (Flat.commonSize b - j).toNat
decreasing_by exact Flat.sub_succ_lt ‹j < Flat.commonSize b›

theorem absorbBest_dropped (M : Flat.Mapping) (j o best : Word) :
    Flat.absorbBest { b with dropped := d } M j o best = Flat.absorbBest b M j o best := by
  conv => lhs; rw [Flat.absorbBest]
  conv => rhs; rw [Flat.absorbBest]
  try dsimp only
  by_cases ho : o < b.m
  · have ih (best' : Word) := absorbBest_dropped M j (o + 1) best'
    simp only [ho, ↓reduceDIte, mappable_dropped b d hd M ho, ih]
  · simp only [ho, ↓reduceDIte]
termination_by (b.m - o).toNat
decreasing_by exact Flat.sub_succ_lt ‹o < b.m›

theorem absorbFrom_dropped (M : Flat.Mapping) (j : Word) :
    Flat.absorbFrom { b with dropped := d } M j = Flat.absorbFrom b M j := by
  conv => lhs; rw [Flat.absorbFrom]
  conv => rhs; rw [Flat.absorbFrom]
  simp only [wildcard_dropped]
  try dsimp only
  by_cases hj : j < b.n
  · have ih (M' : Flat.Mapping) := absorbFrom_dropped M' (j + 1)
    simp only [hj, ↓reduceDIte, absorbBest_dropped b d hd,
      mbMap_dropped b d hd M (absorbBest_bound b M j 0 NONE (Or.inl rfl)), ih]
  · simp only [hj, ↓reduceDIte]
termination_by (b.n - j).toNat
decreasing_by exact Flat.sub_succ_lt ‹j < b.n›

theorem buildMapping_dropped (M : Flat.Mapping) :
    Flat.buildMapping { b with dropped := d } M = Flat.buildMapping b M := by
  simp only [Flat.buildMapping, Flat.mapInPlace, Flat.mapClosestCopies,
    Flat.mapWildcardSlotCopies, Flat.keepWildcardSlots, Flat.absorbSurplus,
    inPlaceFrom_dropped b d hd, closestCopiesFrom_dropped b d hd,
    wildcardFrom_dropped b d hd, keepFrom_dropped b d hd, absorbFrom_dropped b d hd]
  rfl

end
end Bbu.Unit.PlannerRunU
