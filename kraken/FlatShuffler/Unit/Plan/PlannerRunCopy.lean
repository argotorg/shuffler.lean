module

public import FlatShuffler.Unit.Plan.PlannerRunMapping
import all FlatShuffler.Unit.Plan.PlannerRunMapping

@[expose] public section

/-! The copies made by `Planner::run` preserve buffer entries outside the
copied range. The equations concern the production flat model. -/

namespace FlatShuffler.Unit.PlannerRunU
open Flat

theorem copyFrom_before (pl : Flat.Planner) (i q : Word)
    (data : Vector StackSlot maxStackSize) (hq : q < i) :
    get (Flat.copyFrom pl i data) q = get data q := by
  rw [Flat.copyFrom]
  split
  · rename_i hi
    rw [copyFrom_before pl (i + 1) q _ (by bv_omega), get_put_ne _ _ (by bv_omega)]
  · rfl
termination_by (pl.sourceSize - i).toNat
decreasing_by exact Flat.sub_succ_lt ‹i < pl.sourceSize›

theorem copyFrom_after (pl : Flat.Planner) (i q : Word)
    (data : Vector StackSlot maxStackSize) (hq : pl.sourceSize ≤ q) :
    get (Flat.copyFrom pl i data) q = get data q := by
  rw [Flat.copyFrom]
  split
  · rename_i hi
    rw [copyFrom_after pl (i + 1) q _ hq, get_put_ne _ _ (by bv_omega)]
  · rfl
termination_by (pl.sourceSize - i).toNat
decreasing_by exact Flat.sub_succ_lt ‹i < pl.sourceSize›

theorem copyFrom_source (pl : Flat.Planner) (i q : Word)
    (data : Vector StackSlot maxStackSize) (hm : pl.sourceSize.toNat ≤ maxStackSize)
    (hi : i ≤ q) (hq : q < pl.sourceSize) :
    get (Flat.copyFrom pl i data) q = get pl.source q := by
  have him : i < pl.sourceSize := by bv_omega
  rw [Flat.copyFrom, dite_eq_left him]
  by_cases hqi : q = i
  · rw [copyFrom_before pl (i + 1) q _ (by bv_omega), hqi,
      get_put_self _ _ (Nat.lt_of_lt_of_le (BitVec.lt_def.mp him) hm)]
  · exact copyFrom_source pl (i + 1) q _ hm (by bv_omega) hq
termination_by (pl.sourceSize - i).toNat
decreasing_by exact Flat.sub_succ_lt him

theorem copy_source (pl : Flat.Planner) (data : Vector StackSlot maxStackSize)
    (hm : pl.sourceSize.toNat ≤ maxStackSize) {q : Word} (hq : q < pl.sourceSize) :
    get (Flat.copyFrom pl 0 data) q = get pl.source q :=
  copyFrom_source pl 0 q data hm (by bv_omega) hq

theorem sourcesFrom_before (n i q : Word) (M : Flat.Mapping)
    (sources : Vector Word maxStackSize) (hq : q < i) :
    get (Flat.sourcesFrom n i M sources) q = get sources q := by
  rw [Flat.sourcesFrom]
  split
  · rename_i hi
    rw [sourcesFrom_before n (i + 1) q M _ (by bv_omega), get_put_ne _ _ (by bv_omega)]
  · rfl
termination_by (n - i).toNat
decreasing_by exact Flat.sub_succ_lt ‹i < n›

theorem sourcesFrom_after (n i q : Word) (M : Flat.Mapping)
    (sources : Vector Word maxStackSize) (hq : n ≤ q) :
    get (Flat.sourcesFrom n i M sources) q = get sources q := by
  rw [Flat.sourcesFrom]
  split
  · rename_i hi
    rw [sourcesFrom_after n (i + 1) q M _ hq, get_put_ne _ _ (by bv_omega)]
  · rfl
termination_by (n - i).toNat
decreasing_by exact Flat.sub_succ_lt ‹i < n›

theorem sourcesFrom_mapping (n i q : Word) (M : Flat.Mapping)
    (sources : Vector Word maxStackSize) (hn : n.toNat ≤ maxStackSize)
    (hi : i ≤ q) (hq : q < n) :
    get (Flat.sourcesFrom n i M sources) q = get M.pos q := by
  have hin : i < n := by bv_omega
  rw [Flat.sourcesFrom, dite_eq_left hin]
  by_cases hqi : q = i
  · rw [sourcesFrom_before n (i + 1) q M _ (by bv_omega), hqi,
      get_put_self _ _ (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hin) hn)]
  · exact sourcesFrom_mapping n (i + 1) q M _ hn (by bv_omega) hq
termination_by (n - i).toNat
decreasing_by exact Flat.sub_succ_lt hin

theorem sources_mapping (n : Word) (M : Flat.Mapping) (sources : Vector Word maxStackSize)
    (hn : n.toNat ≤ maxStackSize) {q : Word} (hq : q < n) :
    get (Flat.sourcesFrom n 0 M sources) q = get M.pos q :=
  sourcesFrom_mapping n 0 q M sources hn (by bv_omega) hq

end FlatShuffler.Unit.PlannerRunU
