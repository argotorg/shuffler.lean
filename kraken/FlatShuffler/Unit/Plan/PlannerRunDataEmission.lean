module

public import FlatShuffler.Unit.Plan.PlannerRunDataSurplus
import all FlatShuffler.Unit.Plan.PlannerRunDataSurplus
public import FlatShuffler.Unit.Plan.PlannerRunDataChecks
import all FlatShuffler.Unit.Plan.PlannerRunDataChecks
public import FlatShuffler.Unit.Plan.PlannerRunDataPermute
import all FlatShuffler.Unit.Plan.PlannerRunDataPermute
public import FlatShuffler.Unit.Plan.PlannerRunDataLoop
import all FlatShuffler.Unit.Plan.PlannerRunDataLoop

@[expose] public section

namespace FlatShuffler.Flat

set_option maxRecDepth 4096

theorem restoreData_eq_of_le (cap : Nat) (old : Vector StackSlot maxStackSize)
    (st : St) (hc : maxStackSize ≤ cap) : restoreData cap old st = st := by
  have hd : (Vector.ofFn fun i : Fin maxStackSize =>
      if i.val < cap then st.data[i.val] else old[i.val]) = st.data := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Nat.lt_of_lt_of_le hi hc, ↓reduceIte]
  unfold restoreData
  rw [hd]

theorem restoreData_finish (cap : Nat) (old : Vector StackSlot maxStackSize)
    (st : St) (hs : st.size.toNat ≤ cap) (hn : st.targetSize.toNat ≤ cap)
    (hf : Unit.RunU.checks st → FInv st) :
    Unit.RunU.finish (restoreData cap old st) =
      let r := Unit.RunU.finish st; (r.1, restoreData cap old r.2) := by
  unfold Unit.RunU.finish
  simp only [restoreData_size, restoreData_pend, restoreData_targetSize,
    restoreData_unmappedFrom, restoreData_availableFrom cap old st _ hs,
    restoreData_labelsFrom]
  by_cases hsz : st.size + st.pend ≠ st.targetSize
  · rw [ite_eq_left hsz, ite_eq_left hsz]
  · rw [ite_eq_right hsz, ite_eq_right hsz]
    by_cases hu : unmappedFrom st 0#64 0#64 ≠ st.pend
    · rw [ite_eq_left hu, ite_eq_left hu]
    · rw [ite_eq_right hu, ite_eq_right hu]
      by_cases ha : (!availableFrom st 0#64) = true
      · rw [ite_eq_left ha, ite_eq_left ha]
      · rw [ite_eq_right ha, ite_eq_right ha]
        by_cases hl : (!labelsFrom st 0#64) = true
        · rw [ite_eq_left hl, ite_eq_left hl]
        · rw [ite_eq_right hl, ite_eq_right hl]
          have hc : Unit.RunU.checks st :=
            ⟨Decidable.not_not.mp hsz, Decidable.not_not.mp hu,
              by cases he : availableFrom st 0#64 <;> simp_all,
              by cases he : labelsFrom st 0#64 <;> simp_all⟩
          apply restoreData_buildBottomUp cap old st (hf hc) hn
          intro mid hm he hc
          exact restoreData_permuteMapping cap old mid
            (Nat.le_trans hm.size_le hm.n)
            (Nat.le_trans hm.size_le hc) (hm.permOk he)

theorem restoreData_emissionRun (cap : Nat) (old : Vector StackSlot maxStackSize)
    (planned : Vector Word maxStackSize) (l : Locals) (st : St) {x : Nat}
    (hs : st.size.toNat ≤ cap) (hn : st.targetSize.toNat ≤ cap)
    (hsafe : Unit.RunU.Safe planned st x) :
    emissionRun planned l (restoreData cap old st) =
      let r := emissionRun planned l st; (r.1, restoreData cap old r.2) := by
  by_cases hc : maxStackSize ≤ cap
  · simp only [restoreData_eq_of_le cap old _ hc]
  have hcap : cap ≤ maxStackSize := Nat.le_of_lt (Nat.lt_of_not_ge hc)
  have hsa : (removeSurplus st).2.size.toNat ≤ cap :=
    Nat.le_trans (removeSurplus_size_le st) hs
  have hna : (removeSurplus st).2.targetSize.toNat ≤ cap := by
    rw [Unit.PlannerRunU.removeSurplus_target]
    exact hn
  unfold emissionRun
  rw [restoreData_removeSurplus cap old st hs]
  dsimp only
  by_cases hd : (removeSurplus st).1 ≠ .done
  · rw [ite_eq_left hd, ite_eq_left hd]
  · rw [ite_eq_right hd, ite_eq_right hd]
    have hdone : (removeSurplus st).1 = .done := Decidable.not_not.mp hd
    rw [restoreData_permuteAtLowestHeight cap old planned l (removeSurplus st).2
      (Nat.le_trans hsa hcap) hsa (hsafe.lowest hdone).2.2]
    dsimp only
    by_cases hl : (permuteAtLowestHeight planned l (removeSurplus st).2).1 ≠ .done
    · rw [ite_eq_left hl, ite_eq_left hl]
    · rw [ite_eq_right hl, ite_eq_right hl]
      have hfields := permuteAtLowestHeight_fields planned l (removeSurplus st).2
      have hsb : (permuteAtLowestHeight planned l (removeSurplus st).2).2.size.toNat ≤ cap := by
        rw [hfields.1]
        exact hsa
      have hnb : (permuteAtLowestHeight planned l (removeSurplus st).2).2.targetSize.toNat ≤ cap := by
        rw [hfields.2]
        exact hna
      exact restoreData_finish cap old _ hsb hnb
        (fun checks => (hsafe.loop l hdone (Decidable.not_not.mp hl) checks).f)

end FlatShuffler.Flat
