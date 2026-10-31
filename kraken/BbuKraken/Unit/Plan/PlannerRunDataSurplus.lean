import BbuKraken.Unit.Plan.PlannerRunDataFrame
import BbuKraken.Unit.Plan.PlannerRunBlockedSurplus

namespace Bbu.Flat

set_option maxRecDepth 4096

theorem restoreData_stackPop (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    stackPop (restoreData cap old st) =
      let r := stackPop st; (r.1, restoreData cap old r.2) := by
  unfold stackPop restoreData
  split <;> rfl

theorem restoreData_mappingPop (cap : Nat) (old : Vector StackSlot MAX_N) (st : St)
    (top : Word) :
    mappingPop (restoreData cap old st) top = restoreData cap old (mappingPop st top) := by
  unfold mappingPop
  dsimp only
  rw [restoreData_dest]
  split <;> rfl

theorem restoreData_pop (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    pop (restoreData cap old st) =
      let r := pop st; (r.1, restoreData cap old r.2) := by
  simp only [pop, restoreData_size, restoreData_stackPop]
  split
  · rfl
  · simp only [restoreData_mappingPop]

theorem restoreData_surplusScan (cap : Nat) (old : Vector StackSlot MAX_N) (st : St)
    (p sh dp : Word) :
    surplusScan (restoreData cap old st) p sh dp = surplusScan st p sh dp := by
  conv => lhs; rw [surplusScan]
  conv => rhs; rw [surplusScan]
  simp only [isSurplus, restoreData_dest, isSwapReachable, depthOf, restoreData_size]
  split
  · rfl
  · split <;> simp_all only [↓reduceIte]
    all_goals exact restoreData_surplusScan cap old st _ _ _
termination_by p.toNat
decreasing_by all_goals bv_omega

theorem restoreData_equalBelow (cap : Nat) (old : Vector StackSlot MAX_N) (st : St)
    (p : Word) (hp : p ≤ st.size) (hs : st.size.toNat ≤ cap) :
    equalBelow (restoreData cap old st) p = equalBelow st p := by
  conv => lhs; rw [equalBelow]
  conv => rhs; rw [equalBelow]
  simp only [BitVec.ofNat_eq_ofNat]
  split
  · rfl
  · rename_i h0
    have hi : (p - 1#64).toNat < cap := by bv_omega
    have ht : (st.size - 1#64).toNat < cap := by bv_omega
    rw [restoreData_size, restoreData_get cap old st _ hi,
      restoreData_get cap old st _ ht]
    simp only [isSurplus, restoreData_dest]
    split <;> simp_all only [↓reduceIte]
    · rfl
    · exact restoreData_equalBelow cap old st (p - 1#64) (by bv_omega) hs
termination_by p.toNat
decreasing_by bv_omega

theorem pop_size_le (st : St) : (pop st).2.size.toNat ≤ st.size.toNat := by
  unfold pop stackPop mappingPop
  dsimp only
  split
  · rw [ite_eq_left (show Status.assertionFailed ≠ .done from by decide)]
    exact Nat.le_refl _
  · rename_i h0
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    split <;> dsimp only <;> bv_omega

theorem surplus_action_size (st : St) (sh dp : Word) :
    (if sh = st.size - 1 then (.done, st)
      else if equalBelow st (st.size - 1) ≠ NONE then
        (.done, swapDestinations st (equalBelow st (st.size - 1)) (st.size - 1))
      else swapWith st dp).2.size = st.size := by
  split
  · rfl
  · split
    · rfl
    · exact swapWith_size st dp

theorem surplusPass_size_le (st : St) :
    match surplusPass st with
    | .error r => r.2.size.toNat ≤ st.size.toNat
    | .ok mid => mid.size.toNat ≤ st.size.toNat := by
  unfold surplusPass
  generalize hsc : surplusScan st st.size NONE NONE = sc
  obtain ⟨sh, dp⟩ := sc
  dsimp only
  by_cases hsh : sh = NONE
  · simp only [hsh, ↓reduceIte, Nat.le_refl]
  · simp only [hsh, ↓reduceIte]
    by_cases hdp : dp = NONE
    · simp only [hdp, ↓reduceIte]
      unfold blockSwapUnreachable block
      split <;> exact Nat.le_refl _
    · simp only [hdp, ↓reduceIte]
      have hs := surplus_action_size st sh dp
      generalize ha : (if sh = st.size - 1 then
          (Status.done, st)
        else if equalBelow st (st.size - 1) ≠ NONE then
          (.done, swapDestinations st (equalBelow st (st.size - 1)) (st.size - 1))
        else swapWith st dp) = r at hs ⊢
      by_cases hd : r.1 ≠ .done
      · rw [ite_eq_left hd]
        exact Nat.le_of_eq (congrArg BitVec.toNat hs)
      · rw [ite_eq_right hd]
        have hp := pop_size_le r.2
        rw [hs] at hp
        by_cases he : (pop r.2).1 ≠ .done
        · rw [ite_eq_left he]; exact hp
        · rw [ite_eq_right he]; exact hp

theorem restoreData_surplusTail (cap : Nat) (old : Vector StackSlot MAX_N)
    (r : Status × St) :
    (if r.1 ≠ .done then Except.error (r.1, restoreData cap old r.2) else
      if (pop (restoreData cap old r.2)).1 ≠ .done then
        Except.error (pop (restoreData cap old r.2))
      else Except.ok (pop (restoreData cap old r.2)).2) =
      ((if r.1 ≠ .done then Except.error r else
        if (pop r.2).1 ≠ .done then Except.error (pop r.2)
        else Except.ok (pop r.2).2).map (restoreData cap old)).mapError
          (fun r => (r.1, restoreData cap old r.2)) := by
  by_cases hd : r.1 ≠ .done
  · rw [ite_eq_left hd, ite_eq_left hd]
    rfl
  · rw [ite_eq_right hd, ite_eq_right hd, restoreData_pop]
    dsimp only
    by_cases hp : (pop r.2).1 ≠ .done
    · rw [ite_eq_left hp, ite_eq_left hp]; rfl
    · rw [ite_eq_right hp, ite_eq_right hp]; rfl

theorem restoreData_surplusPass (cap : Nat) (old : Vector StackSlot MAX_N) (st : St)
    (h0 : st.size ≠ 0#64) (hs : st.size.toNat ≤ cap) :
    surplusPass (restoreData cap old st) =
      ((surplusPass st).map (restoreData cap old)).mapError
        (fun r => (r.1, restoreData cap old r.2)) := by
  have he := restoreData_equalBelow cap old st (st.size - 1#64) (by bv_omega) hs
  have ha : (if (surplusScan st st.size NONE NONE).1 = st.size - 1 then
        (.done, restoreData cap old st)
      else if equalBelow st (st.size - 1) ≠ NONE then
        (.done, restoreData cap old
          (swapDestinations st (equalBelow st (st.size - 1)) (st.size - 1)))
      else swapWith (restoreData cap old st) (surplusScan st st.size NONE NONE).2) =
      let r := (if (surplusScan st st.size NONE NONE).1 = st.size - 1 then
        (.done, st)
      else if equalBelow st (st.size - 1) ≠ NONE then
        (.done, swapDestinations st (equalBelow st (st.size - 1)) (st.size - 1))
      else swapWith st (surplusScan st st.size NONE NONE).2)
      (r.1, restoreData cap old r.2) := by
    split
    · rfl
    · split
      · rfl
      · exact restoreData_swapWith cap old st _ hs
  unfold surplusPass
  dsimp only
  simp only [restoreData_size, restoreData_surplusScan]
  split
  · rfl
  · split
    · rw [restoreData_blockSwapUnreachable]
      cases blockSwapUnreachable st (surplusScan st st.size NONE NONE).1
      rfl
    · simp only [BitVec.ofNat_eq_ofNat, he, restoreData_swapDestinations] at ha ⊢
      rw [ha]
      generalize (if (surplusScan st st.size NONE NONE).1 = st.size - 1#64 then
        (Status.done, st)
        else if equalBelow st (st.size - 1#64) ≠ NONE then
          (.done, swapDestinations st (equalBelow st (st.size - 1#64)) (st.size - 1#64))
        else swapWith st (surplusScan st st.size NONE NONE).2) = r
      exact restoreData_surplusTail cap old r

theorem restoreData_surplusLoop (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (fuel : Nat) (hs : st.size.toNat ≤ cap) :
    surplusLoop (restoreData cap old st) fuel =
      let r := surplusLoop st fuel; (r.1, restoreData cap old r.2) := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
    rw [surplusLoop, surplusLoop, restoreData_size]
    split
    · rfl
    · rename_i h0
      rw [restoreData_surplusPass cap old st h0 hs]
      have hb := surplusPass_size_le st
      cases he : surplusPass st with
      | error r => rfl
      | ok mid =>
        rw [he] at hb
        exact ih mid (Nat.le_trans hb hs)

theorem restoreData_removeSurplus (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (hs : st.size.toNat ≤ cap) :
    removeSurplus (restoreData cap old st) =
      let r := removeSurplus st; (r.1, restoreData cap old r.2) := by
  unfold removeSurplus
  rw [restoreData_size]
  exact restoreData_surplusLoop cap old st _ hs

theorem surplusLoop_size_le (st : St) (fuel : Nat) :
    (surplusLoop st fuel).2.size.toNat ≤ st.size.toNat := by
  induction fuel generalizing st with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    rw [surplusLoop]
    split
    · exact Nat.le_refl _
    · have hb := surplusPass_size_le st
      cases he : surplusPass st with
      | error r => rw [he] at hb; exact hb
      | ok mid => rw [he] at hb; exact Nat.le_trans (ih mid) hb

theorem removeSurplus_size_le (st : St) :
    (removeSurplus st).2.size.toNat ≤ st.size.toNat :=
  surplusLoop_size_le st st.size.toNat

end Bbu.Flat
