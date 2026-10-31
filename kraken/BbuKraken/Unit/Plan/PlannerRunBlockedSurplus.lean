import BbuKraken.Unit.Plan.PlannerRunBlockedBasic

namespace Bbu.Unit.PlannerRunU
open Flat

theorem surplus_scan_deepest_none (st : Flat.St) (p sh dp : Word)
    (hn : (Flat.surplusScan st p sh dp).2 = NONE) :
    dp = NONE ∧ ∀ i, i < p → get st.dest i = NONE → Flat.isSwapReachable st i = false := by
  rw [Flat.surplusScan] at hn
  simp only [BitVec.ofNat_eq_ofNat] at hn
  split at hn
  · rename_i h0
    exact ⟨hn, fun i hi _ => False.elim (by rw [h0] at hi; bv_omega)⟩
  · rename_i h0
    split at hn
    · by_cases hr : Flat.isSwapReachable st (p - 1#64) = true
      · rw [ite_eq_left hr] at hn
        have he := (surplus_scan_deepest_none st (p - 1#64) _ _ hn).1
        have hne : p - 1#64 ≠ NONE := by
          intro e
          have heN := congrArg BitVec.toNat e
          rw [Flat.toNat_NONE] at heN
          bv_omega
        exact False.elim (hne he)
      · rw [ite_eq_right hr] at hn
        obtain ⟨hd, hall⟩ := surplus_scan_deepest_none st (p - 1#64) _ dp hn
        refine ⟨hd, fun i hi hs => ?_⟩
        by_cases he : i = p - 1#64
        · subst i
          exact Bool.eq_false_iff.mpr hr
        · exact hall i (by bv_omega) hs
    · rename_i hs
      obtain ⟨hd, hall⟩ := surplus_scan_deepest_none st (p - 1#64) sh dp hn
      refine ⟨hd, fun i hi hsur => ?_⟩
      by_cases he : i = p - 1#64
      · subst i
        exact False.elim (hs (by simp only [Flat.isSurplus, hsur, BEq.rfl]))
      · exact hall i (by bv_omega) hsur
termination_by p.toNat
decreasing_by all_goals bv_omega

theorem surplus_action_not_blocked (st : Flat.St) (sh dp : Word) :
    (if sh = st.size - 1 then (.done, st)
      else if Flat.equalBelow st (st.size - 1) ≠ NONE then
        (.done, Flat.swapDestinations st (Flat.equalBelow st (st.size - 1)) (st.size - 1))
      else Flat.swapWith st dp).1 ≠ .blocked := by
  split
  · simp
  · split
    · simp
    · exact Flat.swapWith_status _ _

theorem surplus_tail_not_blocked {r : Flat.Status × Flat.St} {out : Flat.St}
    (hn : r.1 ≠ .blocked)
    (he : (if r.1 ≠ .done then Except.error r else
      if (Flat.pop r.2).1 ≠ .done then .error (Flat.pop r.2) else .ok (Flat.pop r.2).2) =
      .error (.blocked, out)) : False := by
  split at he
  · exact hn (congrArg Prod.fst (Except.error.inj he))
  · split at he
    · exact Flat.pop_status _ (congrArg Prod.fst (Except.error.inj he))
    · cases he

theorem Prep.surplusPass_blocked {planned : Vector Word MAX_N} {m : Nat}
    {st out : Flat.St} (h : Prep planned m st)
    (he : Flat.surplusPass st = .error (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  have hp := surplus_scan_pick st st.size NONE NONE (BitVec.le_refl _)
    (Or.inl rfl) (Or.inl rfl)
  unfold Flat.surplusPass at he
  generalize hsc : Flat.surplusScan st st.size NONE NONE = sc at hp he
  obtain ⟨sh, dp⟩ := sc
  dsimp only at hp he
  split at he
  · cases he
  · rename_i hsh
    split at he
    · rename_i hdp
      have hv := hp.1.resolve_left hsh
      have hu := surplus_scan_deepest_none st st.size NONE NONE (by rw [hsc]; exact hdp)
      exact blockSwap_bounds h.map.m_bound h.map.destOk hv.1
        (hu.2 sh hv.1 hv.2) (Except.error.inj he)
    · exact False.elim (surplus_tail_not_blocked (surplus_action_not_blocked st sh dp) he)

theorem pop_target (st : Flat.St) : (Flat.pop st).2.targetSize = st.targetSize := by
  unfold Flat.pop Flat.stackPop Flat.mappingPop
  dsimp only
  repeat' split
  all_goals rfl

theorem surplusPass_ok_target {st mid : Flat.St}
    (he : Flat.surplusPass st = .ok mid) : mid.targetSize = st.targetSize := by
  unfold Flat.surplusPass at he
  generalize hsc : Flat.surplusScan st st.size NONE NONE = sc at he
  obtain ⟨sh, dp⟩ := sc
  dsimp only at he
  split at he
  · cases he
  · split at he
    · cases he
    · generalize ha : (if sh = st.size - 1 then (.done, st)
        else if Flat.equalBelow st (st.size - 1) ≠ NONE then
          (.done, Flat.swapDestinations st (Flat.equalBelow st (st.size - 1)) (st.size - 1))
        else Flat.swapWith st dp) = r at he
      split at he
      · cases he
      · split at he
        · cases he
        · cases he
          have hp := pop_target r.2
          rw [hp]
          split at ha
          · cases ha; rfl
          · split at ha
            · cases ha; rfl
            · cases ha
              exact (Flat.swapWith_keep _ _).1

theorem Prep.surplusLoop_blocked {planned : Vector Word MAX_N} {m : Nat}
    (fuel : Nat) {st out : Flat.St} (h : Prep planned m st)
    (he : Flat.surplusLoop st fuel = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  cases fuel with
  | zero => cases he
  | succ fuel =>
    rw [Flat.surplusLoop] at he
    split at he
    · cases he
    · rename_i h0
      have hp := h.surplus_pass h0
      cases hr : Flat.surplusPass st with
      | error r =>
        rw [hr] at he
        exact h.surplusPass_blocked (by rw [hr]; exact congrArg Except.error he)
      | ok mid =>
        rw [hr] at hp he
        dsimp only at hp he
        have ht := surplusPass_ok_target hr
        simpa only [ht] using hp.1.surplusLoop_blocked fuel he
termination_by fuel

theorem Prep.removeSurplus_blocked {planned : Vector Word MAX_N} {m : Nat}
    {st out : Flat.St} (h : Prep planned m st)
    (he : Flat.removeSurplus st = (.blocked, out)) :
    BlockedBounds st.targetSize out :=
  h.surplusLoop_blocked st.size.toNat he

theorem surplus_action_target (st : Flat.St) (sh dp : Word) :
    (if sh = st.size - 1 then (.done, st)
      else if Flat.equalBelow st (st.size - 1) ≠ NONE then
        (.done, Flat.swapDestinations st (Flat.equalBelow st (st.size - 1)) (st.size - 1))
      else Flat.swapWith st dp).2.targetSize = st.targetSize := by
  split
  · rfl
  · split
    · rfl
    · exact (Flat.swapWith_keep _ _).1

theorem surplusPass_target (st : Flat.St) :
    match Flat.surplusPass st with
    | .error r => r.2.targetSize = st.targetSize
    | .ok mid => mid.targetSize = st.targetSize := by
  unfold Flat.surplusPass
  generalize hsc : Flat.surplusScan st st.size NONE NONE = sc
  obtain ⟨sh, dp⟩ := sc
  dsimp only
  by_cases hsh : sh = NONE
  · simp only [hsh, ↓reduceIte]
  · simp only [hsh, ↓reduceIte]
    by_cases hdp : dp = NONE
    · simp only [hdp, ↓reduceIte]
      exact (Flat.block_keep _ _ _).1
    · simp only [hdp, ↓reduceIte]
      have ht := surplus_action_target st sh dp
      generalize ha : (if sh = st.size - 1 then (.done, st)
        else if Flat.equalBelow st (st.size - 1) ≠ NONE then
          (.done, Flat.swapDestinations st (Flat.equalBelow st (st.size - 1)) (st.size - 1))
        else Flat.swapWith st dp) = r at ht ⊢
      by_cases hd : r.1 ≠ .done
      · rw [ite_eq_left hd]
        exact ht
      · rw [ite_eq_right hd]
        by_cases hp : (Flat.pop r.2).1 ≠ .done
        · rw [ite_eq_left hp]
          exact (pop_target r.2).trans ht
        · rw [ite_eq_right hp]
          exact (pop_target r.2).trans ht

theorem surplusLoop_target (st : Flat.St) (fuel : Nat) :
    (Flat.surplusLoop st fuel).2.targetSize = st.targetSize := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Flat.surplusLoop]
    split
    · rfl
    · have ht := surplusPass_target st
      cases hr : Flat.surplusPass st with
      | error r =>
        rw [hr] at ht
        exact ht
      | ok mid =>
        rw [hr] at ht
        exact (surplusLoop_target mid fuel).trans ht
termination_by fuel

theorem removeSurplus_target (st : Flat.St) :
    (Flat.removeSurplus st).2.targetSize = st.targetSize :=
  surplusLoop_target st st.size.toNat

end Bbu.Unit.PlannerRunU
