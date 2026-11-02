module

public import FlatShuffler.FlatSurplus
import all FlatShuffler.FlatSurplus
public import FlatShuffler.FlatPopRel
import all FlatShuffler.FlatPopRel

@[expose] public section

/-!
The flat model of `removeSurplus` (`FlatSurplus.lean`) is an instance of the list model
`Map.State.removeSurplus` (`MapModel.lean`), for a stack of at most `MAX_N` slots.

`absOut` reads the list result from a flat result: `.done` has no blocked slot, `.blocked` has
the members `blockedOffset` and `blockedExcess`, and `.assertionFailed` is the assertion.

The proof follows the passes of the loop: `scan_abs` (the scan), `equalBelow_abs` (the loop of
`equalSurplus`), `swapDestinations_abs`, `swapWith_abs` and `pop_abs` (`FlatPopRel.lean`). The
list model computes the excess of a blocked slot in `Nat`, the flat model in `Word`: `scan_inv`
shows that a shallowest slot with no deepest one is out of swap reach, so the two agree.
-/

namespace FlatShuffler.Flat

-- The list result of a flat result of `removeSurplus`.
def absOut (planned : Map.Mapping) : Status × St → M (Option (Nat × Nat) × Map.State)
  | (.done, st) => .ok (none, absSt planned st)
  | (.blocked, st) => .ok (some (st.blockedOffset.toNat, st.blockedExcess.toNat), absSt planned st)
  | (.assertionFailed, _) => .error .assertion

/-! ## Lemmas on the arrays and the words -/

theorem take_put {α : Type} (v : Vector α MAX_N) (i : Word) (x : α) (n : Nat) :
    (put v i x).toList.take n = (v.toList.take n).set i.toNat x := by
  simp only [put, Vector.toList_setIfInBounds, List.take_set]

theorem getD_take {α : Type} (v : Vector α MAX_N) {k p : Nat} (hk : k ≤ MAX_N) (hp : p < k)
    (d : α) : (v.toList.take k).getD p d = v[p]'(by omega) := by
  simp [List.getD_eq_getElem?_getD, hp, show p < MAX_N by omega]

theorem getD_abs (v : Vector Word MAX_N) {k p : Nat} (hk : k ≤ MAX_N) (hp : p < k) :
    ((v.toList.take k).map optOf).getD p none = optOf (v[p]'(by omega)) := by
  simp [List.getD_eq_getElem?_getD, hp, show p < MAX_N by omega]

theorem length_take_data {α : Type} (v : Vector α MAX_N) {k : Nat} (hk : k ≤ MAX_N) :
    (v.toList.take k).length = k := by
  simp [hk]

theorem stack_abs {planned : Map.Mapping} (st : St) (h : st.size.toNat ≤ MAX_N) :
    (absSt planned st).stack.length = st.size.toNat := length_take_data _ h

theorem get_eq {α : Type} [Inhabited α] (v : Vector α MAX_N) {w : Word} {p : Nat}
    (hw : w.toNat = p) (hp : p < MAX_N) : get v w = v[p] := by
  subst hw; exact get_toNat v hp

theorem optOf_eq_some {w : Word} {k : Word} (hk : k.toNat < MAX_N) :
    optOf w = some k.toNat ↔ w = k := by
  by_cases hw : w = NONE
  · subst hw; simp only [optOf_none, reduceCtorEq, false_iff]; exact (ne_none hk).symm
  · rw [optOf_some hw, Option.some.injEq]
    exact ⟨BitVec.eq_of_toNat_eq, fun e => e ▸ rfl⟩

theorem pos_sub_one {pos : Word} {p : Nat} (hp : pos.toNat = p + 1) : (pos - 1).toNat = p := by
  bv_omega

theorem pos_ne_zero {pos : Word} {p : Nat} (hp : pos.toNat = p + 1) : pos ≠ 0 := by
  rintro rfl; simp at hp

/-! ## `swapDestinations` and `swapWith` -/

-- `swapDestinations` changes only `dest` and `pos`.
theorem swapDestinations_eq (st : St) (a b : Word) :
    swapDestinations st a b = { st with dest := (swapDestinations st a b).dest,
                                        pos := (swapDestinations st a b).pos } := rfl

theorem swapDestinations_abs (st : St) {a b : Word} (h : st.size.toNat ≤ MAX_N)
    (ha : a.toNat < st.size.toNat) (hb : b.toNat < st.size.toNat) :
    absMapping (swapDestinations st a b).dest (swapDestinations st a b).pos st.size st.targetSize
      = (absMapping st.dest st.pos st.size st.targetSize).swapDestinations a.toNat b.toNat := by
  have haN : a.toNat < MAX_N := by omega
  have hbN : b.toNat < MAX_N := by omega
  unfold swapDestinations Map.Mapping.swapDestinations absMapping
  simp only [getD_abs _ h ha, getD_abs _ h hb, ← get_toNat _ haN, ← get_toNat _ hbN]
  rw [← abs_put, ← abs_put, getD_abs _ h ha, getD_abs _ h hb, ← get_toNat _ haN,
    ← get_toNat _ hbN]
  generalize put (put st.dest a (get st.dest b)) b (get st.dest a) = d
  have hsa := optOf_some (ne_none haN)
  have hsb := optOf_some (ne_none hbN)
  by_cases hA : get d a = NONE <;> by_cases hB : get d b = NONE
  · simp only [hA, hB, optOf_none, ne_eq, not_true_eq_false, ite_false]
  · simp only [hA, hB, optOf_none, optOf_some hB, ne_eq, not_true_eq_false, not_false_eq_true,
      ite_false, ite_true, abs_put, hsb]
  · simp only [hA, hB, optOf_none, optOf_some hA, ne_eq, not_true_eq_false, not_false_eq_true,
      ite_false, ite_true, abs_put, hsa]
  · simp only [hA, hB, optOf_some hA, optOf_some hB, ne_eq, not_false_eq_true, ite_true, abs_put,
      hsa, hsb]

theorem swapW_of_eq {w : Word} {k : Nat} (h : w.toNat = k) : Op.swapW w = Op.swap k := by
  subst h
  simp only [Op.swapW, Op.swap, Op.mk.injEq, true_and, and_true]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

theorem swapWith_abs (planned : Map.Mapping) (st : St) (pos : Word) (h : st.size.toNat ≤ MAX_N) :
    (absSt planned st).swapWith pos.toNat = absRes planned (swapWith st pos) := by
  unfold Map.State.swapWith swapWith
  rw [stack_abs st h]
  by_cases hp : pos < st.size
  · have hpn : pos.toNat < st.size.toNat := hp
    have hpN : pos.toNat < MAX_N := by omega
    have hg : (absSt planned st).mapping.dest.getD pos.toNat none = optOf (get st.dest pos) := by
      rw [get_toNat _ hpN]; exact getD_abs _ h hpn
    simp only [hg, optOf_eq_some hpN]
    by_cases hf : get st.dest pos = pos
    · simp [isFinal, hf, absRes]
    have hdep : (st.size - 1 - pos).toNat = st.size.toNat - 1 - pos.toNat := by bv_omega
    simp only [isFinal, hf, hp, beq_iff_eq, ite_false, not_true_eq_false, false_or,
      Nat.not_le.2 hpn]
    by_cases hr : 1 ≤ st.size - 1 - pos ∧ st.size - 1 - pos ≤ maxSwapDepth
    · have hr' : 1 ≤ st.size.toNat - 1 - pos.toNat
          ∧ st.size.toNat - 1 - pos.toNat ≤ MAX_SWAP_DEPTH := by
        simp only [BitVec.le_def, maxSwapDepth] at hr; rw [hdep] at hr; exact hr
      simp only [depthOf, hr, hr', and_self, not_true_eq_false, ite_false, absRes,
        Except.ok.injEq]
      have hs1 : (st.size - 1).toNat = st.size.toNat - 1 := by bv_omega
      have htn : (st.size - 1).toNat < st.size.toNat := by omega
      have hm := swapDestinations_abs (stackSwap st pos) h hpn htn
      unfold absSt
      rw [swapDestinations_eq]
      simp only [stackSwap] at hm ⊢
      rw [hm, hs1]
      congr 1
      · have g1 : get st.data (st.size - 1) = st.data[st.size.toNat - 1]'(by omega) := by
          rw [get_toNat _ (by omega)]; simp only [hs1]
        rw [take_put, take_put, hs1, getD_take _ h (by omega), getD_take _ h hpn, g1,
          get_toNat _ hpN]
      · rw [swapW_of_eq hdep]
    · have hr' : ¬(1 ≤ st.size.toNat - 1 - pos.toNat
          ∧ st.size.toNat - 1 - pos.toNat ≤ MAX_SWAP_DEPTH) := by
        simp only [BitVec.le_def, maxSwapDepth] at hr; rw [hdep] at hr; exact hr
      simp only [depthOf, hr, hr', not_false_eq_true, ite_true, absRes]
  · have hpn : st.size.toNat ≤ pos.toNat := by bv_omega
    simp [hp, hpn, absRes]

-- `swapWith` and `pop` do not block.
theorem swapWith_status (st : St) (pos : Word) : (swapWith st pos).1 ≠ .blocked := by
  unfold swapWith; dsimp only; repeat' split
  all_goals simp

theorem pop_status (st : St) : (pop st).1 ≠ .blocked := by
  unfold pop stackPop; dsimp only; repeat' split
  all_goals simp_all

theorem swapWith_size (st : St) (pos : Word) : (swapWith st pos).2.size = st.size := by
  unfold swapWith; dsimp only; repeat' split
  all_goals rfl

/-! ## The scans -/

theorem reach_iff (st : St) {q : Word} (hq : q.toNat < st.size.toNat) :
    isSwapReachable st q = true ↔ st.size.toNat - 1 - q.toNat ≤ MAX_SWAP_DEPTH := by
  have : (st.size - 1 - q).toNat = st.size.toNat - 1 - q.toNat := by bv_omega
  simp only [isSwapReachable, depthOf, maxSwapDepth, decide_eq_true_eq, BitVec.le_def, this]
  rfl

-- The scan below `pos`.
theorem scan_abs (planned : Map.Mapping) (st : St) (h : st.size.toNat ≤ MAX_N) (p : Nat) :
    ∀ (pos : Word), pos.toNat = p → p ≤ st.size.toNat → ∀ sh dp : Word,
      (absSt planned st).surplusScan p (optOf sh) (optOf dp)
        = (optOf (surplusScan st pos sh dp).1, optOf (surplusScan st pos sh dp).2) := by
  induction p with
  | zero =>
    intro pos hp _ sh dp
    have : pos = 0 := BitVec.eq_of_toNat_eq (by simpa using hp)
    subst this
    rw [surplusScan]; rfl
  | succ p ih =>
    intro pos hp hle sh dp
    have hq := pos_sub_one hp
    have hpN : p < MAX_N := by omega
    have hq' : (pos - 1).toNat < st.size.toNat := by omega
    have hg : (absSt planned st).mapping.dest.getD p none = optOf (get st.dest (pos - 1)) := by
      rw [get_eq _ hq hpN]; exact getD_abs _ h (by omega)
    rw [surplusScan, dite_eq_right (pos_ne_zero hp)]
    simp only [Map.State.surplusScan, hg, optOf_eq_none, isSurplus, beq_iff_eq, stack_abs st h]
    by_cases hs : get st.dest (pos - 1) = NONE
    · simp only [hs, ite_true]
      rw [← ih (pos - 1) hq (by omega)]
      have ho : optOf (pos - 1) = some p := by rw [optOf_some (ne_none (by omega)), hq]
      congr 1
      · by_cases h0 : sh = NONE
        · simp only [h0, ite_true, ho]
        · simp only [h0, ite_false]
      · by_cases hr : isSwapReachable st (pos - 1) = true
        · have hr' := (reach_iff st hq').1 hr
          rw [hq] at hr'
          simp only [hr, hr', ite_true, ho]
        · have hr' : ¬(st.size.toNat - 1 - p ≤ MAX_SWAP_DEPTH) := by
            rw [← hq]; exact fun e => hr ((reach_iff st hq').2 e)
          simp only [hr, hr', Bool.false_eq_true, ite_false]
    · simp only [hs, ite_false]
      exact ih (pos - 1) hq (by omega) sh dp

-- A shallowest slot with no deepest one is out of swap reach.
theorem scan_inv (s : Map.State) (p : Nat) (hp : p ≤ s.stack.length) :
    ∀ sh dp : Option Nat,
      (∀ a, sh = some a → dp = none →
        a < s.stack.length ∧ MAX_SWAP_DEPTH < s.stack.length - 1 - a) →
      ∀ a, (s.surplusScan p sh dp).1 = some a → (s.surplusScan p sh dp).2 = none →
        a < s.stack.length ∧ MAX_SWAP_DEPTH < s.stack.length - 1 - a := by
  induction p with
  | zero => intro sh dp hi; exact hi
  | succ p ih =>
    intro sh dp hi
    simp only [Map.State.surplusScan]
    split
    · apply ih (by omega)
      intro a ha hd
      by_cases hr : s.stack.length - 1 - p ≤ MAX_SWAP_DEPTH
      · simp [hr] at hd
      · simp only [hr, ite_false] at hd
        by_cases h0 : sh = none
        · simp only [h0, ite_true, Option.some.injEq] at ha
          subst ha; omega
        · simp only [h0, ite_false] at ha
          exact hi a ha hd
    · exact ih (by omega) sh dp hi

-- The loop of `equalSurplus` below `pos`. The result is below `pos`.
theorem equalBelow_abs (planned : Map.Mapping) (st : St) (h : st.size.toNat ≤ MAX_N)
    (_hk : st.size.toNat ≠ 0) (p : Nat) :
    ∀ pos : Word, pos.toNat = p → p ≤ st.size.toNat →
      (absSt planned st).equalBelow (st.size.toNat - 1) p = optOf (equalBelow st pos)
        ∧ (equalBelow st pos = NONE ∨ (equalBelow st pos).toNat < p) := by
  induction p with
  | zero =>
    intro pos hp _
    have : pos = 0 := BitVec.eq_of_toNat_eq (by simpa using hp)
    subst this
    rw [equalBelow]
    exact ⟨optOf_none.symm, .inl rfl⟩
  | succ p ih =>
    intro pos hp hle
    have hq := pos_sub_one hp
    have hpN : p < MAX_N := by omega
    have hs1 : (st.size - 1).toNat = st.size.toNat - 1 := by bv_omega
    have hg : (absSt planned st).mapping.dest.getD p none = optOf (get st.dest (pos - 1)) := by
      rw [get_eq _ hq hpN]; exact getD_abs _ h (by omega)
    have hd : (absSt planned st).stack.getD p default = get st.data (pos - 1) := by
      rw [get_eq _ hq hpN]; exact getD_take _ h (by omega) _
    have ht : (absSt planned st).stack.getD (st.size.toNat - 1) default
        = get st.data (st.size - 1) := by
      rw [get_eq _ hs1 (by omega)]; exact getD_take _ h (by omega) _
    rw [equalBelow, dite_eq_right (pos_ne_zero hp)]
    simp only [Map.State.equalBelow, hg, hd, ht, optOf_eq_none, isSurplus, beq_iff_eq]
    by_cases hc : get st.dest (pos - 1) = NONE ∧ get st.data (pos - 1) = get st.data (st.size - 1)
    · simp only [hc, and_self, ite_true]
      exact ⟨by rw [optOf_some (ne_none (by omega)), hq], .inr (by omega)⟩
    · simp only [hc, ite_false]
      obtain ⟨h1, h2⟩ := ih (pos - 1) hq (by omega)
      exact ⟨h1, h2.imp_right (fun e => by omega)⟩

/-! ## The loop -/

-- The pop at the end of a pass, then the next passes.
theorem tail_abs (planned : Map.Mapping) (fuel : Nat)
    (ih : ∀ st : St, st.size.toNat ≤ MAX_N →
      (absSt planned st).surplusLoop fuel = absOut planned (surplusLoop st fuel))
    (r : Status × St) (hb : r.1 ≠ .blocked) (h : r.2.size.toNat ≤ MAX_N) :
    ((absRes planned r).bind Map.State.pop).bind (·.surplusLoop fuel)
      = absOut planned (match (if r.1 ≠ .done then .error r
          else if (pop r.2).1 ≠ .done then .error (pop r.2) else .ok (pop r.2).2
            : Except (Status × St) St) with
        | .error r => r
        | .ok st => surplusLoop st fuel) := by
  obtain ⟨s, st⟩ := r
  cases s with
  | blocked => exact absurd rfl hb
  | assertionFailed => rfl
  | done =>
    simp only [absRes, Except.bind, ne_eq, not_true_eq_false, ite_false]
    rw [pop_abs planned st h]
    have hp := pop_size st h
    have hs := pop_status st
    revert hp hs
    obtain ⟨s', st'⟩ := pop st
    intro hp hs
    cases s' with
    | blocked => exact absurd rfl hs
    | assertionFailed => rfl
    | done => exact ih st' hp

theorem surplusLoop_abs (planned : Map.Mapping) (fuel : Nat) :
    ∀ st : St, st.size.toNat ≤ MAX_N →
      (absSt planned st).surplusLoop fuel = absOut planned (surplusLoop st fuel) := by
  induction fuel with
  | zero => intro st _; rfl
  | succ fuel ih =>
    intro st h
    by_cases h0 : st.size = 0
    · have hs : (absSt planned st).stack = [] := by simp [absSt, h0]
      simp only [Map.State.surplusLoop, surplusLoop, hs, h0, ite_true]; rfl
    have hk : st.size.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e))
    have hne : (absSt planned st).stack ≠ [] := take_ne_nil st.data hk
    have hsc := scan_abs planned st h st.size.toNat st.size rfl (Nat.le_refl _) NONE NONE
    have hinv := scan_inv (absSt planned st) (absSt planned st).stack.length (Nat.le_refl _)
      none none (by simp)
    rw [optOf_none] at hsc
    rw [stack_abs st h, hsc] at hinv
    simp only [Map.State.surplusLoop, surplusLoop, hne, h0, ite_false, stack_abs st h, hsc]
    unfold surplusPass
    generalize surplusScan st st.size NONE NONE = sc at hinv ⊢
    obtain ⟨sh, dp⟩ := sc
    dsimp only at hinv ⊢
    -- No surplus slot.
    by_cases hsh : sh = NONE
    · simp only [hsh, optOf_none, ite_true]; rfl
    -- No surplus slot in swap reach: the shallowest one blocks.
    by_cases hdp : dp = NONE
    · have ⟨hlt, hx⟩ := hinv _ (optOf_some hsh) (by rw [hdp, optOf_none])
      have hex : (depthOf st sh - maxSwapDepth).toNat
          = st.size.toNat - 1 - sh.toNat - MAX_SWAP_DEPTH := by
        simp only [depthOf, maxSwapDepth]; unfold MAX_SWAP_DEPTH at hx ⊢; bv_omega
      have hne0 : depthOf st sh - maxSwapDepth ≠ 0 := by
        intro e; rw [e] at hex; unfold MAX_SWAP_DEPTH at hx hex; simp at hex; omega
      simp only [hsh, hdp, optOf_some hsh, optOf_none, ite_true, ite_false, blockSwapUnreachable,
        block, hne0, absOut, hex, Nat.sub_eq_zero_iff_le, Nat.not_le.2 hx]
      rfl
    have hs1 : (st.size - 1).toNat = st.size.toNat - 1 := by bv_omega
    simp only [hsh, hdp, optOf_some hsh, optOf_some hdp, ite_false]
    -- The top is surplus.
    by_cases htop : sh = st.size - 1
    · simp only [htop, hs1, ite_true]
      exact tail_abs planned fuel ih (.done, st) (by simp) h
    have htop' : ¬sh.toNat = st.size.toNat - 1 :=
      fun e => htop (BitVec.eq_of_toNat_eq (by rw [e, hs1]))
    obtain ⟨hE, hlt⟩ :=
      equalBelow_abs planned st h hk (st.size.toNat - 1) (st.size - 1) hs1 (by omega)
    simp only [htop, htop', ite_false, hE]
    -- No surplus slot equal to the top: a swap with the deepest one.
    by_cases he : equalBelow st (st.size - 1) = NONE
    · simp only [he, optOf_none, ne_eq, not_true_eq_false, ite_false]
      rw [swapWith_abs planned st dp h]
      exact tail_abs planned fuel ih _ (swapWith_status st dp) (by rw [swapWith_size]; exact h)
    -- A surplus slot equal to the top takes its destination.
    have hlt' : (equalBelow st (st.size - 1)).toNat < st.size.toNat := by
      rcases hlt with e | e
      · exact absurd e he
      · omega
    have hm := swapDestinations_abs st h hlt' (show (st.size - 1).toNat < st.size.toNat by omega)
    rw [hs1] at hm
    simp only [he, optOf_some he, ne_eq, not_false_eq_true, ite_true]
    have hst : ({ absSt planned st with mapping := ((absSt planned st).mapping.swapDestinations
        (equalBelow st (st.size - 1)).toNat (st.size.toNat - 1)) } : Map.State)
        = absSt planned (swapDestinations st (equalBelow st (st.size - 1)) (st.size - 1)) := by
      unfold absSt; rw [swapDestinations_eq]; dsimp only; rw [hm]
    rw [hst]
    exact tail_abs planned fuel ih (.done, _) (by simp) h

/-! ## `removeSurplus` -/

theorem removeSurplus_abs (planned : Map.Mapping) (st : St) (h : st.size.toNat ≤ MAX_N) :
    (absSt planned st).removeSurplus = absOut planned (removeSurplus st) := by
  unfold Map.State.removeSurplus removeSurplus
  rw [stack_abs st h]
  exact surplusLoop_abs planned _ st h

end FlatShuffler.Flat
