module

public import FlatShuffler.FlatList.PermLoop
import all FlatShuffler.FlatList.PermLoop
public import FlatShuffler.FlatList.PermList
import all FlatShuffler.FlatList.PermList

@[expose] public section

/-!
The loops of the flat `permute` before `permuteLoop`: `readDestinations`, `clearDesired` and
the `leader` loop `regroup` with `markDesired`, `nextVacant` and `placeGroup`. The `leader`
loop gives the result of `FlatShuffler.normalize` (`PermList.lean`).
-/

namespace FlatShuffler.Flat

theorem toNat_succ {a : Word} (h : a.toNat < MAX_N) : (a + 1).toNat = a.toNat + 1 := by
  rw [MAX_N_eq] at h; bv_omega

/-! ## `readDestinations` and `clearDesired` -/

theorem readDestinations_spec (fs : St) (hn : fs.size.toNat ≤ MAX_N)
    (hd : ∀ i : Word, i.toNat < fs.size.toNat → get fs.dest i ≠ NONE) :
    ∀ m (pos : Word) (perm : Vector Word MAX_N), fs.size.toNat - pos.toNat = m →
      pos.toNat ≤ fs.size.toNat →
      ∃ v, readDestinations fs pos perm = some v ∧ ∀ i : Word,
        get v i = if pos.toNat ≤ i.toNat ∧ i.toNat < fs.size.toNat then get fs.dest i
          else get perm i := by
  intro m
  induction m with
  | zero =>
    intro pos perm hm hpos
    have hc : ¬pos < fs.size := by bv_omega
    rw [readDestinations, dite_eq_right hc]
    exact ⟨perm, rfl, fun i => (ite_eq_right (fun h => by have := h.1; have := h.2; omega)).symm⟩
  | succ m ih =>
    intro pos perm hm hpos
    have hc : pos < fs.size := by bv_omega
    have hpn : pos.toNat < fs.size.toNat := by omega
    have hp1 : (pos + 1).toNat = pos.toNat + 1 := toNat_succ (by omega)
    have e : readDestinations fs pos perm =
        readDestinations fs (pos + 1) (put perm pos (get fs.dest pos)) := by
      rw [readDestinations, dite_eq_left hc]
      exact ite_eq_right (hd pos hpn)
    obtain ⟨v, h1, h2⟩ := ih (pos + 1) (put perm pos (get fs.dest pos)) (by omega) (by omega)
    refine ⟨v, by rw [e, h1], fun i => ?_⟩
    rw [h2 i, hp1, get_put _ _ _ (by omega)]
    by_cases hi : i = pos
    · rw [hi, ite_eq_right (fun h => by omega), ite_eq_left rfl,
        ite_eq_left ⟨Nat.le_refl _, hpn⟩]
    · have hi' := toNat_ne_of_ne hi
      rw [ite_eq_right hi]
      by_cases hc1 : pos.toNat + 1 ≤ i.toNat ∧ i.toNat < fs.size.toNat
      · rw [ite_eq_left hc1, ite_eq_left ⟨by omega, hc1.2⟩]
      · rw [ite_eq_right hc1, ite_eq_right (fun h => hc1 ⟨by omega, h.2⟩)]

theorem clearDesired_spec (fs : St) (hn : fs.size.toNat ≤ MAX_N) :
    ∀ m (off : Word) (dB : Vector Word MAX_N), fs.size.toNat - off.toNat = m →
      off.toNat ≤ fs.size.toNat → ∀ w : Word,
        get (clearDesired fs off dB) w =
          if off.toNat ≤ w.toNat ∧ w.toNat < fs.size.toNat then NONE else get dB w := by
  intro m
  induction m with
  | zero =>
    intro off dB hm hoff w
    have hc : ¬off < fs.size := by bv_omega
    rw [clearDesired, dite_eq_right hc]
    exact (ite_eq_right (fun h => by have := h.1; have := h.2; omega)).symm
  | succ m ih =>
    intro off dB hm hoff w
    have hc : off < fs.size := by bv_omega
    have hon : off.toNat < fs.size.toNat := by omega
    have ho1 : (off + 1).toNat = off.toNat + 1 := toNat_succ (by omega)
    rw [clearDesired, dite_eq_left hc, ih (off + 1) _ (by omega) (by omega) w, ho1,
      get_put _ _ _ (by omega)]
    by_cases hw : w = off
    · rw [hw, ite_eq_right (fun h => by omega), ite_eq_left rfl,
        ite_eq_left ⟨Nat.le_refl _, hon⟩]
    · have hw' := toNat_ne_of_ne hw
      rw [ite_eq_right hw]
      by_cases hc1 : off.toNat + 1 ≤ w.toNat ∧ w.toNat < fs.size.toNat
      · rw [ite_eq_left hc1, ite_eq_left ⟨by omega, hc1.2⟩]
      · rw [ite_eq_right hc1, ite_eq_right (fun h => hc1 ⟨by omega, h.2⟩)]

/-! ## `markDesired` -/

theorem markDesired_spec (fs : St) {leader : Word} (hl : leader < fs.size) (slot : StackSlot)
    (perm : Vector Word MAX_N) (hn : fs.size.toNat ≤ MAX_N)
    (hp : ∀ y : Word, y.toNat ≤ leader.toNat → (get perm y).toNat < MAX_N) :
    ∀ m (pos : Word) (dB : Vector Word MAX_N), leader.toNat + 1 - pos.toNat = m →
      pos.toNat ≤ leader.toNat + 1 → ∀ w : Word,
        (get (markDesired fs leader hl slot perm pos dB) w = leader ↔
          get dB w = leader ∨ ∃ y : Word, pos.toNat ≤ y.toNat ∧ y.toNat ≤ leader.toNat ∧
            get fs.data y = slot ∧ get perm y = w) ∧
        (get (markDesired fs leader hl slot perm pos dB) w = leader ∨
          get (markDesired fs leader hl slot perm pos dB) w = get dB w) := by
  have hL : leader.toNat < fs.size.toNat := hl
  intro m
  induction m with
  | zero =>
    intro pos dB hm hpos w
    have hc : ¬pos ≤ leader := by bv_omega
    rw [markDesired, dite_eq_right hc]
    exact ⟨⟨Or.inl, fun h => h.elim id fun ⟨y, h1, h2, _⟩ => absurd h2 (by omega)⟩, Or.inr rfl⟩
  | succ m ih =>
    intro pos dB hm hpos w
    have hc : pos ≤ leader := by bv_omega
    have hp1 : (pos + 1).toNat = pos.toNat + 1 := toNat_succ (by omega)
    have e : markDesired fs leader hl slot perm pos dB = markDesired fs leader hl slot perm (pos + 1)
        (if get fs.data pos = slot then put dB (get perm pos) leader else dB) := by
      rw [markDesired, dite_eq_left hc]
    have hq : (get (if get fs.data pos = slot then put dB (get perm pos) leader else dB) w = leader ↔
          get dB w = leader ∨ (get fs.data pos = slot ∧ get perm pos = w)) ∧
        (get (if get fs.data pos = slot then put dB (get perm pos) leader else dB) w = leader ∨
          get (if get fs.data pos = slot then put dB (get perm pos) leader else dB) w =
            get dB w) := by
      by_cases hd : get fs.data pos = slot
      · rw [ite_eq_left hd, get_put _ _ _ (hp pos (by omega))]
        by_cases hw : w = get perm pos
        · rw [ite_eq_left hw]; exact ⟨⟨fun _ => Or.inr ⟨hd, hw.symm⟩, fun _ => rfl⟩, Or.inl rfl⟩
        · rw [ite_eq_right hw]
          exact ⟨⟨Or.inl, fun h => h.elim id fun h' => absurd h'.2.symm hw⟩, Or.inr rfl⟩
      · rw [ite_eq_right hd]
        exact ⟨⟨Or.inl, fun h => h.elim id fun h' => absurd h'.1 hd⟩, Or.inr rfl⟩
    obtain ⟨h1, h2⟩ := ih (pos + 1)
      (if get fs.data pos = slot then put dB (get perm pos) leader else dB) (by omega) (by omega) w
    rw [e]
    refine ⟨?_, ?_⟩
    · rw [h1, hq.1]
      constructor
      · rintro ((h | ⟨hd, hw⟩) | ⟨y, hy1, hy2, hy3, hy4⟩)
        · exact Or.inl h
        · exact Or.inr ⟨pos, Nat.le_refl _, by omega, hd, hw⟩
        · exact Or.inr ⟨y, by omega, hy2, hy3, hy4⟩
      · rintro (h | ⟨y, hy1, hy2, hy3, hy4⟩)
        · exact Or.inl (Or.inl h)
        · by_cases hy : y = pos
          · rw [hy] at hy3 hy4; exact Or.inl (Or.inr ⟨hy3, hy4⟩)
          · exact Or.inr ⟨y, by have := toNat_ne_of_ne hy; omega, hy2, hy3, hy4⟩
    · rcases h2 with h | h
      · exact Or.inl h
      · rw [h]; exact hq.2

/-! ## `nextVacant` and `placeGroup` -/

theorem nextVacant_spec (fs : St) (leader : Word) (slot : StackSlot) (dB : Vector Word MAX_N)
    {P : Nat → Bool} (hn : fs.size.toNat ≤ MAX_N)
    (hP : ∀ w : Word, w.toNat < fs.size.toNat →
      (P w.toNat = true ↔ get dB w = leader ∧ ¬get fs.data w = slot)) :
    ∀ m (v : Word), fs.size.toNat - v.toNat = m → v.toNat ≤ fs.size.toNat →
      v.toNat ≤ (nextVacant fs leader slot dB v).toNat ∧
      (nextVacant fs leader slot dB v).toNat ≤ fs.size.toNat ∧
      ((nextVacant fs leader slot dB v).toNat < fs.size.toNat →
        P (nextVacant fs leader slot dB v).toNat = true) ∧
      (List.range (nextVacant fs leader slot dB v).toNat).countP P =
        (List.range v.toNat).countP P := by
  intro m
  induction m with
  | zero =>
    intro v hm hv
    have hc : ¬(v < fs.size ∧ ¬(get dB v = leader ∧ ¬get fs.data v = slot)) := fun h => by
      have := h.1; bv_omega
    rw [nextVacant, dite_eq_right hc]
    exact ⟨Nat.le_refl _, hv, fun h => by omega, rfl⟩
  | succ m ih =>
    intro v hm hv
    have hvs : v < fs.size := by bv_omega
    by_cases hc : get dB v = leader ∧ ¬get fs.data v = slot
    · have hc' : ¬(v < fs.size ∧ ¬(get dB v = leader ∧ ¬get fs.data v = slot)) :=
        fun h => h.2 hc
      rw [nextVacant, dite_eq_right hc']
      exact ⟨Nat.le_refl _, hv, fun _ => (hP v (by omega)).2 hc, rfl⟩
    · have hv1 : (v + 1).toNat = v.toNat + 1 := toNat_succ (by omega)
      have e : nextVacant fs leader slot dB v = nextVacant fs leader slot dB (v + 1) := by
        rw [nextVacant, dite_eq_left ⟨hvs, hc⟩]
      rw [e]
      obtain ⟨a1, a2, a3, a4⟩ := ih (v + 1) (by omega) (by omega)
      refine ⟨by omega, a2, a3, ?_⟩
      rw [a4, hv1, countP_range_succ, ite_eq_right (fun h => hc ((hP v (by omega)).1 h)),
        Nat.add_zero]

-- `placeGroup` from `pos`: a slot of the group at `x` goes to `x` if the group desires `x`,
-- else to the next vacant offset in order. `vacant` is past as many vacant offsets as
-- there are movers below `pos`.
theorem placeGroup_spec (fs : St) {leader : Word} (hl : leader < fs.size) (slot : StackSlot)
    (dB : Vector Word MAX_N) {g d : Nat → Bool} (hn : fs.size.toNat ≤ MAX_N)
    (hg : ∀ w : Word, w.toNat < fs.size.toNat → (get fs.data w = slot ↔ g w.toNat = true))
    (hd : ∀ w : Word, w.toNat < fs.size.toNat → (get dB w = leader ↔ d w.toNat = true))
    (hc : (List.range fs.size.toNat).countP (fun y => g y && !d y) ≤
      (List.range fs.size.toNat).countP (fun w => d w && !g w)) :
    ∀ m (pos vacant : Word) (perm : Vector Word MAX_N), leader.toNat + 1 - pos.toNat = m →
      pos.toNat ≤ leader.toNat + 1 → vacant.toNat ≤ fs.size.toNat →
      (List.range vacant.toNat).countP (fun w => d w && !g w) =
        (List.range pos.toNat).countP (fun y => g y && !d y) →
      ∃ out, placeGroup fs leader hl slot dB pos vacant perm = some out ∧
        ∀ x : Word, (get out x).toNat =
          if pos.toNat ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true then
            (if d x.toNat = true then x.toNat else
              ((List.range fs.size.toNat).filter fun w => d w && !g w)[
                (List.range x.toNat).countP fun y => g y && !d y]!)
          else (get perm x).toNat := by
  have hL : leader.toNat < fs.size.toNat := hl
  intro m
  induction m with
  | zero =>
    intro pos vacant perm hm hpos hv hcnt
    have hc : ¬pos ≤ leader := by bv_omega
    rw [placeGroup, dite_eq_right hc]
    exact ⟨perm, rfl, fun x => (ite_eq_right (fun h => by have := h.1; have := h.2.1; omega)).symm⟩
  | succ m ih =>
    intro pos vacant perm hm hpos hv hcnt
    have hc' : pos ≤ leader := by bv_omega
    have hpL : pos.toNat ≤ leader.toNat := by omega
    have hpn : pos.toNat < fs.size.toNat := by omega
    have hp1 : (pos + 1).toNat = pos.toNat + 1 := toNat_succ (by omega)
    have hcs := countP_range_succ (fun y => g y && !d y) pos.toNat
    -- the frame: the positions above `pos`
    have frame : ∀ (perm' : Vector Word MAX_N) (out : Vector Word MAX_N) (a : Nat),
        (∀ x : Word, (get out x).toNat =
          if (pos + 1).toNat ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true then
            (if d x.toNat = true then x.toNat else
              ((List.range fs.size.toNat).filter fun w => d w && !g w)[
                (List.range x.toNat).countP fun y => g y && !d y]!)
          else (get perm' x).toNat) →
        perm' = put perm pos (BitVec.ofNat 64 a) → a < MAX_N →
        (g pos.toNat = true → a = if d pos.toNat = true then pos.toNat else
              ((List.range fs.size.toNat).filter fun w => d w && !g w)[
                (List.range pos.toNat).countP fun y => g y && !d y]!) →
        (g pos.toNat = false → a = (get perm pos).toNat) →
        ∀ x : Word, (get out x).toNat =
          if pos.toNat ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true then
            (if d x.toNat = true then x.toNat else
              ((List.range fs.size.toNat).filter fun w => d w && !g w)[
                (List.range x.toNat).countP fun y => g y && !d y]!)
          else (get perm x).toNat := by
      intro perm' out a h2 hpe ha hga hgb x
      rw [h2 x, hp1, hpe, get_put _ _ _ (by omega)]
      by_cases hx : x = pos
      · rw [hx, ite_eq_right (fun h => by omega), ite_eq_left rfl, toNat_ofNat_small ha]
        cases hgp : g pos.toNat
        · rw [ite_eq_right (fun h => absurd h.2.2 (by decide))]
          exact hgb hgp
        · rw [ite_eq_left ⟨Nat.le_refl _, hpL, rfl⟩]
          exact hga hgp
      · have hx' := toNat_ne_of_ne hx
        rw [ite_eq_right hx]
        by_cases hc1 : pos.toNat + 1 ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true
        · rw [ite_eq_left hc1, ite_eq_left (c := pos.toNat ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true)
          ⟨by omega, hc1.2⟩]
        · rw [ite_eq_right hc1, ite_eq_right (fun h => hc1 ⟨by omega, h.2⟩)]
    by_cases hgp : get fs.data pos = slot
    · have hgp' := (hg pos hpn).1 hgp
      by_cases hdp : get dB pos = leader
      · have hdp' := (hd pos hpn).1 hdp
        have e : placeGroup fs leader hl slot dB pos vacant perm =
            placeGroup fs leader hl slot dB (pos + 1) vacant (put perm pos pos) := by
          rw [placeGroup, dite_eq_left hc', ite_eq_right (c := ¬get fs.data pos = slot)
            (fun h => h hgp), ite_eq_left hdp]
        obtain ⟨out, h1, h2⟩ := ih (pos + 1) vacant (put perm pos pos) (by omega) (by omega) hv
          (by rw [hcnt, hp1, hcs, ite_eq_right (by simp [hdp']), Nat.add_zero])
        refine ⟨out, by rw [e, h1], frame _ out pos.toNat h2 (by rw [BitVec.ofNat_toNat,
          BitVec.setWidth_eq]) (by omega) (fun _ => by rw [ite_eq_left hdp'])
          (fun h => absurd hgp' (by rw [h]; decide))⟩
      · have hdp' : d pos.toNat = false := by
          cases h : d pos.toNat
          · rfl
          · exact absurd ((hd pos hpn).2 h) hdp
        obtain ⟨a1, a2, a3, a4⟩ := nextVacant_spec fs leader slot dB (P := fun w => d w && !g w) hn
          (fun w hw => by rw [hd w hw, hg w hw]; simp) _ vacant rfl hv
        have hq : (g pos.toNat && !d pos.toNat) = true := by rw [hgp', hdp']; rfl
        -- a vacant offset is left: the movers are not more than the vacant offsets
        have hvn : (nextVacant fs leader slot dB vacant).toNat < fs.size.toNat := by
          refine Nat.lt_of_le_of_ne a2 (fun h => ?_)
          rw [h] at a4
          have := countP_range_lt (P := fun y => g y && !d y) hq hpn
          omega
        have e : placeGroup fs leader hl slot dB pos vacant perm =
            placeGroup fs leader hl slot dB (pos + 1) (nextVacant fs leader slot dB vacant + 1)
              (put perm pos (nextVacant fs leader slot dB vacant)) := by
          rw [placeGroup, dite_eq_left hc', ite_eq_right (c := ¬get fs.data pos = slot)
            (fun h => h hgp), ite_eq_right hdp]
          exact ite_eq_right (c := ¬nextVacant fs leader slot dB vacant < fs.size)
            (fun h => h (by bv_omega))
        obtain ⟨v, hV⟩ : ∃ v, nextVacant fs leader slot dB vacant = v := ⟨_, rfl⟩
        rw [hV] at a1 a2 a3 a4 hvn e
        have hv1 : (v + 1).toNat = v.toNat + 1 := toNat_succ (by omega)
        have hP := countP_range_succ (fun w => d w && !g w) v.toNat
        obtain ⟨out, h1, h2⟩ := ih (pos + 1) (v + 1) (put perm pos v) (by omega) (by omega)
          (by omega)
          (by rw [hv1, hP, ite_eq_left (a3 hvn), a4, hcnt, hp1, hcs, ite_eq_left hq])
        refine ⟨out, by rw [e, h1], frame _ out v.toNat h2 (by rw [BitVec.ofNat_toNat,
          BitVec.setWidth_eq]) (by omega) (fun _ => ?_)
          (fun h => absurd hgp' (by rw [h]; decide))⟩
        rw [ite_eq_right (c := d pos.toNat = true) (by rw [hdp']; decide), ← hcnt, ← a4]
        exact (filter_range_getElem (P := fun w => d w && !g w) (a3 hvn) hvn).symm
    · have hgp' : g pos.toNat = false := by
        cases h : g pos.toNat
        · rfl
        · exact absurd ((hg pos hpn).2 h) hgp
      have e : placeGroup fs leader hl slot dB pos vacant perm =
          placeGroup fs leader hl slot dB (pos + 1) vacant perm := by
        rw [placeGroup, dite_eq_left hc', ite_eq_left (c := ¬get fs.data pos = slot) hgp]
      obtain ⟨out, h1, h2⟩ := ih (pos + 1) vacant perm (by omega) (by omega) hv
        (by rw [hcnt, hp1, hcs, ite_eq_right (c := (g pos.toNat && !d pos.toNat) = true)
          (by simp [hgp']), Nat.add_zero])
      refine ⟨out, by rw [e, h1], fun x => ?_⟩
      rw [h2 x, hp1]
      by_cases hx : x.toNat = pos.toNat
      · rw [ite_eq_right (c := pos.toNat + 1 ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true)
          (fun h => by omega),
          ite_eq_right (c := pos.toNat ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true)
          (fun h => by rw [hx, hgp'] at h; exact absurd h.2.2 (by decide))]
      · by_cases hc1 : pos.toNat + 1 ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true
        · rw [ite_eq_left hc1, ite_eq_left
            (c := pos.toNat ≤ x.toNat ∧ x.toNat ≤ leader.toNat ∧ g x.toNat = true)
            ⟨by omega, hc1.2⟩]
        · rw [ite_eq_right hc1, ite_eq_right (fun h => hc1 ⟨by omega, h.2⟩)]

/-! ## The `leader` loop -/

theorem _root_.FlatShuffler.St.val_eq (st : FlatShuffler.St) (i : Nat) : st.val i = (st.slots.map Slot.val)[i]! := by
  simp [FlatShuffler.St.val, getElem!_def]
  cases st.slots[i]? <;> rfl

-- The word of an offset below `n` is `k` if and only if the offset is `k`.
theorem optW_eq_iff {o : Option Nat} {k : Word} {n : Nat} (hn : n ≤ MAX_N) (hk : k.toNat < n)
    (ho : ∀ p, o = some p → p < n) : optW o = k ↔ o = some k.toNat := by
  cases o with
  | none =>
    refine ⟨fun h => ?_, fun h => by cases h⟩
    simp only [optW] at h; rw [← h, toNat_NONE] at hk; rw [MAX_N_eq] at hn; omega
  | some p =>
    have hp := ho p rfl
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← h, optW, toNat_ofNat_small (by omega)]
    · cases h; exact eq_of_toNat (toNat_ofNat_small (by omega))

-- The slot at `k` has no copy above `k` if and only if `k` is its shallowest copy.
theorem leader_iff {e : Env} {fs : St} {st : FlatShuffler.St} (hs : Sim e fs st) {k : Word}
    (hk : k.toNat < st.len) :
    shallowestCopyPosition fs (get fs.data k) = k ↔
      isLast (st.slots.map Slot.val) k.toNat = true := by
  have hN := hs.len_lt
  rw [sim_copy hs, hs.data k hk, FlatShuffler.shallowestCopyPosition]
  have ho : ∀ p, (List.range st.len).reverse.find? (st.val · == st.val k.toNat) = some p →
      p < st.len :=
    fun p h => List.mem_range.1 (List.mem_reverse.1 (List.mem_of_find?_eq_some h))
  rw [optW_eq_iff hN hk ho, find?_last st.val st.len hk, isLast_iff]
  simp only [List.length_map, ← FlatShuffler.St.val_eq]
  exact Iff.rfl

theorem fregroup_skip {fs : St} {k : Word} {perm dB : Vector Word MAX_N} (hk : k < fs.size)
    (h : shallowestCopyPosition fs (get fs.data k) ≠ k) :
    regroup fs k perm dB = regroup fs (k + 1) perm dB := by
  rw [regroup, dite_eq_left hk]
  exact ite_eq_left h

theorem fregroup_lead {fs : St} {k : Word} {perm dB out : Vector Word MAX_N} (hk : k < fs.size)
    (h : shallowestCopyPosition fs (get fs.data k) = k)
    (hp : placeGroup fs k hk (get fs.data k) (markDesired fs k hk (get fs.data k) perm 0 dB) 0 0
      perm = some out) :
    regroup fs k perm dB = regroup fs (k + 1) out (markDesired fs k hk (get fs.data k) perm 0 dB) := by
  rw [regroup, dite_eq_left hk]
  dsimp only
  rw [ite_eq_right (fun h' => h' h), hp]

-- The offsets below `n` that `desiredBy` marks: none, or a leader below `k`.
def DInv (n : Nat) (k : Word) (dB : Vector Word MAX_N) : Prop :=
  ∀ w : Word, w.toNat < n → get dB w = NONE ∨ (get dB w).toNat < k.toNat

-- The `leader` loop from `k` is the fold of the list `regroup` over the last copies from `k`.
theorem sim_regroup {e : Env} {fs : St} {st : FlatShuffler.St} (hs : Sim e fs st) :
    ∀ m (k : Word) (perm dB : Vector Word MAX_N) (q : List Nat), st.len - k.toNat = m →
      k.toNat ≤ st.len → PermV st.len perm q → IsPerm q → DInv st.len k dB →
      ∃ r, ((List.range' k.toNat m).filter (isLast (st.slots.map Slot.val))).foldlM
          (fun q l => FlatShuffler.regroup (st.slots.map Slot.val) q (st.slots.map Slot.val)[l]!) q =
            .ok r ∧
        ∃ out, regroup fs k perm dB = some out ∧ PermV st.len out r ∧ IsPerm r := by
  have hN := hs.len_lt
  have hsz := hs.size
  have hn : fs.size.toNat ≤ MAX_N := by rw [hsz]; exact hN
  have hvl : (st.slots.map Slot.val).length = st.len := by simp [FlatShuffler.St.len]
  intro m
  induction m with
  | zero =>
    intro k perm dB q hm hk hpv hq _
    have hc : ¬k < fs.size := by bv_omega
    exact ⟨q, rfl, perm, by rw [regroup, dite_eq_right hc], hpv, hq⟩
  | succ m ih =>
    intro k perm dB q hm hk hpv hq hdi
    have hkn : k.toNat < st.len := by omega
    have hkw : k < fs.size := by bv_omega
    have hk1 : (k + 1).toNat = k.toNat + 1 := toNat_succ (by omega)
    by_cases hl : isLast (st.slots.map Slot.val) k.toNat = true
    · have hsc : shallowestCopyPosition fs (get fs.data k) = k := (leader_iff hs hkn).2 hl
      have hslot : get fs.data k = (st.slots.map Slot.val)[k.toNat]! := by
        rw [hs.data k hkn, FlatShuffler.St.val_eq]
      -- the list side
      obtain ⟨r1, hr1, hr1l, hr1p, hr1x⟩ :=
        regroup_ok (st.slots.map Slot.val)[k.toNat]! (hpv.1.trans hvl.symm) hq
      -- the flat side
      have hpm : ∀ y : Word, y.toNat ≤ k.toNat → (get perm y).toNat < MAX_N := fun y hy => by
        rw [hpv.2 y (by omega)]
        have := hq.1 y.toNat (by rw [hpv.1]; omega)
        rw [getElem!_pos q y.toNat (by rw [hpv.1]; omega)]
        have := hpv.1
        omega
      have mk := markDesired_spec fs hkw (get fs.data k) perm hn hpm (k.toNat + 1) 0 dB
        (by simp) (by simp)
      have hg : ∀ w : Word, w.toNat < fs.size.toNat → (get fs.data w = get fs.data k ↔
          ((st.slots.map Slot.val)[w.toNat]! == (st.slots.map Slot.val)[k.toNat]!) = true) :=
        fun w hw => by rw [hs.data w (by omega), hslot, FlatShuffler.St.val_eq, beq_iff_eq]
      have hd : ∀ w : Word, w.toNat < fs.size.toNat →
          (get (markDesired fs k hkw (get fs.data k) perm 0 dB) w = k ↔
            decide (w.toNat ∈ grpDest (st.slots.map Slot.val) q
              (st.slots.map Slot.val)[k.toNat]!) = true) := fun w hw => by
        rw [(mk w).1, decide_eq_true_iff]
        have hnk : get dB w ≠ k := fun h => by
          rcases hdi w (by omega) with h' | h'
          · rw [h'] at h; rw [← h, toNat_NONE] at hkn; rw [MAX_N_eq] at hN; omega
          · rw [h] at h'; omega
        rw [grpDest, List.mem_map]
        constructor
        · rintro (h | ⟨y, -, hy, hyd, hyp⟩)
          · exact absurd h hnk
          · refine ⟨y.toNat, mem_grp.2 ⟨by omega, ?_⟩, ?_⟩
            · rw [← FlatShuffler.St.val_eq, ← hs.data y (by omega), hyd, hslot]
            · rw [← hpv.2 y (by omega), hyp]
        · rintro ⟨y, hy, hyw⟩
          obtain ⟨hyn, hyv⟩ := mem_grp.1 hy
          have hyk : y ≤ k.toNat :=
            Nat.le_of_not_lt fun hlt => (isLast_iff.1 hl) y hlt hyn hyv
          have hy' : (BitVec.ofNat 64 y).toNat = y := toNat_ofNat_small (by omega)
          refine Or.inr ⟨BitVec.ofNat 64 y, by simp, by rw [hy']; exact hyk, ?_, ?_⟩
          · rw [hs.data _ (by rw [hy']; omega), hy', FlatShuffler.St.val_eq, hyv, hslot]
          · apply eq_of_toNat
            rw [hpv.2 _ (by rw [hy']; omega), hy', hyw]
      have hc := length_movers (st.slots.map Slot.val)[k.toNat]! (hpv.1.trans hvl.symm) hq
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, hvl] at hc
      obtain ⟨out, hpg, hout⟩ := placeGroup_spec fs hkw (get fs.data k)
        (markDesired fs k hkw (get fs.data k) perm 0 dB)
        (g := fun w => (st.slots.map Slot.val)[w]! == (st.slots.map Slot.val)[k.toNat]!)
        (d := fun w => decide (w ∈ grpDest (st.slots.map Slot.val) q
          (st.slots.map Slot.val)[k.toNat]!))
        hn hg hd (by rw [hsz]; exact Nat.le_of_eq hc) (k.toNat + 1) 0 0 perm
        (by simp) (by simp) (by simp) (by simp)
      have hpv' : PermV st.len out r1 := ⟨hr1l.trans hvl, fun i hi => by
        rw [hout i, hr1x i.toNat (by omega), regroupAt]
        by_cases hgi : ((st.slots.map Slot.val)[i.toNat]! ==
            (st.slots.map Slot.val)[k.toNat]!) = true
        · have hik : i.toNat ≤ k.toNat := Nat.le_of_not_lt fun hlt =>
            (isLast_iff.1 hl) _ hlt (by omega) (beq_iff_eq.1 hgi)
          rw [ite_eq_left (c := (0 : Word).toNat ≤ i.toNat ∧ i.toNat ≤ k.toNat ∧
              ((st.slots.map Slot.val)[i.toNat]! == (st.slots.map Slot.val)[k.toNat]!) = true)
            ⟨by simp, hik, hgi⟩, ite_eq_left (c := ((st.slots.map Slot.val)[i.toNat]! ==
              (st.slots.map Slot.val)[k.toNat]!) = true) hgi, hsz, hvl]
          by_cases hm : i.toNat ∈ grpDest (st.slots.map Slot.val) q
              (st.slots.map Slot.val)[k.toNat]!
          · rw [ite_eq_left (decide_eq_true hm), ite_eq_left hm]
          · rw [ite_eq_right (c := decide (i.toNat ∈ grpDest (st.slots.map Slot.val) q
              (st.slots.map Slot.val)[k.toNat]!) = true) (fun h => hm (of_decide_eq_true h)), ite_eq_right hm]
        · rw [ite_eq_right (c := (0 : Word).toNat ≤ i.toNat ∧ i.toNat ≤ k.toNat ∧
              ((st.slots.map Slot.val)[i.toNat]! == (st.slots.map Slot.val)[k.toNat]!) = true)
            (fun h => hgi h.2.2), ite_eq_right hgi, hpv.2 i hi]⟩
      have hdi' : DInv st.len (k + 1) (markDesired fs k hkw (get fs.data k) perm 0 dB) :=
        fun w hw => by
          rcases (mk w).2 with h | h
          · right; rw [h, hk1]; omega
          · rw [h]
            rcases hdi w hw with h' | h'
            · exact Or.inl h'
            · right; rw [hk1]; omega
      obtain ⟨r, h1, out', h2, h3, h4⟩ := ih (k + 1) out _ r1 (by omega) (by omega) hpv' hr1p hdi'
      rw [hk1] at h1
      rw [List.range'_succ, List.filter_cons,
        ite_eq_left (c := isLast (st.slots.map Slot.val) k.toNat = true) hl, List.foldlM_cons,
        hr1]
      exact ⟨r, h1, out', by rw [fregroup_lead hkw hsc hpg]; exact h2, h3, h4⟩
    · have hsc : shallowestCopyPosition fs (get fs.data k) ≠ k :=
        fun h => hl ((leader_iff hs hkn).1 h)
      obtain ⟨r, h1, out, h2, h3, h4⟩ := ih (k + 1) perm dB q (by omega) (by omega) hpv hq
        (fun w hw => by
          rcases hdi w hw with h | h
          · exact Or.inl h
          · right; omega)
      rw [hk1] at h1
      rw [List.range'_succ, List.filter_cons,
        ite_eq_right (c := isLast (st.slots.map Slot.val) k.toNat = true) hl]
      exact ⟨r, h1, out, by rw [fregroup_skip hkw hsc]; exact h2, h3, h4⟩

end FlatShuffler.Flat
