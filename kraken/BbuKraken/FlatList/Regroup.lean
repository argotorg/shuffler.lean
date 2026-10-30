import BbuKraken.FlatList.PermLoop
import BbuKraken.FlatList.PermList

/-!
The loops of the flat `permute` before `permuteLoop`: `readDestinations`, `clearDesired` and
the `leader` loop `regroup` with `markDesired`, `nextVacant` and `placeGroup`. The `leader`
loop gives the result of `Bbu.normalize` (`PermList.lean`).
-/

namespace Bbu.Flat

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

end Bbu.Flat
