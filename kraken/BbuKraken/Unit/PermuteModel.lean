import BbuKraken.Unit.Defs

/-!
# The flat model of `permute`: the facts for the asm proof

`Unit/Permute.lean` proves that the asm of `permute` gives `Flat.permute`. The asm has no bound on
its last loop, and the model has fuel (`Flat.permuteLoop`). This file gives the facts that make
the fuel sufficient and that keep the reads and writes of the asm below the size:

- `regroup_bij`: if `regroup` gives a permutation, it is a bijection of the offsets below the
  size (`Bij`). The proof follows the C++: each group of equal slots gets the offsets that its
  destinations give, and the offsets of two groups are different (`RInv`, `PInv`).
  `RInv.lt` and `PInv.lt` keep the offsets below the size during `regroup`.
- `permuteStep_cont`: an iteration of the last loop that continues keeps `Bij` and makes the
  measure `mu` smaller (2 for each offset below the top that is not in place, 1 if the top is in
  place). `mu` is at least 1 (`mu_pos`) and at most `2 * size - 1` (`mu_start`), so the fuel
  `2 * size` is sufficient (`fuel_pos`).

All indices are words below the size, and the size is at most `MAX_N`.
-/

namespace Bbu.Unit.Permute

/-! ## `get` and `put` -/

theorem get_put_self {α : Type} [Inhabited α] (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N)
    (x : α) : Flat.get (Flat.put v i x) i = x := by
  simp [Flat.get, Flat.put, hi]

theorem get_put_ne {α : Type} [Inhabited α] (v : Vector α MAX_N) {i j : Word} (x : α) (h : j ≠ i) :
    Flat.get (Flat.put v i x) j = Flat.get v j := by
  unfold Flat.get Flat.put
  split
  · next hj =>
    rw [Vector.getElem_setIfInBounds_ne]
    exact fun e => h (BitVec.eq_of_toNat_eq e.symm)
  · rfl

theorem get_put {α : Type} [Inhabited α] (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N)
    (x : α) (j : Word) : Flat.get (Flat.put v i x) j = if j = i then x else Flat.get v j := by
  split
  · next h => subst h; exact get_put_self v hi x
  · next h => exact get_put_ne v x h

/-! ## `shallowestCopyPosition` -/

section
variable (st : Flat.St) (x : StackSlot)

-- `copyBelow st x p` is the highest offset below `p` that holds `x`, or `NONE`.
theorem copyBelow_spec (p : Word) :
    (Flat.copyBelow st x p = Flat.NONE ∧ ∀ j < p, Flat.get st.data j ≠ x)
      ∨ (Flat.copyBelow st x p < p ∧ Flat.get st.data (Flat.copyBelow st x p) = x
        ∧ ∀ j < p, Flat.get st.data j = x → j ≤ Flat.copyBelow st x p) := by
  suffices h : ∀ k (p : Word), p.toNat = k →
      (Flat.copyBelow st x p = Flat.NONE ∧ ∀ j < p, Flat.get st.data j ≠ x)
      ∨ (Flat.copyBelow st x p < p ∧ Flat.get st.data (Flat.copyBelow st x p) = x
        ∧ ∀ j < p, Flat.get st.data j = x → j ≤ Flat.copyBelow st x p) from h _ p rfl
  intro k
  induction k with
  | zero =>
    intro p hp
    have h0 : p = 0 := by bv_omega
    subst h0
    left
    refine ⟨by rw [Flat.copyBelow]; rfl, fun j hj => absurd hj (by bv_omega)⟩
  | succ k ih =>
    intro p hp
    have h0 : p ≠ 0 := by bv_omega
    rw [Flat.copyBelow]; simp only [h0, ↓reduceDIte]
    split
    · next he =>
      right
      exact ⟨by bv_omega, he, fun j hj _ => by bv_omega⟩
    · next he =>
      rcases ih (p - 1) (by bv_omega) with ⟨hn, hall⟩ | ⟨hlt, hx, hmax⟩
      · left
        refine ⟨hn, fun j hj => ?_⟩
        by_cases hjp : j = p - 1
        · subst hjp; exact he
        · exact hall j (by bv_omega)
      · right
        refine ⟨by bv_omega, hx, fun j hj hjx => ?_⟩
        by_cases hjp : j = p - 1
        · subst hjp; exact absurd hjx he
        · exact hmax j (by bv_omega) hjx

end

-- The leader of offset `i`: the highest offset with the slot of `i`.
def lead (st : Flat.St) (i : Word) : Word := Flat.shallowestCopyPosition st (Flat.get st.data i)

theorem lead_spec (st : Flat.St) {i : Word} (hi : i < st.size) :
    i ≤ lead st i ∧ lead st i < st.size ∧ Flat.get st.data (lead st i) = Flat.get st.data i
      ∧ ∀ j < st.size, Flat.get st.data j = Flat.get st.data i → j ≤ lead st i := by
  rcases copyBelow_spec st (Flat.get st.data i) st.size with ⟨-, hall⟩ | ⟨hlt, hx, hmax⟩
  · exact absurd rfl (hall i hi)
  · exact ⟨hmax i hi rfl, hlt, hx, hmax⟩

-- Two offsets with the same slot have the same leader.
theorem lead_eq (st : Flat.St) {i j : Word} (h : Flat.get st.data i = Flat.get st.data j) :
    lead st i = lead st j := by
  simp only [lead, h]

/-! ## The loops of `regroup` -/

-- `pos + 1 ≤ i` and `pos ≤ i` agree for `i ≠ pos` and `pos < size ≤ 2^64 - 1`.
theorem succ_le_iff {pos i n : Word} (hlt : pos < n) (e : i ≠ pos) : pos + 1 ≤ i ↔ pos ≤ i := by
  constructor <;> intro <;> bv_omega

theorem readDestinations_spec (st : Flat.St) (hn : st.size.toNat ≤ MAX_N) (pos : Word)
    (v p : Vector Word MAX_N) (h : Flat.readDestinations st pos v = some p) :
    ∀ i < st.size, Flat.get p i = if pos ≤ i then Flat.get st.dest i else Flat.get v i := by
  fun_induction Flat.readDestinations st pos v with
  | case1 pos v hlt d hd => simp at h
  | case2 pos v hlt d hd ih =>
    intro i hi
    rw [ih h i hi, get_put _ (by bv_omega)]
    by_cases e : i = pos
    · subst e; rw [ite_eq_right (by bv_omega), ite_eq_left rfl, ite_eq_left (BitVec.le_refl _)]
    · rw [ite_eq_right e]; exact ite_cond_congr (propext (succ_le_iff hlt e))
  | case3 pos v hge =>
    intro i hi
    cases h
    rw [ite_eq_right (by bv_omega)]

theorem clearDesired_spec (st : Flat.St) (hn : st.size.toNat ≤ MAX_N) (pos : Word)
    (v : Vector Word MAX_N) :
    ∀ i < st.size, Flat.get (Flat.clearDesired st pos v) i
      = if pos ≤ i then Flat.NONE else Flat.get v i := by
  fun_induction Flat.clearDesired st pos v with
  | case1 pos v hlt ih =>
    intro i hi
    rw [ih i hi, get_put _ (by bv_omega)]
    by_cases e : i = pos
    · subst e; rw [ite_eq_right (by bv_omega), ite_eq_left rfl, ite_eq_left (BitVec.le_refl _)]
    · rw [ite_eq_right e]; exact ite_cond_congr (propext (succ_le_iff hlt e))
  | case2 pos v hge =>
    intro i hi
    rw [ite_eq_right (by bv_omega)]

section
variable (st : Flat.St) (L : Word) (hl : L < st.size) (σ : StackSlot)

theorem markDesired_spec (p : Vector Word MAX_N) (pos : Word) (dB : Vector Word MAX_N) :
    (∀ j, pos ≤ j → j ≤ L → Flat.get st.data j = σ → (Flat.get p j).toNat < MAX_N →
        Flat.get (Flat.markDesired st L hl σ p pos dB) (Flat.get p j) = L)
      ∧ ∀ x, (∀ j, pos ≤ j → j ≤ L → Flat.get st.data j = σ → Flat.get p j ≠ x) →
        Flat.get (Flat.markDesired st L hl σ p pos dB) x = Flat.get dB x := by
  fun_induction Flat.markDesired st L hl σ p pos dB with
  | case1 pos dB hle dB1 ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun j hj hjl hd hlt => ?_, fun x hx => ?_⟩
    · by_cases e : j = pos
      · subst e
        by_cases hw : ∃ k, j + 1 ≤ k ∧ k ≤ L ∧ Flat.get st.data k = σ ∧ Flat.get p k = Flat.get p j
        · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hw
          rw [← hk4]; exact ih1 k hk1 hk2 hk3 (hk4 ▸ hlt)
        · rw [ih2 _ (fun k hk1 hk2 hk3 he => hw ⟨k, hk1, hk2, hk3, he⟩)]
          simp only [dB1, hd]
          exact get_put_self _ hlt _
      · exact ih1 j (by clear ih1 ih2 dB1; bv_omega) hjl hd hlt
    · rw [ih2 x (fun j hj hjl hd => hx j (by clear ih1 ih2 dB1 hx; bv_omega) hjl hd)]
      simp only [dB1]
      split
      · next hd => exact get_put_ne _ _ (Ne.symm (hx pos (BitVec.le_refl _) hle hd))
      · rfl
  | case2 pos dB hgt =>
    exact ⟨fun j hj hjl => absurd (BitVec.le_trans hj hjl) hgt, fun _ _ => rfl⟩

theorem nextVacant_spec (dB : Vector Word MAX_N) (vac : Word) :
    vac ≤ Flat.nextVacant st L σ dB vac
      ∧ (Flat.nextVacant st L σ dB vac < st.size →
        Flat.get dB (Flat.nextVacant st L σ dB vac) = L
          ∧ Flat.get st.data (Flat.nextVacant st L σ dB vac) ≠ σ) := by
  fun_induction Flat.nextVacant st L σ dB vac with
  | case1 vac h ih => exact ⟨by have := ih.1; bv_omega, ih.2⟩
  | case2 vac h =>
    refine ⟨BitVec.le_refl _, fun hlt => ?_⟩
    exact Classical.byContradiction fun hc => h ⟨hlt, hc⟩

end

-- The invariant of `placeGroup` for the group of `L` with the slot `σ`, from `pos`: each slot of
-- the group below `pos` has its own offset in `pc`, its own offset if `dB` gives it to the
-- group, else an offset below `vac` that `dB` gives to the group and that holds no slot of the
-- group. The other offsets keep the offsets of `p`.
structure PInv (st : Flat.St) (L : Word) (σ : StackSlot) (dB p : Vector Word MAX_N) (pos vac : Word)
    (pc : Vector Word MAX_N) : Prop where
  place : ∀ i < pos, Flat.get st.data i = σ →
    (Flat.get pc i = i ∧ Flat.get dB i = L)
      ∨ (Flat.get pc i < vac ∧ Flat.get pc i < st.size ∧ Flat.get dB (Flat.get pc i) = L
        ∧ Flat.get st.data (Flat.get pc i) ≠ σ)
  inj : ∀ i < pos, ∀ k < pos, Flat.get st.data i = σ → Flat.get st.data k = σ →
    Flat.get pc i = Flat.get pc k → i = k
  keep : ∀ i, (pos ≤ i ∨ Flat.get st.data i ≠ σ) → Flat.get pc i = Flat.get p i

theorem placeGroup_spec (st : Flat.St) (hn : st.size.toNat ≤ MAX_N) (L : Word) (hl : L < st.size)
    (σ : StackSlot) (dB p : Vector Word MAX_N) (pos vac : Word) (pc p' : Vector Word MAX_N)
    (hpos : pos ≤ L + 1) (hinv : PInv st L σ dB p pos vac pc)
    (h : Flat.placeGroup st L hl σ dB pos vac pc = some p') : ∃ vac', PInv st L σ dB p (L + 1) vac' p' := by
  have hlN : L.toNat < st.size.toNat := hl
  fun_induction Flat.placeGroup st L hl σ dB pos vac pc with
  | case1 pos vac pc hle hd ih =>
    refine ih (by bv_omega) ⟨fun i hi hdi => hinv.place i ?_ hdi, fun i hi k hk hdi hdk => hinv.inj i ?_ k ?_ hdi hdk,
      fun i hi => hinv.keep i ?_⟩ h
    · have : i ≠ pos := fun e => hd (e ▸ hdi)
      bv_omega
    · have : i ≠ pos := fun e => hd (e ▸ hdi)
      bv_omega
    · have : k ≠ pos := fun e => hd (e ▸ hdk)
      bv_omega
    · rcases hi with hi | hi
      · exact Or.inl (by bv_omega)
      · exact Or.inr hi
  | case2 pos vac pc hle hd hdB ih =>
    have hd : Flat.get st.data pos = σ := Classical.not_not.mp hd
    have hpm : pos.toNat < MAX_N := by bv_omega
    have hget : ∀ i, i ≠ pos → Flat.get (Flat.put pc pos pos) i = Flat.get pc i :=
      fun i e => get_put_ne _ _ e
    refine ih (by bv_omega) ⟨fun i hi hdi => ?_, fun i hi k hk hdi hdk he => ?_, fun i hi => ?_⟩ h
    · by_cases e : i = pos
      · subst e; exact Or.inl ⟨get_put_self _ hpm _, hdB⟩
      · rw [hget i e]; exact hinv.place i (by bv_omega) hdi
    · -- `pos` is the only slot below `pos + 1` whose offset is `pos`.
      have hpos : ∀ k < pos, Flat.get st.data k = σ → Flat.get pc k ≠ pos := fun k hk hdk he =>
        (hinv.place k hk hdk).elim (fun h1 => absurd (h1.1.symm.trans he) (by bv_omega))
          (fun h2 => h2.2.2.2 (he ▸ hd))
      by_cases ei : i = pos <;> by_cases ek : k = pos
      · exact ei.trans ek.symm
      · subst ei; rw [get_put_self _ hpm, hget k ek] at he
        exact absurd he.symm (hpos k (by bv_omega) hdk)
      · subst ek; rw [get_put_self _ hpm, hget i ei] at he
        exact absurd he (hpos i (by bv_omega) hdi)
      · rw [hget i ei, hget k ek] at he
        exact hinv.inj i (by bv_omega) k (by bv_omega) hdi hdk he
    · have e : i ≠ pos := by
        rintro rfl; rcases hi with hi | hi
        · bv_omega
        · exact hi hd
      rw [hget i e]
      exact hinv.keep i (hi.imp_left fun _ => by bv_omega)
  | case3 pos vac pc hle hd hdB v hv => simp at h
  | case4 pos vac pc hle hd hdB v hv ih =>
    have hd : Flat.get st.data pos = σ := Classical.not_not.mp hd
    have hv : v < st.size := Classical.not_not.mp hv
    have hvs : vac ≤ v ∧ (v < st.size → Flat.get dB v = L ∧ Flat.get st.data v ≠ σ) :=
      nextVacant_spec st L σ dB vac
    clear_value v
    obtain ⟨hv1, hv2, hv3⟩ := And.intro hvs.1 (hvs.2 hv)
    have hpm : pos.toNat < MAX_N := by bv_omega
    have hget : ∀ i, i ≠ pos → Flat.get (Flat.put pc pos v) i = Flat.get pc i :=
      fun i e => get_put_ne _ _ e
    refine ih (by bv_omega) ⟨fun i hi hdi => ?_, fun i hi k hk hdi hdk he => ?_, fun i hi => ?_⟩ h
    · by_cases e : i = pos
      · subst e; rw [get_put_self _ hpm]
        exact Or.inr ⟨by bv_omega, hv, hv2, hv3⟩
      · rw [hget i e]
        rcases hinv.place i (by bv_omega) hdi with h1 | ⟨h1, h2, h3, h4⟩
        · exact Or.inl h1
        · exact Or.inr ⟨by bv_omega, h2, h3, h4⟩
    · have hpos : ∀ k < pos, Flat.get st.data k = σ → Flat.get pc k ≠ v := fun k hk hdk he =>
        (hinv.place k hk hdk).elim (fun h1 => hv3 (by rw [← he, h1.1]; exact hdk))
          (fun h2 => absurd h2.1 (by rw [he]; bv_omega))
      by_cases ei : i = pos <;> by_cases ek : k = pos
      · exact ei.trans ek.symm
      · subst ei; rw [get_put_self _ hpm, hget k ek] at he
        exact absurd he.symm (hpos k (by bv_omega) hdk)
      · subst ek; rw [get_put_self _ hpm, hget i ei] at he
        exact absurd he (hpos i (by bv_omega) hdi)
      · rw [hget i ei, hget k ek] at he
        exact hinv.inj i (by bv_omega) k (by bv_omega) hdi hdk he
    · have e : i ≠ pos := by
        rintro rfl; rcases hi with hi | hi
        · bv_omega
        · exact hi hd
      rw [hget i e]
      exact hinv.keep i (hi.imp_left fun _ => by bv_omega)
  | case5 pos vac pc hgt =>
    cases h
    have e : pos = L + 1 := by bv_omega
    exact ⟨vac, e ▸ hinv⟩


/-! ## `regroup` gives a bijection -/


theorem ofNat_toNat (w : Word) : BitVec.ofNat 64 w.toNat = w := by
  apply BitVec.eq_of_toNat_eq; simp

-- The destinations of `PermOk` are a bijection.
theorem permOk_bij {st : Flat.St} (hn : st.size.toNat ≤ MAX_N) (hp : PermOk st)
    {p0 : Vector Word MAX_N} (h : Flat.readDestinations st 0 Flat.initial = some p0) :
    Bij st.size p0 := by
  have hr := readDestinations_spec st hn 0 _ _ h
  have hd : ∀ i < st.size, Flat.get p0 i = Flat.get st.dest i := fun i hi => by
    rw [hr i hi, ite_eq_left (by bv_omega)]
  refine ⟨fun i hi => ?_, fun i hi k hk he => ?_⟩
  · have := hp.lt i.toNat hi
    rw [ofNat_toNat] at this
    rw [hd i hi]; exact this
  · rw [hd i hi, hd k hk] at he
    have := hp.inj i.toNat hi k.toNat hk (by rw [ofNat_toNat, ofNat_toNat]; exact he)
    exact BitVec.eq_of_toNat_eq this

-- `readDestinations` gives a result if no destination below the size is `NONE`.
theorem rd_some (st : Flat.St) (hne : ∀ i < st.size, Flat.get st.dest i ≠ Flat.NONE)
    (pos : Word) (v : Vector Word MAX_N) : ∃ p, Flat.readDestinations st pos v = some p := by
  fun_induction Flat.readDestinations st pos v with
  | case1 pos v hlt d hd => exact absurd hd (hne pos hlt)
  | case2 pos v hlt d hd ih => exact ih
  | case3 pos v hge => exact ⟨_, rfl⟩

-- The destinations of `PermOk` are below the size, so not `NONE`: `readDestinations` gives a
-- result.
theorem rd_some_of_permOk {st : Flat.St} (hn : st.size.toNat ≤ MAX_N) (hp : PermOk st) :
    ∃ p, Flat.readDestinations st 0 Flat.initial = some p := by
  refine rd_some st (fun i hi e => ?_) 0 _
  have := hp.lt i.toNat (BitVec.lt_def.mp hi)
  rw [ofNat_toNat, e] at this
  have h1 : Flat.NONE.toNat = 2 ^ 64 - 1 := by decide
  simp only [MAX_N] at hn
  omega

-- `permuteMapping` is `permute` with the result of `readDestinations`.
theorem permuteMapping_of {st : Flat.St} {p : Vector Word MAX_N}
    (h : Flat.readDestinations st 0 Flat.initial = some p) :
    Flat.permuteMapping st = Flat.permute st p := by
  rw [Flat.permuteMapping, h]

-- The invariant of `regroup` before the leader `L`, from the permutation `p0` of the
-- destinations. An offset whose leader is below `L` has the destination of an offset with its
-- slot, and the offsets of two such offsets with the same slot are different. The other offsets
-- keep their destinations. `dB` marks no offset with a leader from `L` on.
structure RInv (st : Flat.St) (p0 : Vector Word MAX_N) (L : Word) (p dB : Vector Word MAX_N) :
    Prop where
  src : ∀ i < st.size, lead st i < L →
    ∃ j < st.size, Flat.get st.data j = Flat.get st.data i ∧ Flat.get p0 j = Flat.get p i
  inj : ∀ i < st.size, ∀ k < st.size, Flat.get st.data i = Flat.get st.data k → lead st i < L →
    Flat.get p i = Flat.get p k → i = k
  keep : ∀ i < st.size, L ≤ lead st i → Flat.get p i = Flat.get p0 i
  mark : ∀ x < st.size, Flat.get dB x = Flat.NONE ∨ Flat.get dB x < L

theorem RInv.init (st : Flat.St) (hn : st.size.toNat ≤ MAX_N) (p0 : Vector Word MAX_N) :
    RInv st p0 0 p0 (Flat.clearDesired st 0 Flat.initial) where
  src _ _ h := absurd h (by bv_omega)
  inj _ _ _ _ _ h := absurd h (by bv_omega)
  keep _ _ _ := rfl
  mark x hx := Or.inl (by rw [clearDesired_spec st hn 0 _ x hx, ite_eq_left (by bv_omega)])

-- An offset that is not a leader.
theorem RInv.skip {st : Flat.St} {p0 p dB : Vector Word MAX_N} {L : Word}
    (hr : RInv st p0 L p dB) (hl : L < st.size)
    (hlead : lead st L ≠ L) : RInv st p0 (L + 1) p dB := by
  have hLN : L.toNat < st.size.toNat := hl
  have hno : ∀ i < st.size, lead st i ≠ L := fun i hi e =>
    hlead (by rw [← e]; exact lead_eq st (lead_spec st hi).2.2.1)
  have hlt : ∀ i < st.size, lead st i < L + 1 → lead st i < L := fun i hi h => by
    have := hno i hi; bv_omega
  exact ⟨fun i hi h => hr.src i hi (hlt i hi h), fun i hi k hk hd h => hr.inj i hi k hk hd (hlt i hi h),
    fun i hi h => hr.keep i hi (by bv_omega), fun x hx => (hr.mark x hx).imp_right fun h => by bv_omega⟩

theorem PInv.init (st : Flat.St) (L : Word) (σ : StackSlot) (dB p : Vector Word MAX_N) :
    PInv st L σ dB p 0 0 p :=
  ⟨fun _ hi => absurd hi (by bv_omega), fun _ hi => absurd hi (by bv_omega), fun _ _ => rfl⟩

-- The group of the leader `L`, with the slot `σ`.
theorem RInv.group {st : Flat.St} {p0 p dB : Vector Word MAX_N} {L : Word}
    (hn : st.size.toNat ≤ MAX_N) (hb : Bij st.size p0) (hr : RInv st p0 L p dB) (hl : L < st.size)
    {σ : StackSlot} (hσ : Flat.get st.data L = σ) (hlead : lead st L = L) {vac : Word}
    {p' : Vector Word MAX_N} (hp : PInv st L σ (Flat.markDesired st L hl σ p 0 dB) p (L + 1) vac p') :
    RInv st p0 (L + 1) p' (Flat.markDesired st L hl σ p 0 dB) := by
  have hLN : L.toNat < st.size.toNat := hl
  obtain ⟨m1, m2⟩ := markDesired_spec st L hl σ p 0 dB
  generalize Flat.markDesired st L hl σ p 0 dB = dB' at m1 m2 hp ⊢
  -- The members of the group are the offsets with the leader `L`.
  have hmem : ∀ i < st.size, Flat.get st.data i = σ ↔ lead st i = L := by
    intro i hi; constructor
    · intro h; rw [← hlead]; exact lead_eq st (h.trans hσ.symm)
    · intro h; rw [← hσ, ← (lead_spec st hi).2.2.1, h]
  have hle : ∀ i < st.size, lead st i = L → i ≤ L := fun i hi h => h ▸ (lead_spec st hi).1
  have hp0 : ∀ j ≤ L, Flat.get st.data j = σ → Flat.get p j = Flat.get p0 j := fun j hjl hdj =>
    hr.keep j (by bv_omega) (by rw [(hmem j (by bv_omega)).1 hdj]; exact BitVec.le_refl _)
  -- An offset that `dB'` marks with `L` is the destination of a member.
  have hsrc : ∀ y < st.size, Flat.get dB' y = L →
      ∃ j < st.size, Flat.get st.data j = σ ∧ Flat.get p0 j = y := by
    intro y hy he
    refine Classical.byContradiction fun hc => ?_
    rw [m2 y (fun j _ hjl hdj hpj => hc ⟨j, by bv_omega, hdj, (hp0 j hjl hdj).symm.trans hpj⟩)] at he
    rcases hr.mark y hy with h | h
    · rw [h] at he; unfold Flat.NONE at he; bv_omega
    · rw [he] at h; exact absurd h (BitVec.lt_irrefl _)
  refine ⟨fun i hi h => ?_, fun i hi k hk hd h he => ?_, fun i hi h => ?_, fun x hx => ?_⟩
  · by_cases e : lead st i = L
    · have hdi : Flat.get st.data i = σ := (hmem i hi).2 e
      have hil : i ≤ L := hle i hi e
      have hy : Flat.get p' i < st.size ∧ Flat.get dB' (Flat.get p' i) = L := by
        rcases hp.place i (by bv_omega) hdi with ⟨h1, h2⟩ | ⟨_, h2, h3, _⟩
        · rw [h1]; exact ⟨hi, h2⟩
        · exact ⟨h2, h3⟩
      obtain ⟨j, hj, hdj, hpj⟩ := hsrc _ hy.1 hy.2
      exact ⟨j, hj, hdj.trans hdi.symm, hpj⟩
    · have hdi : Flat.get st.data i ≠ σ := fun h => e ((hmem i hi).1 h)
      rw [hp.keep i (Or.inr hdi)]
      exact hr.src i hi (by bv_omega)
  · by_cases e : lead st i = L
    · have hdi : Flat.get st.data i = σ := (hmem i hi).2 e
      have hdk : Flat.get st.data k = σ := hd ▸ hdi
      have hkl := hle k hk ((hmem k hk).1 hdk)
      have hil := hle i hi e
      exact hp.inj i (by bv_omega) k (by bv_omega) hdi hdk he
    · have hdi : Flat.get st.data i ≠ σ := fun h => e ((hmem i hi).1 h)
      have hdk : Flat.get st.data k ≠ σ := hd ▸ hdi
      rw [hp.keep i (Or.inr hdi), hp.keep k (Or.inr hdk)] at he
      exact hr.inj i hi k hk hd (by bv_omega) he
  · have e : lead st i ≠ L := fun e => by rw [e] at h; bv_omega
    have hdi : Flat.get st.data i ≠ σ := fun h => e ((hmem i hi).1 h)
    rw [hp.keep i (Or.inr hdi)]
    exact hr.keep i hi (by bv_omega)
  · by_cases hw : ∃ j, 0 ≤ j ∧ j ≤ L ∧ Flat.get st.data j = σ ∧ Flat.get p j = x
    · obtain ⟨j, h0, hjl, hdj, hpj⟩ := hw
      have hlt : (Flat.get p j).toNat < MAX_N := by
        have := hb.1 j (by bv_omega); rw [hp0 j hjl hdj]; bv_omega
      rw [← hpj, m1 j h0 hjl hdj hlt]
      exact Or.inr (by bv_omega)
    · rw [m2 x (fun j h0 hjl hdj hpj => hw ⟨j, h0, hjl, hdj, hpj⟩)]
      exact (hr.mark x hx).imp_right fun h => by bv_omega

-- At the end, `p` is a bijection.
theorem RInv.bij {st : Flat.St} {p0 p dB : Vector Word MAX_N} {L : Word} (hb : Bij st.size p0)
    (hr : RInv st p0 L p dB) (hL : st.size ≤ L) : Bij st.size p := by
  have hall : ∀ i < st.size, lead st i < L := fun i hi => by
    have := (lead_spec st hi).2.1; bv_omega
  refine ⟨fun i hi => ?_, fun i hi k hk he => ?_⟩
  · obtain ⟨j, hj, _, hpj⟩ := hr.src i hi (hall i hi)
    rw [← hpj]; exact hb.1 j hj
  · obtain ⟨j, hj, hdj, hpj⟩ := hr.src i hi (hall i hi)
    obtain ⟨j', hj', hdj', hpj'⟩ := hr.src k hk (hall k hk)
    have e : j = j' := hb.2 j hj j' hj' (by rw [hpj, hpj', he])
    subst e
    exact hr.inj i hi k hk (hdj.symm.trans hdj') (hall i hi) he

-- During `regroup`, the offsets are below the size.
theorem RInv.lt {st : Flat.St} {p0 p dB : Vector Word MAX_N} {L : Word} (hb : Bij st.size p0)
    (hr : RInv st p0 L p dB) : ∀ i < st.size, Flat.get p i < st.size := by
  intro i hi
  by_cases h : lead st i < L
  · obtain ⟨j, hj, _, hpj⟩ := hr.src i hi h
    rw [← hpj]; exact hb.1 j hj
  · rw [hr.keep i hi (by bv_omega)]; exact hb.1 i hi

-- During `placeGroup`, the offsets are below the size.
theorem PInv.lt {st : Flat.St} {L : Word} {σ : StackSlot} {dB p pc : Vector Word MAX_N}
    {pos vac : Word} (hlt : ∀ i < st.size, Flat.get p i < st.size)
    (hp : PInv st L σ dB p pos vac pc) : ∀ i < st.size, Flat.get pc i < st.size := by
  intro i hi
  by_cases h : pos ≤ i ∨ Flat.get st.data i ≠ σ
  · rw [hp.keep i h]; exact hlt i hi
  · have h1 : i < pos := by
      have : ¬pos ≤ i := fun e => h (Or.inl e)
      bv_omega
    have h2 : Flat.get st.data i = σ := Classical.byContradiction fun e => h (Or.inr e)
    rcases hp.place i h1 h2 with ⟨e, _⟩ | ⟨_, e, _⟩
    · rw [e]; exact hi
    · exact e

theorem regroup_spec (st : Flat.St) (hn : st.size.toNat ≤ MAX_N) (p0 : Vector Word MAX_N)
    (hb : Bij st.size p0) (L : Word) (p dB pf : Vector Word MAX_N) (hr : RInv st p0 L p dB)
    (h : Flat.regroup st L p dB = some pf) : Bij st.size pf := by
  fun_induction Flat.regroup st L p dB with
  | case1 L p dB hl slot hne ih => exact ih (hr.skip hl hne) h
  | case2 => simp at h
  | case3 L p dB hl slot hlead dB' p' hpg ih =>
    have hpos : (0 : Word) ≤ L + 1 := by bv_omega
    obtain ⟨vac, hp⟩ := placeGroup_spec st hn L hl slot dB' p 0 0 p p' hpos (PInv.init ..) hpg
    exact ih (hr.group hn hb hl rfl (Classical.not_not.mp hlead) hp) h
  | case4 L p dB hge =>
    cases h
    exact hr.bij hb (by bv_omega)

-- The permutation of `permute` after `regroup` is a bijection, for a bijection `p0`.
theorem regroup_bij {st : Flat.St} (hn : st.size.toNat ≤ MAX_N) {p0 p : Vector Word MAX_N}
    (hb : Bij st.size p0)
    (h : Flat.regroup st 0 p0 (Flat.clearDesired st 0 Flat.initial) = some p) : Bij st.size p :=
  regroup_spec st hn p0 hb 0 p0 _ p (RInv.init st hn p0) h

/-! ## The measure of the loop of `permute` -/


theorem countP_lt {n : Nat} {f g : Nat → Bool} (hle : ∀ i < n, f i → g i)
    (hlt : ∃ j < n, ¬ f j ∧ g j) :
    (List.range n).countP f < (List.range n).countP g := by
  induction n with
  | zero => obtain ⟨j, hj, -⟩ := hlt; omega
  | succ n ih =>
    simp only [List.range_succ, List.countP_append, List.countP_singleton]
    have hle' : ∀ i < n, f i → g i := fun i hi => hle i (by omega)
    have hmono : (List.range n).countP f ≤ (List.range n).countP g :=
      List.countP_mono_left (fun i hi hf => hle' i (List.mem_range.mp hi) hf)
    obtain ⟨j, hj, hfj, hgj⟩ := hlt
    by_cases hjn : j = n
    · subst hjn
      have := hle j (by omega)
      grind
    · have := ih hle' ⟨j, by omega, hfj, hgj⟩
      have := hle n (by omega)
      grind

theorem countP_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    (List.range n).countP f = (List.range n).countP g :=
  List.countP_congr (fun i hi => by rw [h i (List.mem_range.mp hi)])

-- The number of offsets below `top` that are not in place.
def misplaced (top : Word) (p : Vector Word MAX_N) : Nat :=
  (List.range top.toNat).countP fun i => Flat.get p (BitVec.ofNat 64 i) != BitVec.ofNat 64 i

-- The measure of the loop of `permute`: 2 for each offset below `top` that is not in place, and
-- 1 if `top` is in place.
def mu (top : Word) (p : Vector Word MAX_N) : Nat :=
  2 * misplaced top p + if Flat.get p top = top then 1 else 0

theorem mu_le (top : Word) (p : Vector Word MAX_N) : mu top p ≤ 2 * top.toNat + 1 := by
  have : misplaced top p ≤ top.toNat := by
    unfold misplaced
    exact Nat.le_trans List.countP_le_length (by simp)
  unfold mu; split <;> omega

theorem mu_pos {n : Word} {p : Vector Word MAX_N} (hb : Bij n p) (h0 : 0 < n) : 1 ≤ mu (n - 1) p := by
  unfold mu
  split
  · omega
  · next ht =>
    have hj := hb.1 (n - 1) (by bv_omega)
    generalize hj' : Flat.get p (n - 1) = j at hj ht
    have hjj : Flat.get p j ≠ j := fun e => ht (hb.2 j hj (n - 1) (by bv_omega) (e.trans hj'.symm))
    have hjt : j.toNat < (n - 1).toNat := by
      have : j ≠ n - 1 := ht
      bv_omega
    have : 0 < misplaced (n - 1) p := by
      unfold misplaced
      apply List.countP_pos_iff.mpr
      exact ⟨j.toNat, List.mem_range.mpr hjt, by simp [hjj]⟩
    omega

-- The permutation after `exchange` at `pos`.
def swapP (p : Vector Word MAX_N) (top pos : Word) : Vector Word MAX_N :=
  Flat.put (Flat.put p pos (Flat.get p top)) top (Flat.get p pos)

theorem get_swapP (p : Vector Word MAX_N) {top pos : Word} (ht : top.toNat < MAX_N)
    (hpos : pos.toNat < MAX_N) (i : Word) :
    Flat.get (swapP p top pos) i
      = if i = top then Flat.get p pos else if i = pos then Flat.get p top else Flat.get p i := by
  unfold swapP; rw [get_put _ ht, get_put _ hpos]

-- The transposition of `top` and `pos`.
def tr (top pos i : Word) : Word := if i = top then pos else if i = pos then top else i

theorem tr_inj (top pos : Word) {i k : Word} (h : tr top pos i = tr top pos k) : i = k := by
  unfold tr at h
  by_cases h1 : i = top <;> by_cases h3 : k = top <;> by_cases h2 : i = pos <;> by_cases h4 : k = pos
    <;> simp_all

theorem get_swapP' (p : Vector Word MAX_N) {top pos : Word} (ht : top.toNat < MAX_N)
    (hpos : pos.toNat < MAX_N) (i : Word) : Flat.get (swapP p top pos) i = Flat.get p (tr top pos i) := by
  rw [get_swapP p ht hpos]; unfold tr
  by_cases h1 : i = top
  · simp [h1]
  · by_cases h2 : i = pos
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapP_bij {n top pos : Word} {p : Vector Word MAX_N} (hn : n.toNat ≤ MAX_N) (hb : Bij n p)
    (ht : top < n) (hpos : pos < n) : Bij n (swapP p top pos) := by
  have hg := get_swapP' p (top := top) (pos := pos) (by bv_omega) (by bv_omega)
  have hs : ∀ i < n, tr top pos i < n := by
    intro i hi; unfold tr; split
    · exact hpos
    · split
      · exact ht
      · exact hi
  refine ⟨fun i hi => ?_, fun i hi k hk he => ?_⟩
  · rw [hg]; exact hb.1 _ (hs i hi)
  · rw [hg, hg] at he; exact tr_inj top pos (hb.2 _ (hs i hi) _ (hs k hk) he)

theorem swapP_mu {n pos : Word} {p : Vector Word MAX_N} (hn : n.toNat ≤ MAX_N) (hb : Bij n p)
    (hpos : pos < n) (hne : pos ≠ n - 1)
    (hc : Flat.get p (n - 1) = pos ∨ (Flat.get p (n - 1) = n - 1 ∧ Flat.get p pos ≠ pos)) :
    mu (n - 1) (swapP p (n - 1) pos) < mu (n - 1) p := by
  generalize htop : n - 1 = top at hne hc ⊢
  have ht : top < n := by bv_omega
  have hpt : pos.toNat < top.toNat := by bv_omega
  have hg := get_swapP' p (top := top) (pos := pos) (by bv_omega) (by bv_omega)
  -- The offsets below `top` are not `top`.
  have hw : ∀ i < top.toNat, BitVec.ofNat 64 i ≠ top := by
    intro i hi e
    have h1 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := top.isLt; omega)
    rw [e] at h1; omega
  rcases hc with hc | ⟨hc, hpp⟩
  · -- `pos` is the destination of the top: the swap puts `pos` in place.
    have hpp : Flat.get p pos ≠ pos := fun e => hne (hb.2 pos hpos top ht (e.trans hc.symm))
    have hlt : misplaced top (swapP p top pos) < misplaced top p := by
      refine countP_lt (fun i hi hf => ?_) ⟨pos.toNat, hpt, ?_, ?_⟩
      · by_cases e : BitVec.ofNat 64 i = pos
        · rw [e]; simpa using hpp
        · rw [hg] at hf; simpa [tr, hw i hi, e] using hf
      · rw [ofNat_toNat, hg]; simp [tr, hne, hc]
      · rw [ofNat_toNat]; simpa using hpp
    unfold mu; split <;> split <;> omega
  · -- The top is in place: the swap moves it out, and `pos` stays out of place.
    have hpt' : Flat.get p pos ≠ top := fun e => hne (hb.2 pos hpos top ht (e.trans hc.symm))
    have heq : misplaced top (swapP p top pos) = misplaced top p := by
      refine countP_congr fun i hi => ?_
      by_cases e : BitVec.ofNat 64 i = pos
      · rw [e, hg]; simp only [tr, hne, hc, ite_true, ite_false]
        rw [bne_iff_ne.mpr (Ne.symm hne), bne_iff_ne.mpr hpp]
      · rw [hg]; simp [tr, hw i hi, e]
    have ht' : Flat.get (swapP p top pos) top ≠ top := by rw [hg]; simpa [tr] using hpt'
    unfold mu; rw [heq]; simp only [ht', hc, ite_false, ite_true]; omega

-- `misplacedBelow p top c` is `top`, or an offset below `c` that is not in place.
theorem misplacedBelow_spec (p : Vector Word MAX_N) (top c : Word) :
    Flat.misplacedBelow p top c = top
      ∨ (Flat.misplacedBelow p top c < c
        ∧ Flat.get p (Flat.misplacedBelow p top c) ≠ Flat.misplacedBelow p top c) := by
  fun_induction Flat.misplacedBelow p top c with
  | case1 => exact Or.inl rfl
  | case2 c h0 hne => exact Or.inr ⟨by bv_omega, hne⟩
  | case3 c h0 he ih =>
    rcases ih with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨by bv_omega, h2⟩

-- `exchange` swaps the offsets of `pos` and `top`.
theorem exchange_cont {st st' : Flat.St} {top pos : Word} {p p' : Vector Word MAX_N}
    (h : Flat.exchange st top p pos = .cont st' p') : p' = swapP p top pos := by
  unfold Flat.exchange at h
  split at h <;> (try split at h) <;> first | (cases h; rfl) | cases h

-- An iteration of the loop of `permute` that continues keeps `Bij` and makes `mu` smaller.
theorem permuteStep_cont {n : Word} {st st' : Flat.St} {p p' : Vector Word MAX_N}
    (hn : n.toNat ≤ MAX_N) (h0 : 0 < n) (hb : Bij n p)
    (h : Flat.permuteStep st (n - 1) p = .cont st' p') : Bij n p' ∧ mu (n - 1) p' < mu (n - 1) p := by
  have ht : n - 1 < n := by bv_omega
  unfold Flat.permuteStep at h
  dsimp only at h
  split at h
  · next hpt =>
    split at h
    · cases h
    · next hm =>
      rw [exchange_cont h]
      rcases misplacedBelow_spec p (n - 1) (n - 1) with e | ⟨h1, h2⟩
      · exact absurd e hm
      · exact ⟨swapP_bij hn hb ht (by bv_omega),
          swapP_mu hn hb (by bv_omega) hm (Or.inr ⟨hpt, h2⟩)⟩
  · next hpt =>
    rw [exchange_cont h]
    exact ⟨swapP_bij hn hb ht (hb.1 _ ht), swapP_mu hn hb (hb.1 _ ht) hpt (Or.inl rfl)⟩

-- With `mu ≤ fuel`, the loop of `permute` has fuel for one more iteration.
theorem fuel_pos {n : Word} {p : Vector Word MAX_N} {f : Nat} (hb : Bij n p) (h0 : 0 < n)
    (hf : mu (n - 1) p ≤ f) : ∃ f', f = f' + 1 :=
  ⟨f - 1, by have := mu_pos hb h0; omega⟩

-- The fuel of `permute` is sufficient at the start.
theorem mu_start {n : Word} (p : Vector Word MAX_N) (h0 : 0 < n) : mu (n - 1) p ≤ 2 * n.toNat := by
  have := mu_le (n - 1) p
  have : (n - 1).toNat + 1 = n.toNat := by bv_omega
  omega

end Bbu.Unit.Permute
