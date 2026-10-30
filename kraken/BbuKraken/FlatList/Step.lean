import BbuKraken.FlatList.Produce

/-!
An iteration of the loop: `urgentFrom`, `candidateFrom`, `placeTop`, `bound` and `body` of
the flat model against `urgentFrom`, `movableCopy`, `placeTop`, `takeBound` and `step` of
the list model.
-/

namespace Bbu.Flat

section
variable {e : Env} {fs : St} {st : Bbu.St}

/-! ## `urgentFrom` -/

-- The word of `urgentToDup`: the list model uses `n` for none.
def urgW (n k : Nat) : Word := if k < n then BitVec.ofNat 64 k else NONE

-- The flat result `r` of `urgentFrom` holds the list result `m`.
def UrgR (e : Env) : Except (Status × St) Word → M Nat → Prop
  | .ok u, .ok k => k ≤ e.n ∧ u = urgW e.n k
  | .error r, .error err => SimR e r (.error err)
  | _, _ => False

theorem urgW_n (n : Nat) : urgW n n = NONE := by simp [urgW]

theorem urgW_of_lt {n k : Nat} (h : k < n) : urgW n k = BitVec.ofNat 64 k := by simp [urgW, h]

theorem urgW_toNat {n : Nat} {o : Word} (h : o.toNat < n) : urgW n o.toNat = o := by
  rw [urgW_of_lt h]; exact eq_of_toNat (toNat_ofNat_of_lt o.isLt)

theorem urgW_eq_NONE {n k : Nat} (hn : n ≤ MAX_N) (hk : k ≤ n) : urgW n k = NONE ↔ k = n := by
  unfold urgW
  by_cases h : k < n
  · rw [ite_eq_left h]
    have hw : (BitVec.ofNat 64 k).toNat = k := toNat_ofNat_of_lt (by unfold MAX_N at hn; omega)
    refine ⟨fun he => absurd he (lt_NONE (by rw [hw]; omega)), fun he => by omega⟩
  · rw [ite_eq_right h]; exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem sim_urgentFrom (hs : Sim e fs st) (t : Word) (ht : t.toNat < e.n) (o : Word)
    (ho : o.toNat ≤ e.n) (k : Nat) (hk : k ≤ e.n) :
    UrgR e (urgentFrom fs t o (urgW e.n k)) (Bbu.urgentFrom e st t.toNat o.toNat k) := by
  have hn := hs.n
  have hle := hs.n_le
  have hsz := hs.size
  have hl := hs.len_lt
  rw [urgentFrom, Bbu.urgentFrom]
  by_cases h0 : o.toNat < e.n
  · have ho' : o < fs.targetSize := by unfold MAX_N at hle; bv_omega
    have h1 : (o + 1).toNat = o.toNat + 1 := by unfold MAX_N at hle; bv_omega
    rw [dite_eq_left ho', ite_eq_left h0, ← h1]
    by_cases hp : (positionOf st o.toNat).isSome
    · rw [ite_eq_left (c := get fs.pos o ≠ NONE) ((hs.pos_ne_NONE h0).mpr hp), ite_eq_left hp]
      exact sim_urgentFrom hs t ht (o + 1) (by omega) k hk
    rw [ite_eq_right (c := get fs.pos o ≠ NONE) (fun h => hp ((hs.pos_ne_NONE h0).mp h)),
      ite_eq_right hp]
    dsimp only
    rw [hs.target h0, ← hs.isSpilled]
    generalize get fs.target o = slot
    by_cases hj : (isJunk slot || canBeFreelyGenerated slot || Bbu.isSpilled e slot) = true
    · rw [ite_eq_left hj, ite_eq_left hj]
      exact sim_urgentFrom hs t ht (o + 1) (by omega) k hk
    rw [ite_eq_right hj, ite_eq_right hj, sim_copy hs]
    generalize hc : Bbu.shallowestCopyPosition st slot = c
    cases c with
    | none =>
      rw [show optW none = NONE from rfl, ite_eq_right (c := NONE ≠ NONE) (fun h => h rfl)]
      exact sim_urgentFrom hs t ht (o + 1) (by omega) k hk
    | some p =>
      unfold MAX_N at hl hle
      have hp := shallowestCopy_lt hc
      have hw : (BitVec.ofNat 64 p).toNat = p := toNat_ofNat_of_lt (by omega)
      have hnn : BitVec.ofNat 64 p ≠ NONE := lt_NONE (by rw [hw]; unfold MAX_N; omega)
      have hdr : isDupReachable fs (BitVec.ofNat 64 p) = true ↔ st.len - 1 - p ≤ MAX_DUP_DEPTH := by
        unfold isDupReachable depthOf maxDupDepth MAX_DUP_DEPTH
        rw [decide_eq_true_iff]
        constructor <;> intro h <;> bv_omega
      rw [show optW (some p) = BitVec.ofNat 64 p from rfl,
        ite_eq_left (c := BitVec.ofNat 64 p ≠ NONE) hnn]
      dsimp only
      by_cases hr : MAX_DUP_DEPTH < st.len - 1 - p
      · rw [ite_eq_left (c := (!isDupReachable fs (BitVec.ofNat 64 p)) = true)
          (by rw [Bool.not_eq_true', Bool.eq_false_iff]; exact fun h => absurd (hdr.mp h) (by omega)),
          ite_eq_left hr]
        have := sim_blockDup hs (c := BitVec.ofNat 64 p) (by rw [hw]; exact hp) (by rw [hw]; exact hr)
        rw [hw] at this
        exact this
      rw [ite_eq_right (c := (!isDupReachable fs (BitVec.ofNat 64 p)) = true)
          (fun h => by rw [hdr.mpr (by omega)] at h; exact absurd h (by decide)),
        ite_eq_right hr]
      have hcond : (depthOf fs (BitVec.ofNat 64 p) = maxDupDepth ∧ BitVec.ofNat 64 p ≠ t ∧
          urgW e.n k = NONE) ↔ (st.len - 1 - p = MAX_DUP_DEPTH ∧ p ≠ t.toNat ∧ k = e.n) := by
        rw [urgW_eq_NONE (by unfold MAX_N; omega) hk]
        unfold depthOf maxDupDepth MAX_DUP_DEPTH
        constructor
        · rintro ⟨a, b, c⟩
          exact ⟨by bv_omega, fun h => b (eq_of_toNat (by rw [hw]; exact h)), c⟩
        · rintro ⟨a, b, c⟩
          exact ⟨by bv_omega, fun h => b (by rw [← hw, h]), c⟩
      have hu : (if depthOf fs (BitVec.ofNat 64 p) = maxDupDepth ∧ BitVec.ofNat 64 p ≠ t ∧
          urgW e.n k = NONE then o else urgW e.n k) =
          urgW e.n (if st.len - 1 - p = MAX_DUP_DEPTH ∧ p ≠ t.toNat ∧ k = e.n then o.toNat
            else k) := by
        by_cases h : st.len - 1 - p = MAX_DUP_DEPTH ∧ p ≠ t.toNat ∧ k = e.n
        · rw [ite_eq_left (hcond.mpr h), ite_eq_left h, urgW_toNat h0]
        · rw [ite_eq_right (fun h' => h (hcond.mp h')), ite_eq_right h]
      rw [hu]
      exact sim_urgentFrom hs t ht (o + 1) (by omega) _ (by split <;> omega)
  · rw [dite_eq_right (fun h => h0 (by bv_omega)), ite_eq_right h0]
    exact ⟨hk, rfl⟩
termination_by e.n - o.toNat
decreasing_by all_goals omega

/-! ## `candidateFrom` -/

theorem candidate_eq (hs : Sim e fs st) {b : Word} (hb : b.toNat < st.len) :
    ∀ k, b.toNat + k < st.len →
      candidateFrom fs (st.val b.toNat) b (BitVec.ofNat 64 (b.toNat + k)) =
        BitVec.ofNat 64 ((((List.range (b.toNat + k + 1)).reverse.take k).find?
          (fun c => st.val c == st.val b.toNat && st.dest c != c)).getD b.toNat) := by
  have hl := hs.len_lt
  unfold MAX_N at hl
  intro k
  induction k with
  | zero =>
    intro _
    rw [candidateFrom, dite_eq_right (fun h => by bv_omega)]
    simp
  | succ k ih =>
    intro hk
    have hc : (BitVec.ofNat 64 (b.toNat + (k + 1))).toNat = b.toNat + k + 1 :=
      toNat_ofNat_of_lt (by omega)
    rw [candidateFrom, dite_eq_left (show BitVec.ofNat 64 (b.toNat + (k + 1)) > b by bv_omega),
      hs.data _ (by rw [hc]; omega), hc]
    rw [show b.toNat + (k + 1) + 1 = (b.toNat + k + 1) + 1 by omega, List.range_succ,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.take_succ_cons]
    have hcl : b.toNat + k + 1 < st.len := by omega
    by_cases hP : st.val (b.toNat + k + 1) = st.val b.toNat ∧
        st.dest (b.toNat + k + 1) ≠ b.toNat + k + 1
    · rw [ite_eq_left (c := st.val (b.toNat + k + 1) = st.val b.toNat ∧
          (!isFinal fs (BitVec.ofNat 64 (b.toNat + (k + 1)))) = true)
          ⟨hP.1, by
            rw [Bool.not_eq_true', Bool.eq_false_iff]
            exact fun h => hP.2 (by rw [← hc]; exact (isFinal_iff hs (by rw [hc]; exact hcl)).mp h)⟩,
        List.find?_cons_of_pos (by simp [hP.1, hP.2])]
      rfl
    · rw [ite_eq_right (c := st.val (b.toNat + k + 1) = st.val b.toNat ∧
          (!isFinal fs (BitVec.ofNat 64 (b.toNat + (k + 1)))) = true)
          (fun h => hP ⟨h.1, by
            have h2 := h.2
            rw [Bool.not_eq_true', Bool.eq_false_iff] at h2
            exact fun h' => h2 ((isFinal_iff hs (by rw [hc]; exact hcl)).mpr (by rw [hc]; exact h'))⟩),
        List.find?_cons_of_neg (by simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]; exact hP),
        show BitVec.ofNat 64 (b.toNat + (k + 1)) - 1 = BitVec.ofNat 64 (b.toNat + k) by
          apply eq_of_toNat; rw [toNat_ofNat_of_lt (by omega)]; bv_omega]
      exact ih (by omega)

theorem movable_eq (hs : Sim e fs st) {b : Nat} (hb : b < st.len) :
    candidateFrom fs (st.val b) (BitVec.ofNat 64 b) (fs.size - 1) =
      BitVec.ofNat 64 ((movableCopy st b).getD b) := by
  have hl := hs.len_lt
  have hsz := hs.size
  unfold MAX_N at hl
  have hbw : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_of_lt (by omega)
  have := candidate_eq hs (b := BitVec.ofNat 64 b) (by rw [hbw]; exact hb) (st.len - 1 - b)
    (by rw [hbw]; omega)
  rw [hbw, show b + (st.len - 1 - b) = st.len - 1 by omega,
    show st.len - 1 + 1 = st.len by omega] at this
  rw [show fs.size - 1 = BitVec.ofNat 64 (st.len - 1) by
    apply eq_of_toNat; rw [toNat_ofNat_of_lt (by omega)]; bv_omega, this]
  rfl

/-! ## The end of an iteration -/

-- The flat end `x` of an iteration holds the list end `m`.
def NR (e : Env) : Next → M (Bbu.St × Bbu.Next) → Prop
  | .cont fs t', .ok (st, .next k) => t' + 1 = BitVec.ofNat 64 k ∧ Sim e fs st
  | .ret r, .ok (st, .finish) => ∃ fs, Sim e fs st ∧
      (fs.size ≠ fs.targetSize → r = (.assertionFailed, fs)) ∧
      (fs.size = fs.targetSize → r = permute fs)
  | .ret r, .error err => SimR e r (.error err)
  | _, _ => False

theorem NR.bind {r : Status × St} {m : M Bbu.St} {g : St → Next}
    {f : Bbu.St → M (Bbu.St × Bbu.Next)} (h : SimR e r m)
    (hg : ∀ fs st, Sim e fs st → m = .ok st → NR e (g fs) (f st)) :
    NR e (if r.1 ≠ .done then .ret r else g r.2) (m.bind f) := by
  match m, h with
  | .ok st, ⟨h1, h2⟩ =>
    rw [ite_eq_right (c := r.1 ≠ .done) (fun h => h h1)]
    exact hg _ _ h2 rfl
  | .error (.blocked p x s), ⟨h1, h2⟩ =>
    rw [ite_eq_left (c := r.1 ≠ .done) (by rw [h1]; decide)]
    exact ⟨h1, h2⟩
  | .error .assertion, h1 =>
    rw [ite_eq_left (c := r.1 ≠ .done) (by rw [h1]; decide)]
    exact h1

theorem NR.map {r : Status × St} {m : M Bbu.St} {t' : Word} {k : Nat} (h : SimR e r m)
    (hk : t' + 1 = BitVec.ofNat 64 k) :
    NR e (if r.1 ≠ .done then .ret r else .cont r.2 t') (m.map (·, .next k)) := by
  match m, h with
  | .ok st, ⟨h1, h2⟩ =>
    rw [ite_eq_right (c := r.1 ≠ .done) (fun h => h h1)]
    exact ⟨hk, h2⟩
  | .error (.blocked p x s), ⟨h1, h2⟩ =>
    rw [ite_eq_left (c := r.1 ≠ .done) (by rw [h1]; decide)]
    exact ⟨h1, h2⟩
  | .error .assertion, h1 =>
    rw [ite_eq_left (c := r.1 ≠ .done) (by rw [h1]; decide)]
    exact h1

theorem succ_eq {t : Word} {n : Nat} (hn : n ≤ MAX_N) (ht : t.toNat < n) :
    t + 1 = BitVec.ofNat 64 (t.toNat + 1) := by
  unfold MAX_N at hn
  apply eq_of_toNat; rw [toNat_ofNat_of_lt (by omega)]; bv_omega

theorem sim_placeTop (hs : Sim e fs st) {t : Word} (ht : t.toNat < e.n) :
    NR e (placeTop fs t) (Bbu.placeTop st t.toNat) := by
  have hsz := hs.size
  have hl := hs.len_lt
  have hle : e.n ≤ MAX_N := hs.n ▸ hs.n_le
  have h1 := succ_eq hle ht
  have hn := hs.n
  unfold MAX_N at hl hle
  unfold placeTop Bbu.placeTop
  by_cases h2 : st.len ≤ t.toNat
  · rw [ite_eq_left (c := ¬t < fs.size) (by bv_omega),
      ite_eq_left (c := st.len ≤ t.toNat ∨ st.dest t.toNat = t.toNat) (.inl h2)]
    exact rfl
  have htl : t.toNat < st.len := by omega
  rw [ite_eq_right (c := ¬t < fs.size) (fun h => h (by bv_omega))]
  by_cases h3 : st.dest t.toNat = t.toNat
  · rw [ite_eq_left (c := isFinal fs t = true) ((isFinal_iff hs htl).mpr h3),
      ite_eq_left (c := st.len ≤ t.toNat ∨ st.dest t.toNat = t.toNat) (.inr h3)]
    exact rfl
  rw [ite_eq_right (c := isFinal fs t = true) (fun h => h3 ((isFinal_iff hs htl).mp h)),
    ite_eq_right (c := st.len ≤ t.toNat ∨ st.dest t.toNat = t.toNat) (fun h => h.elim h2 h3)]
  by_cases h4 : t.toNat = st.len - 1
  · rw [ite_eq_right (c := t ≠ fs.size - 1) (fun h => h (eq_of_toNat (by bv_omega))),
      ite_eq_right (c := t.toNat ≠ st.len - 1) (fun h => h h4)]
    exact ⟨h1, hs⟩
  rw [ite_eq_left (c := t ≠ fs.size - 1) (fun h => h4 (by rw [h]; bv_omega)),
    ite_eq_left (c := t.toNat ≠ st.len - 1) h4]
  dsimp only
  have hr : isSwapReachable fs t = true ↔ st.len - 1 - t.toNat ≤ MAX_SWAP_DEPTH := by
    unfold isSwapReachable depthOf maxSwapDepth MAX_SWAP_DEPTH
    rw [decide_eq_true_iff]
    constructor <;> intro h <;> bv_omega
  by_cases h5 : MAX_SWAP_DEPTH < st.len - 1 - t.toNat
  · rw [ite_eq_left (c := (!isSwapReachable fs t) = true)
        (by rw [Bool.not_eq_true', Bool.eq_false_iff]; exact fun h => absurd (hr.mp h) (by omega)),
      ite_eq_left h5]
    exact sim_blockSwap hs htl h5
  · rw [ite_eq_right (c := (!isSwapReachable fs t) = true)
        (fun h => by rw [hr.mpr (by omega)] at h; exact absurd h (by decide)),
      ite_eq_right h5]
    exact NR.map (sim_swapWith hs t) h1

end

end Bbu.Flat
