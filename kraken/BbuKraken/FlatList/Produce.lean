import BbuKraken.FlatList.Leaf

/-!
`produce` and `generate` of the flat model against `Bbu.produce` and `Bbu.generate`.
`emitF` is the first part of `produce`, which `Bbu.emit` models.
-/

namespace Bbu.Flat

/-! ## The parts of `produce` and `generate` -/

-- The action of `produce`.
def emitF (fs : St) (t : Word) : Status × St :=
  let slot := get fs.target t
  let copy := shallowestCopyPosition fs slot
  if isJunk slot then push fs slot t
  else if copy ≠ NONE ∧ isDupReachable fs copy then dup fs copy t
  else if canBeFreelyGenerated slot || isSpilled fs slot then push fs slot t
  else if copy ≠ NONE then blockDupUnreachable fs copy
  else (.assertionFailed, fs)

-- The end of `produce`, after a done action.
def produceTail (t : Word) (fs : St) : Status × St :=
  if get fs.pos t ≠ fs.size - 1 then (.assertionFailed, fs)
  else (.done, { fs with pend := fs.pend - 1 })

theorem produce_eq (fs : St) (t : Word) :
    produce fs t =
      if (emitF fs t).1 ≠ .done then emitF fs t else produceTail t (emitF fs t).2 := rfl

-- The end of `generate`, after a done `produce`.
def genTail (t : Word) (fs : St) : Status × St :=
  if t + 1 < fs.size ∧ ¬isFinal fs t then
    if get fs.data t = get fs.data (fs.size - 1) then
      (.done, swapDestinations fs t (fs.size - 1))
    else if isSwapReachable fs t then swapWith fs t
    else (.done, fs)
  else (.done, fs)

theorem generate_eq (fs : St) (t : Word) :
    generate fs t =
      if ¬t < fs.targetSize then (.assertionFailed, fs)
      else if (produce fs t).1 ≠ .done then produce fs t else genTail t (produce fs t).2 := rfl

/-! ## Results -/

section
variable {e : Env} {fs : St} {st : Bbu.St}

-- A flat result that is not done ends the unit, as an error ends a bind of the list model.
theorem SimR.bind {r : Status × St} {m : M Bbu.St} {g : St → Status × St}
    {f : Bbu.St → M Bbu.St} (h : SimR e r m)
    (hg : ∀ fs st, Sim e fs st → m = .ok st → SimR e (g fs) (f st)) :
    SimR e (if r.1 ≠ .done then r else g r.2) (m.bind f) := by
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

theorem sim_block (hs : Sim e fs st) (p w : Word) (hw : w ≠ 0) :
    SimR e (block fs p w) (.error (.blocked p.toNat w.toNat st)) := by
  unfold block
  rw [ite_eq_right hw]
  exact ⟨rfl, hs.trace, hs.slots, by simp, by simp⟩

theorem sim_blockDup (hs : Sim e fs st) {c : Word} (hc : c.toNat < st.len)
    (hx : MAX_DUP_DEPTH < st.len - 1 - c.toNat) :
    SimR e (blockDupUnreachable fs c)
      (.error (.blocked c.toNat (st.len - 1 - c.toNat - MAX_DUP_DEPTH) st)) := by
  have hsz := hs.size
  have hl := hs.len_lt
  unfold MAX_N at hl
  unfold MAX_DUP_DEPTH at hx ⊢
  have hw : (depthOf fs c - maxDupDepth).toNat = st.len - 1 - c.toNat - 15 := by
    unfold depthOf maxDupDepth; bv_omega
  have hw0 : depthOf fs c - maxDupDepth ≠ 0 := by
    unfold depthOf maxDupDepth; bv_omega
  unfold blockDupUnreachable
  rw [← hw]
  exact sim_block hs _ _ hw0

theorem sim_blockSwap (hs : Sim e fs st) {c : Word} (hc : c.toNat < st.len)
    (hx : MAX_SWAP_DEPTH < st.len - 1 - c.toNat) :
    SimR e (blockSwapUnreachable fs c)
      (.error (.blocked c.toNat (st.len - 1 - c.toNat - MAX_SWAP_DEPTH) st)) := by
  have hsz := hs.size
  have hl := hs.len_lt
  unfold MAX_N at hl
  unfold MAX_SWAP_DEPTH at hx ⊢
  have hw : (depthOf fs c - maxSwapDepth).toNat = st.len - 1 - c.toNat - 16 := by
    unfold depthOf maxSwapDepth; bv_omega
  have hw0 : depthOf fs c - maxSwapDepth ≠ 0 := by
    unfold depthOf maxSwapDepth; bv_omega
  unfold blockSwapUnreachable
  rw [← hw]
  exact sim_block hs _ _ hw0

/-! ## `produce` -/

theorem find_val {slot : StackSlot} {p : Nat}
    (h : Bbu.shallowestCopyPosition st slot = some p) : st.val p = slot := by
  have := List.find?_some h
  simpa using this

theorem sim_emit (hs : Sim e fs st) {t : Word} (ht : t.toNat < e.n) (hlt : st.len < e.n) :
    SimR e (emitF fs t) (emit e st t.toNat) := by
  have hsz := hs.size
  have hl := hs.len_lt
  unfold MAX_N at hl
  unfold emitF emit
  dsimp only
  rw [hs.target ht, sim_copy hs, ← hs.isSpilled]
  generalize get fs.target t = slot
  generalize hc : Bbu.shallowestCopyPosition st slot = c
  by_cases hj : isJunk slot = true
  · rw [ite_eq_left hj, ite_eq_left hj]
    exact sim_push hs ht hlt
  rw [ite_eq_right hj, ite_eq_right hj]
  cases c with
  | none =>
    rw [show optW none = NONE from rfl]
    simp only [Option.filter_none]
    rw [ite_eq_right (c := NONE ≠ NONE ∧ _) (fun h => h.1 rfl)]
    by_cases hf : (canBeFreelyGenerated slot || Bbu.isSpilled e slot) = true
    · rw [ite_eq_left hf, ite_eq_left hf]
      exact sim_push hs ht hlt
    · rw [ite_eq_right hf, ite_eq_right hf, ite_eq_right (c := NONE ≠ NONE) (fun h => h rfl)]
      exact rfl
  | some p =>
    have hp := shallowestCopy_lt hc
    have hv := find_val hc
    have hw : (BitVec.ofNat 64 p).toNat = p := toNat_ofNat_of_lt (by omega)
    have hn : BitVec.ofNat 64 p ≠ NONE := lt_NONE (by rw [hw]; unfold MAX_N; omega)
    have hdr : isDupReachable fs (BitVec.ofNat 64 p) = true ↔ st.len - 1 - p ≤ MAX_DUP_DEPTH := by
      unfold isDupReachable depthOf maxDupDepth MAX_DUP_DEPTH
      rw [decide_eq_true_iff]
      constructor <;> intro h <;> bv_omega
    rw [show optW (some p) = BitVec.ofNat 64 p from rfl]
    by_cases hr : st.len - 1 - p ≤ MAX_DUP_DEPTH
    · rw [ite_eq_left (c := BitVec.ofNat 64 p ≠ NONE ∧ _) ⟨hn, hdr.mpr hr⟩]
      simp only [Option.filter, hr, decide_true]
      have := sim_dup hs ht hlt (copy := BitVec.ofNat 64 p) (by rw [hw]; exact hp)
      rw [hw, hv] at this
      exact this
    · rw [ite_eq_right (c := BitVec.ofNat 64 p ≠ NONE ∧ _) (fun h => hr (hdr.mp h.2))]
      simp only [Option.filter, hr, decide_false]
      by_cases hf : (canBeFreelyGenerated slot || Bbu.isSpilled e slot) = true
      · rw [ite_eq_left hf, ite_eq_left hf]
        exact sim_push hs ht hlt
      · rw [ite_eq_right hf, ite_eq_right hf, ite_eq_left (c := BitVec.ofNat 64 p ≠ NONE) hn]
        have := sim_blockDup hs (c := BitVec.ofNat 64 p) (by rw [hw]; exact hp)
          (by rw [hw]; omega)
        rw [hw] at this
        exact this

theorem Sim.pendDec (hs : Sim e fs st) :
    Sim e { fs with pend := fs.pend - 1 }
      { st with pendingGenerations := sizeDec st.pendingGenerations } := by
  refine ⟨hs.env, hs.n_le, hs.size, hs.len_le, hs.data, hs.dest, hs.pos, ?_, hs.trace, hs.hpos.congr rfl rfl⟩
  show (fs.pend - 1).toNat = sizeDec st.pendingGenerations
  rw [← hs.pend]
  unfold sizeDec
  split <;> bv_omega

theorem optW_eq_ofNat {x : Option Nat} {k : Nat} (hx : ∀ p, x = some p → p < 2 ^ 64 - 1)
    (hk : k < 2 ^ 64 - 1) : optW x = BitVec.ofNat 64 k ↔ x = some k := by
  cases x with
  | none =>
    simp only [optW, reduceCtorEq, iff_false]
    intro h
    have := congrArg BitVec.toNat h
    rw [toNat_NONE, toNat_ofNat_of_lt (by omega)] at this
    omega
  | some p =>
    have := hx p rfl
    simp only [optW, Option.some.injEq]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rwa [toNat_ofNat_of_lt (by omega), toNat_ofNat_of_lt (by omega)] at this
    · intro h; rw [h]

theorem sim_produceTail (hs : Sim e fs st) {t : Word} (ht : t.toNat < e.n) (h1 : 0 < st.len) :
    SimR e (produceTail t fs)
      (if positionOf st t.toNat ≠ some (st.len - 1) then .error .assertion
       else .ok { st with pendingGenerations := sizeDec st.pendingGenerations }) := by
  have hsz := hs.size
  have hl := hs.len_lt
  unfold MAX_N at hl
  have hT : fs.size - 1 = BitVec.ofNat 64 (st.len - 1) := by
    apply eq_of_toNat; rw [toNat_ofNat_of_lt (by omega)]; bv_omega
  have hq : get fs.pos t = fs.size - 1 ↔ positionOf st t.toNat = some (st.len - 1) := by
    rw [hs.pos t (hs.n ▸ ht), hT]
    exact optW_eq_ofNat (fun p hp => by have := positionOf_some hs.hpos hp; omega) (by omega)
  unfold produceTail
  by_cases h : positionOf st t.toNat = some (st.len - 1)
  · rw [ite_eq_right (c := get fs.pos t ≠ fs.size - 1) (fun h' => h' (hq.mpr h)),
      ite_eq_right (c := positionOf st t.toNat ≠ some (st.len - 1)) (fun h' => h' h)]
    exact ⟨rfl, hs.pendDec⟩
  · rw [ite_eq_left (c := get fs.pos t ≠ fs.size - 1) (fun h' => h (hq.mp h')),
      ite_eq_left (c := positionOf st t.toNat ≠ some (st.len - 1)) h]
    exact rfl

theorem sim_produce (hs : Sim e fs st) {t : Word} (ht : t.toNat < e.n) (hlt : st.len < e.n) :
    SimR e (produce fs t) (Bbu.produce e st t.toNat) := by
  rw [produce_eq]
  refine SimR.bind (sim_emit hs ht hlt) ?_
  intro fs' st' hs' he
  obtain ⟨h1, -, -⟩ := emit_shape he
  exact sim_produceTail hs' ht (by omega)

/-! ## `generate` -/

theorem sim_genTail (hs : Sim e fs st) {t : Word} (ht : t.toNat < e.n) :
    SimR e (genTail t fs)
      (if t.toNat + 1 < st.len ∧ st.dest t.toNat ≠ t.toNat then
        if st.val t.toNat = st.val (st.len - 1) then
          .ok (Bbu.swapDestinations st t.toNat (st.len - 1))
        else if st.len - 1 - t.toNat ≤ MAX_SWAP_DEPTH then Bbu.swapWith st t.toNat
        else .ok st
      else .ok st) := by
  have hsz := hs.size
  have hl := hs.len_lt
  have hn := hs.n
  have hle := hs.n_le
  unfold MAX_N at hl hle
  unfold genTail
  by_cases h1 : ¬t.toNat + 1 < st.len
  · rw [ite_eq_right (c := t + 1 < fs.size ∧ ¬isFinal fs t = true) (fun h => h1 (by have := h.1; bv_omega)),
      ite_eq_right (c := t.toNat + 1 < st.len ∧ st.dest t.toNat ≠ t.toNat) (fun h => h1 h.1)]
    exact ⟨rfl, hs⟩
  have htl : t.toNat < st.len := by omega
  have hc1 : t + 1 < fs.size := by bv_omega
  have hT : (fs.size - 1).toNat = st.len - 1 := by bv_omega
  by_cases h2 : st.dest t.toNat = t.toNat
  · rw [ite_eq_right (c := t + 1 < fs.size ∧ ¬isFinal fs t = true) (fun h => h.2 ((isFinal_iff hs htl).mpr h2)),
      ite_eq_right (c := t.toNat + 1 < st.len ∧ st.dest t.toNat ≠ t.toNat) (fun h => h.2 h2)]
    exact ⟨rfl, hs⟩
  rw [ite_eq_left (c := t + 1 < fs.size ∧ ¬isFinal fs t = true) ⟨hc1, fun h => h2 ((isFinal_iff hs htl).mp h)⟩,
    ite_eq_left (c := t.toNat + 1 < st.len ∧ st.dest t.toNat ≠ t.toNat) ⟨by omega, h2⟩]
  rw [hs.data t htl, hs.data (fs.size - 1) (by rw [hT]; omega), hT]
  by_cases h3 : st.val t.toNat = st.val (st.len - 1)
  · rw [ite_eq_left h3, ite_eq_left h3]
    exact ⟨rfl, hs.swapDest' htl hT (by omega)⟩
  rw [ite_eq_right h3, ite_eq_right h3]
  have hr : isSwapReachable fs t = true ↔ st.len - 1 - t.toNat ≤ MAX_SWAP_DEPTH := by
    unfold isSwapReachable depthOf maxSwapDepth MAX_SWAP_DEPTH
    rw [decide_eq_true_iff]
    constructor <;> intro h <;> bv_omega
  by_cases h4 : st.len - 1 - t.toNat ≤ MAX_SWAP_DEPTH
  · rw [ite_eq_left (hr.mpr h4), ite_eq_left h4]
    exact sim_swapWith hs t
  · rw [ite_eq_right (fun h => h4 (hr.mp h)), ite_eq_right h4]
    exact ⟨rfl, hs⟩

theorem sim_generate (hs : Sim e fs st) (t : Word) (hlt : st.len < e.n) :
    SimR e (generate fs t) (Bbu.generate e st t.toNat) := by
  have hn := hs.n
  rw [generate_eq]
  unfold Bbu.generate
  by_cases h0 : t < fs.targetSize
  · have ht : t.toNat < e.n := by rw [hn]; bv_omega
    rw [ite_eq_right (c := ¬t < fs.targetSize) (fun h => h h0),
      ite_eq_right (c := e.n ≤ t.toNat) (by omega)]
    refine SimR.bind (sim_produce hs ht hlt) ?_
    intro fs' st' hs' _
    exact sim_genTail hs' ht
  · rw [ite_eq_left (c := ¬t < fs.targetSize) h0,
      ite_eq_left (c := e.n ≤ t.toNat) (by rw [hn]; bv_omega)]
    exact rfl

end

end Bbu.Flat
