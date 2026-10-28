import BbuKraken.Fn.ShallowestCopy
import BbuKraken.Kit

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu
namespace TakeBound

/-! ## The model -/

-- `takeBound` after the choice of `pos`.
def tail (st : St) (t b pos : Nat) : M (St × Bool) :=
  let st := swapDest st pos b
  if pos = t then .ok (st, true)
  else if pos ≠ st.len - 1 then
    let depth := st.len - 1 - pos
    if MAX_SWAP_DEPTH < depth then .error (.blocked pos (depth - MAX_SWAP_DEPTH))
    else (swapWith st pos).map (·, false)
  else .ok (st, false)

theorem takeBound_eq (st : St) (t b : Nat) : takeBound st t b =
    if b < t then .error .assertion
    else tail st t b (if st.val t = st.val b then t else (movableCopy st b).getD b) := rfl

-- The test of `movableCopy` on the slot `c`.
def Mv (st : St) (b c : Nat) : Bool := st.val c == st.val b && st.dest c != c

theorem movableCopy_some {st : St} {b c : Nat} (hbc : b < c) (hc : c < st.len) (hp : Mv st b c = true)
    (h : ∀ j, c < j → j < st.len → Mv st b j = false) : movableCopy st b = some c := by
  unfold movableCopy
  simp only [Mv] at hp h
  generalize st.len = n at hc h
  induction n with
  | zero => omega
  | succ n ih =>
    rw [show n + 1 - 1 - b = (n - 1 - b) + 1 by omega]
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.take_succ_cons, List.find?_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [h n hc (by omega)]
      exact ih hc fun j h1 h2 => h j h1 (by omega)
    · rw [hp]

theorem movableCopy_none {st : St} {b : Nat} (h : ∀ j, b < j → j < st.len → Mv st b j = false) :
    movableCopy st b = none := by
  unfold movableCopy
  simp only [Mv] at h
  generalize st.len = n at h
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hb : b < n
    · rw [show n + 1 - 1 - b = (n - 1 - b) + 1 by omega]
      simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.take_succ_cons, List.find?_cons]
      rw [h n hb (by omega)]
      exact ih fun j h1 h2 => h j h1 (by omega)
    · rw [show n + 1 - 1 - b = 0 by omega]
      rfl

theorem movableCopy_lt {st : St} {b c : Nat} (h : movableCopy st b = some c) : c < st.len := by
  unfold movableCopy at h
  exact List.mem_range.mp (List.mem_reverse.mp (List.mem_of_mem_take (List.mem_of_find?_eq_some h)))

theorem swapDest_len (st : St) (a b : Nat) : (swapDest st a b).len = st.len := by
  simp [swapDest, St.len]

theorem swapDest_ops (st : St) (a b : Nat) : (swapDest st a b).ops = st.ops := rfl

-- The four ends of `tail`.
theorem tail_t (st : St) (t b : Nat) : tail st t b t = .ok (swapDest st t b, true) := by
  simp [tail]

theorem tail_top {st : St} {t b pos : Nat} (h1 : pos ≠ t) (h2 : pos = st.len - 1) :
    tail st t b pos = .ok (swapDest st pos b, false) := by
  subst h2
  simp [tail, h1, swapDest_len]

theorem tail_blk {st : St} {t b pos : Nat} (h1 : pos ≠ t) (h2 : 17 < st.len - pos) :
    tail st t b pos = .error (.blocked pos (st.len - pos - 17)) := by
  have h3 : pos ≠ st.len - 1 := by omega
  have h4 : MAX_SWAP_DEPTH < st.len - 1 - pos := by simp only [MAX_SWAP_DEPTH]; omega
  simp only [tail, h1, h3, h4, swapDest_len, ↓reduceIte, ne_eq, not_false_eq_true]
  simp only [MAX_SWAP_DEPTH]
  congr 2
  omega

theorem tail_call {st : St} {t b pos : Nat} (h1 : pos ≠ t) (h2 : pos ≠ st.len - 1)
    (h3 : st.len - pos ≤ 17) :
    tail st t b pos = (swapWith (swapDest st pos b) pos).map (·, false) := by
  have h4 : ¬ MAX_SWAP_DEPTH < st.len - 1 - pos := by simp only [MAX_SWAP_DEPTH]; omega
  simp only [tail, h1, h2, h4, swapDest_len, ↓reduceIte, ne_eq, not_false_eq_true]

theorem ns_test (v : Word) (r) :
    CondCode.ns.interp (StatusFlags.from_result (v &&& v) r) = !v.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

-- `cmpq b, a; ja` jumps iff `b < a`.
theorem a_sub (a b : BitVec 64) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := ((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int), af, of })
      = decide (b.toNat < a.toNat) := by
  simp only [CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result]
  have := a.isLt; have := b.isLt
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_eq_false_iff_ne,
    decide_eq_true_eq, ne_eq]
  rw [BitVec.toNat_sub]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : a ≠ b := fun h => h2 (by rw [h, BitVec.sub_self]; rfl)
    have h4 : a.toNat ≠ b.toNat := fun h => h3 (BitVec.eq_of_toNat_eq h)
    omega
  · intro h
    refine ⟨by omega, fun h2 => ?_⟩
    have := congrArg BitVec.toNat h2
    rw [BitVec.toNat_sub] at this
    simp at this
    omega

theorem dec_eq_iff {L R : BitVec 64} {n p : Nat} (hL : L.toNat = n) (hR : R.toNat = p) (hp : p < n) :
    L + -1#64 = R ↔ p = n - 1 := by
  constructor
  · intro h; subst hL hR; bv_omega
  · intro h; subst hL hR; bv_omega

theorem depth_toNat {L R : BitVec 64} {n p : Nat} (hL : L.toNat = n) (hR : R.toNat = p) (hp : p < n) :
    (L - R + -1#64).toNat = n - p - 1 := by
  subst hL hR; bv_omega

theorem depth_gt {L R : BitVec 64} {n p k : Nat} (hL : L.toNat = n) (hR : R.toNat = p) (hp : p < n)
    (hk : k < 2 ^ 64) (h : (BitVec.ofNat 64 k).toNat < (L - R + -1#64).toNat) : k + 1 < n - p := by
  rw [depth_toNat hL hR hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at h; omega

theorem depth_le {L R : BitVec 64} {n p k : Nat} (hL : L.toNat = n) (hR : R.toNat = p) (hp : p < n)
    (hk : k < 2 ^ 64) (h : ¬ (BitVec.ofNat 64 k).toNat < (L - R + -1#64).toNat) : n - p ≤ k + 1 := by
  rw [depth_toNat hL hR hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at h; omega

theorem sub_ofNat {L R : BitVec 64} {n p : Nat} (hL : L.toNat = n) (hR : R.toNat = p) (hp : p < n) :
    L - R = BitVec.ofNat 64 (n - p) := by
  subst hL hR; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; bv_omega

/-! ## Memory in a function body with frame `F` -/

section
variable {F : Nat} {s : MachineData} {ra : Int64} {A : MachineData → Prop} {m : Mem 64}

-- The memory `m` of a body for the call `s`: the return address, the struct,
-- the frame, and no change outside the blocks that the body may write.
structure Mid (F : Nat) (s : MachineData) (ra : Int64) (m : Mem 64) : Prop where
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  wf : Wf m (rdi s)
  map : Mem.Mapped [frame F s] m
  un : Mem.UnchangedOutside (mod F s).mem s.dmem m

-- The return address lies in the frame.
theorem ra_in_frame (hF : 8 ≤ F) (hpre : Pre F A s) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - 8#64, 8)] → Mem.Blocks.Inside x 1 [frame F s] := by
  have hle := hpre.2.1.le
  intro x hx
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

theorem Mid.init (hF : 8 ≤ F) (hpre : Pre F A s) : Mid F s ra (s.pushRa ra).dmem := by
  have hu : Mem.UnchangedOutside [(rsp s - 8#64, 8)] s.dmem (s.pushRa ra).dmem :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  have hd := disjoint_mono (ra_in_frame hF hpre) hpre.2.1.disj
  refine ⟨?_, Wf.congr_of_disjoint hu hpre.1 (disjoint_symm hd), hpre.2.1.mapped.storeInt _ _ _, ?_⟩
  · exact (rd_store_same _ rfl).trans BitVec.ofInt_toInt
  · intro x hx
    exact hu x fun h => hx (Or.inl (ra_in_frame hF hpre x h |>.elim id False.elim))

-- The struct regions of `m` are those of the call.
theorem Mid.keeps (hpre : Pre F A s) (h : Mid F s ra m) :
    envOf m (rdi s) = env s ∧ readable m (rdi s) = readable s.dmem (rdi s)
      ∧ writable m (rdi s) = writable s.dmem (rdi s) :=
  Post.env (t := { s with dmem := m }) hpre ⟨fun _ _ => rfl, h.un⟩

-- A store of 8 bytes in `writable` that keeps `len` and `nops`.
theorem Mid.store (hF : 8 ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) {a : Addr} {v : Int}
    (ha : Mem.Blocks.Inside a 8 (writable m (rdi s)))
    (h0 : rd (m.storeInt a 8 v) (wordAt (rdi s) 0) = rd m (wordAt (rdi s) 0))
    (h2 : rd (m.storeInt a 8 v) (wordAt (rdi s) 2) = rd m (wordAt (rdi s) 2)) :
    Mid F s ra (m.storeInt a 8 v) := by
  obtain ⟨-, hr, hwr⟩ := h.keeps hpre
  have hu : Mem.UnchangedOutside [(a, 8)] m (m.storeInt a 8 v) :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  -- the bytes of the store lie in `writable`
  have hw : ∀ x, Mem.Blocks.Inside x 1 [(a, 8)] → Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) := by
    intro x hx
    rw [← hwr]
    simp only [Mem.Blocks.Inside, or_false] at hx
    have := Mem.Blocks.Inside.add_ofNat (n := 8) (i := (x - a).toNat) ha (by omega)
    rw [show a + BitVec.ofNat 64 (x - a).toNat = x by bv_omega] at this
    exact this
  refine ⟨?_, ?_, h.map.storeInt _ _ _, ?_⟩
  · rw [rd_congr hu (fun x hx hy => hpre.2.1.disj x (ra_in_frame hF hpre x hx)
      (inside_append.mpr (Or.inl (hw x hy))))]
    exact h.ra
  · refine Wf.congr hu h.wf (fun x hx hy => hpre.disj x (hr ▸ hx) (Or.inr (hw x hy)))
      (fun x hx => (h.wf.mapped.storeInt _ _ _) x (inside_append.mpr (Or.inl hx))) ?_ ?_
    · rw [h0]; exact h.wf.len_le
    · rw [h2]; exact h.wf.nops_le
  · intro x hx
    rw [hu x fun hy => hx (Or.inr (hw x hy))]
    exact h.un x hx

-- A callee with frame size `G` at `rsp s - 8` keeps the memory of the body.
theorem Mid.call {G : Nat} {c t : MachineData} {R : MachineData → MachineData → Prop}
    (hG : 8 + G ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - 8#64) (hrdi : rdi c = rdi s) (hp : Post G R c t)
    (hag : (mod G c).Agree c t) : Mid F s ra t.dmem := by
  have hfr := hpre.2.1
  have hle := hfr.le
  have hwr := (h.keeps hpre).2.2
  have hu : Mem.UnchangedOutside (frame G c :: writable s.dmem (rdi s)) m t.dmem := by
    have := hag.2
    simp only [mod, hc, hrdi, hwr] at this
    exact this
  have hsub : ∀ x, Mem.Blocks.Inside x 1 [frame G c] → Mem.Blocks.Inside x 1 [frame F s] := by
    intro x hx
    simp only [Mem.Blocks.Inside, or_false, hrsp] at hx ⊢
    bv_omega
  have hnw : ∀ x, Mem.Blocks.Inside x 1 [frame F s] → ¬ Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
    fun x hx hw => hfr.disj x hx (inside_append.mpr (Or.inl hw))
  refine ⟨?_, hrdi ▸ hp.1, fun x hx => ?_, fun x hx => ?_⟩
  · rw [rd_congr hu fun x hx hl => ?_]
    · exact h.ra
    · rcases hl with hl | hl
      · simp only [Mem.Blocks.Inside, or_false, hrsp] at hx hl
        bv_omega
      · exact hnw x (ra_in_frame (by omega) hpre x hx) hl
  · by_cases hx8 : Mem.Blocks.Inside x 1 [frame G c]
    · exact hp.2.1 x hx8
    · rw [hu x fun hl => hl.elim (fun hl => hx8 (Or.inl hl)) (hnw x hx)]
      exact h.map x hx
  · rw [hu x fun hl => hl.elim (fun hl => hx (Or.inl ((hsub x (Or.inl hl)).elim id False.elim)))
      (fun hl => hx (Or.inr hl))]
    exact h.un x hx

-- The precondition of a callee with frame size `G` at `rsp s - 8`.
theorem Mid.pre {G : Nat} {c : MachineData} {A' : MachineData → Prop}
    (hG : 8 + G ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - 8#64) (hrdi : rdi c = rdi s) (hA : A' c) : Pre G A' c := by
  obtain ⟨-, hr, hwr⟩ := h.keeps hpre
  refine ⟨by rw [hc, hrdi]; exact h.wf, ?_, hA⟩
  exact FrameOk.sub (k := 8) hpre.2.1 hpre.1 hrdi hrsp hG (hc ▸ h.map) (hc ▸ hr) (hc ▸ hwr)

-- The slot of the return address of a callee at `rsp s - 8` is mapped.
theorem Mid.call_isSome (hF : 16 ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) :
    (m.loadInt (rsp s - 8#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  refine Mem.Mapped.loadInt_isSome h.map (Or.inl ?_)
  bv_omega

theorem Mid.retAddr (hF : 8 ≤ F) (hpre : Pre F A s) {t : MachineData} (h : Mid F s ra t.dmem)
    (hsp : rsp t = rsp s - 8#64) : t.retAddr = some ra := by
  have hle := hpre.2.1.le
  have hs : (t.dmem.loadInt (rsp s - 8#64) 8).isSome = true :=
    Mem.Mapped.loadInt_isSome h.map (Or.inl (by bv_omega))
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  have hra := h.ra
  rw [rd, hv, Option.get!_some] at hra
  rw [MachineData.retAddr, show t.regs.get64 .rsp = rsp s - 8#64 from hsp, hv, Option.map_some, hra,
    Int64.ofBitVec_toBitVec]

-- `ret` from a state with the memory `Mid` and the registers of the call gives
-- the postcondition of `Body`.
theorem Mid.ret [Host] {R : MachineData → MachineData → Prop} {ls : List Label}
    {I' : CfgLabel → Nat → Unit → MachineData → Prop} {t : MachineData} (hF : 8 ≤ F)
    (hpre : Pre F A s) (h : Mid F s ra t.dmem) (hsp : rsp t = rsp s - 8#64)
    (hr : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q)
    (hR : ∀ t', t'.dmem = t.dmem → rax t' = rax t → R s t') :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post F R s t ∧ (mod F s).Agree s t) t.retAddr.get!
      { regs := t.regs.set64 Reg64.rsp (t.regs.get64 Reg64.rsp + 8#64), zmms := t.zmms,
        status := t.status, dmem := t.dmem } := by
  have hra := h.retAddr hF hpre hsp
  replace hsp : t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 := hsp
  refine Or.inr ⟨⟨by simp [hra], ⟨h.wf, h.map, hR _ rfl (by simp)⟩, fun q hq => ?_, h.un⟩,
    fun _ _ _ => ?_⟩
  · simp only [Reg64s.get64_set64]
    split
    · subst_vars; rw [hsp]; bv_omega
    · exact hr q (by simp_all [mod])
  · apply MachineData.stackBelow_of_add_eight
    simp [MachineData.pushRa, hsp]
    bv_omega

end

/-! ## Stores to the struct -/

section
variable {m : Mem 64} {S : Addr}

-- A store to the dest word of slot `i` keeps the other words of the struct.
theorem rd_store_dest_other (hw : Wf m S) {i k : Nat} (hi : i < 256) (hk : k < WORDS)
    (hne : k ≠ DEST + i) (v : Int) :
    rd (m.storeInt (wordAt S (DEST + i)) 8 v) (wordAt S k) = rd m (wordAt S k) :=
  rd_storeInt_of_disjoint (disjoint_wordAt (Ne.symm hne) (by simp only [DEST, WORDS]; omega) hk
    hw.struct_lt)

-- A store to the dest word of slot `i` keeps the ops buffer.
theorem rd_store_dest_ops (hw : Wf m S) {i j : Nat} (hi : i < 256) (hj : j < 12 * nOf m S) (v : Int) :
    rd (m.storeInt (wordAt S (DEST + i)) 8 v) (wordAt (opsOf m S) j) = rd m (wordAt (opsOf m S) j) := by
  have hs := hw.struct_lt
  have ho := hw.ops_lt
  refine rd_storeInt_of_disjoint fun x hx hy => hw.disj_struct x ?_ (Or.inl ?_)
  · simp only [Mem.Blocks.Inside, or_false, DEST, WORDS] at hx hs ⊢
    bv_omega
  · simp only [Mem.Blocks.Inside, or_false] at hy ⊢
    bv_omega

theorem stOf_store_dest (hw : Wf m S) {i : Nat} (hi : i < (rd m (wordAt S 0)).toNat) (v : Word) :
    stOf (m.storeInt (wordAt S (DEST + i)) 8 v.toInt) S =
      { stOf m S with slots := (stOf m S).slots.set i ⟨(stOf m S).val i, v.toNat⟩ } := by
  have hlen := hw.len_le
  have hi' : i < 256 := by omega
  have hk : ∀ {k}, k < WORDS → k ≠ DEST + i →
      rd (m.storeInt (wordAt S (DEST + i)) 8 v.toInt) (wordAt S k) = rd m (wordAt S k) :=
    fun hk hne => rd_store_dest_other hw hi' hk hne _
  have ho : opsOf (m.storeInt (wordAt S (DEST + i)) 8 v.toInt) S = opsOf m S :=
    hk (k := 6) (by decide) (by simp only [DEST]; omega)
  have hnops := hw.nops_le
  rw [stOf_val_rd hi]
  simp only [stOf, hk (k := 0) (by decide) (by simp only [DEST]; omega),
    hk (k := 1) (by decide) (by simp only [DEST]; omega),
    hk (k := 2) (by decide) (by simp only [DEST]; omega)]
  congr 1
  · refine List.ext_getElem (by simp) fun j h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_set]
    simp only [List.getElem_map, List.getElem_range, slotOf]
    split
    · subst_vars
      rw [hk (by simp only [STACK, WORDS]; omega) (by simp only [STACK, DEST]; omega),
        rd_store_same _ rfl, BitVec.ofInt_toInt]
    · rw [hk (by simp only [STACK, WORDS]; omega) (by simp only [STACK, DEST]; omega),
        hk (by simp only [DEST, WORDS]; omega) (by omega)]
  · refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    simp only [opOf, ho, rd_store_dest_ops hw hi' (j := 2 * j) (by omega),
      rd_store_dest_ops hw hi' (j := 2 * j + 1) (by omega)]

end

section
variable {F : Nat} {s : MachineData} {ra : Int64} {A : MachineData → Prop} {m : Mem 64}

theorem Mid.store_dest (hF : 8 ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) {i : Nat} (hi : i < 256)
    (v : Int) : Mid F s ra (m.storeInt (wordAt (rdi s) (DEST + i)) 8 v) :=
  h.store hF hpre (inside_arr (by simp only [STACK, DEST]; omega) (by simp only [DEST, WORDS]; omega))
    (rd_store_dest_other h.wf hi (by decide) (by simp only [DEST]; omega) v)
    (rd_store_dest_other h.wf hi (by decide) (by simp only [DEST]; omega) v)

theorem val_set_self (st : St) (a b x : Nat) :
    ({ st with slots := st.slots.set a ⟨st.val a, x⟩ } : St).val b = st.val b := by
  simp only [St.val, List.getElem?_set]
  by_cases hb : b < st.slots.length <;> split <;> simp_all [Nat.not_lt.mpr]

-- The two stores of the dest words of `a` and `b` give `swapDest`.
theorem Mid.swap (hF : 8 ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) {a b : Nat}
    (ha : a < (stOf m (rdi s)).len) (hb : b < (stOf m (rdi s)).len) {va vb : Word}
    (hva : va.toNat = (stOf m (rdi s)).dest a) (hvb : vb.toNat = (stOf m (rdi s)).dest b) :
    Mid F s ra ((m.storeInt (wordAt (rdi s) (DEST + a)) 8 vb.toInt).storeInt
        (wordAt (rdi s) (DEST + b)) 8 va.toInt)
      ∧ stOf ((m.storeInt (wordAt (rdi s) (DEST + a)) 8 vb.toInt).storeInt
        (wordAt (rdi s) (DEST + b)) 8 va.toInt) (rdi s) = swapDest (stOf m (rdi s)) a b := by
  have hl := h.wf.len_le
  rw [stOf_len_rd] at ha hb
  have h1 := h.store_dest hF hpre (i := a) (by omega) vb.toInt
  have e1 := stOf_store_dest h.wf ha vb
  have hb1 : b < (rd (m.storeInt (wordAt (rdi s) (DEST + a)) 8 vb.toInt) (wordAt (rdi s) 0)).toNat := by
    rw [rd_store_dest_other h.wf (by omega) (by decide) (by simp only [DEST]; omega)]
    exact hb
  refine ⟨h1.store_dest hF hpre (by omega) _, ?_⟩
  rw [stOf_store_dest h1.wf hb1 va, e1]
  simp only [swapDest, val_set_self, hva, hvb]

-- The words of `blocked` do not overlap the struct.
theorem blk_disj {S : Addr} (hw : Wf m S) {j k : Nat} (hj : j < 2) (hk : k < WORDS) :
    Mem.Blocks.Disjoint [(wordAt (blkOf m S) j, 8)] [(wordAt S k, 8)] := by
  have hs := hw.struct_lt
  have hb := hw.blk_lt
  intro x hx hy
  refine hw.disj_struct x ?_ (Or.inr (Or.inl ?_))
  · simp only [Mem.Blocks.Inside, or_false, WORDS] at hy hs hk ⊢
    bv_omega
  · simp only [Mem.Blocks.Inside, or_false] at hx ⊢
    bv_omega

theorem rd_store_blk_struct {S : Addr} (hw : Wf m S) {j k : Nat} (hj : j < 2) (hk : k < WORDS)
    (v : Int) : rd (m.storeInt (wordAt (blkOf m S) j) 8 v) (wordAt S k) = rd m (wordAt S k) :=
  rd_storeInt_of_disjoint (blk_disj hw hj hk)

theorem Mid.store_blk (hF : 8 ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) {j : Nat} (hj : j < 2)
    (v : Int) : Mid F s ra (m.storeInt (wordAt (blkOf m (rdi s)) j) 8 v) := by
  have hb := h.wf.blk_lt
  refine h.store hF hpre (inside_of_mem (p := (blkOf m (rdi s), 16)) (by simp [writable]) (Or.inl ?_))
    (rd_store_blk_struct h.wf hj (by decide) v) (rd_store_blk_struct h.wf hj (by decide) v)
  simp only [wordAt]
  bv_omega

end

/-! ## Invariants -/

section
variable (s : MachineData) (ra : Int64)

abbrev m0 : Mem 64 := (s.pushRa ra).dmem
abbrev tN : Nat := (rsi s).toNat
abbrev bN : Nat := (rdx s).toNat

-- The registers of the scan and of `.LB69`.
structure Rg (t : MachineData) : Prop where
  keep : Keep s ra t
  di : rdi t = rdi s
  cx : rcx t = rsi s
  r8 : r8 t = rdi s + rdx s * 8#64
  le : tN s ≤ bN s

-- `.LB71` (`k = 1`) and `.LB70` (`k = 0`): the scan for a copy at `c` in `rax`.
def Scan (k : Nat) (t : MachineData) : Prop :=
  Rg s ra t ∧ (st s).val (tN s) ≠ (st s).val (bN s) ∧ rsi t = rdx s
    ∧ rdx t = rd (m0 s ra) (wordAt (rdi s) (STACK + bN s))
    ∧ ∃ c, rax t = BitVec.ofNat 64 c ∧ bN s < c ∧ c < (st s).len
      ∧ ∀ j, c + k ≤ j → j < (st s).len → Mv (st s) (bN s) j = false

-- `.LB69`: the slot `pos` in `rsi` takes the dest of `b`.
def At69 (t : MachineData) : Prop :=
  Rg s ra t ∧ (st s).val (tN s) ≠ (st s).val (bN s)
    ∧ rsi t = BitVec.ofNat 64 ((movableCopy (st s) (bN s)).getD (bN s))

-- `.LB68`: the slot `t` holds the value of `b`.
def At68 (t : MachineData) : Prop :=
  Rg s ra t ∧ (st s).val (tN s) = (st s).val (bN s) ∧ rax t = rdi s + rsi s * 8#64

-- The state after a change of memory: the memory and the registers of the call.
structure Out (t : MachineData) : Prop where
  mid : Mid 16 s ra t.dmem
  sp : rsp t = rsp s - 8#64
  bx : t.regs.rbx = s.regs.rbx
  bp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

def At75 (t : MachineData) : Prop :=
  Out s ra t ∧ takeBound (st s) (tN s) (bN s) = .ok (stOf t.dmem (rdi s), true)

def At78 (t : MachineData) : Prop :=
  Out s ra t ∧ rdi t = rdi s ∧ ∃ pos, rsi t = BitVec.ofNat 64 pos ∧ pos < (st s).len
    ∧ rdx t = BitVec.ofNat 64 ((st s).len - pos) ∧ 17 < (st s).len - pos
    ∧ takeBound (st s) (tN s) (bN s) = .error (.blocked pos ((st s).len - pos - 17))

def V : Label → MachineData → Nat
  | "take_bound", _ => 2 ^ 66
  | ".LB71", t => 2 * (rax t).toNat + 2
  | ".LB70", t => 2 * (rax t).toNat + 1
  | _, _ => 0

end

-- Use these on big states: a direct `rfl` makes the kernel compare the two states.
theorem V_69 (t : MachineData) : V ".LB69" t = 0 := rfl
theorem V_78 (t : MachineData) : V ".LB78" t = 0 := rfl

theorem v_step {l l' : Label} {t t' : MachineData} {i j : Nat} (h : V l' t' = 0) (h2 : V l t = 0)
    (hij : i < j) : V l' t' < V l t ∨ V l' t' = V l t ∧ i < j :=
  Or.inr ⟨h.trans h2.symm, hij⟩

/-! ## Facts at the entry -/

-- `cmpq b, a` sets no carry iff `b ≤ a`.
theorem sub_toNat_int (a b : BitVec 64) :
    ((a - b).toNat : Int) = (a.toNat : Int) - (b.toNat : Int) ↔ b.toNat ≤ a.toNat := by
  rw [BitVec.toNat_sub]; omega

theorem sub_one_toNat {L : BitVec 64} {n : Nat} (h : L.toNat = n) (h1 : 1 ≤ n) :
    (L - 1#64).toNat = n - 1 := by
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

theorem v_lt (x : BitVec 64) : 2 * x.toNat + 2 < 2 ^ 66 := by
  have := x.isLt; omega

/-- `omega` with the registers of the call in the form of `bbu_norm`. -/
macro "tb_omega" : tactic => `(tactic| ((try simp only [st, rdi, bN, tN, rdx, rsi, rax,
  Reg64s.get64_rdi, Reg64s.get64_rdx, Reg64s.get64_rsi, Reg64s.get64_rax] at *); omega))

theorem stOf_dest_rd {m : Mem 64} {S : Addr} {j : Nat} (hj : j < (rd m (wordAt S 0)).toNat) :
    (stOf m S).dest j = (rd m (wordAt S (DEST + j))).toNat := by
  simp [St.dest, stOf, hj, slotOf]

section
variable {s : MachineData} {ra : Int64}

theorem st_m0 (hpre : Pre 16 takeBoundA s) : stOf (m0 s ra) (rdi s) = st s := by
  have hu : Mem.UnchangedOutside [(rsp s - 8#64, 8)] s.dmem (s.pushRa ra).dmem :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  exact stOf_congr hu hpre.1
    (disjoint_symm (disjoint_mono (ra_in_frame (by decide) hpre) hpre.2.1.disj))

theorem len_m0 (hpre : Pre 16 takeBoundA s) : (rd (m0 s ra) (rdi s)).toNat = (st s).len := by
  rw [← st_m0 (ra := ra) hpre, stOf_len_rd]; simp [wordAt]

theorem addr_stack (S x : BitVec 64) : S + x * 8#64 + 64#64 = wordAt S (STACK + x.toNat) := by
  simp only [wordAt, STACK]; bv_omega

theorem addr_dest (S x : BitVec 64) : S + x * 8#64 + 2112#64 = wordAt S (DEST + x.toNat) := by
  simp only [wordAt, DEST]; bv_omega

theorem val_m0 (hpre : Pre 16 takeBoundA s) {x : BitVec 64} (hx : x.toNat < (st s).len) :
    rd (m0 s ra) (rdi s + x * 8#64 + 64#64) = (st s).val x.toNat := by
  rw [← st_m0 (ra := ra) hpre] at hx ⊢
  rw [addr_stack, stOf_val_rd (by rwa [stOf_len_rd] at hx)]

theorem dest_m0 (hpre : Pre 16 takeBoundA s) {x : BitVec 64} (hx : x.toNat < (st s).len) :
    (rd (m0 s ra) (rdi s + x * 8#64 + 2112#64)).toNat = (st s).dest x.toNat := by
  rw [← st_m0 (ra := ra) hpre] at hx ⊢
  rw [addr_dest, stOf_dest_rd (by rwa [stOf_len_rd] at hx)]

-- The forms of the words at entry after `bbu_norm`.
theorem len_m0' (hpre : Pre 16 takeBoundA s) :
    (rd (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt)
      s.regs.rdi.toBitVec).toNat = (st s).len := len_m0 hpre

theorem val_m0' (hpre : Pre 16 takeBoundA s) {x : BitVec 64} (hx : x.toNat < (st s).len) :
    rd (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt)
      (s.regs.rdi.toBitVec + x * 8#64 + 64#64) = (st s).val x.toNat := val_m0 hpre hx

theorem dest_m0' (hpre : Pre 16 takeBoundA s) {x : BitVec 64} (hx : x.toNat < (st s).len) :
    (rd (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt)
      (s.regs.rdi.toBitVec + x * 8#64 + 2112#64)).toNat = (st s).dest x.toNat := dest_m0 hpre hx

theorem len_isSome (hpre : Pre 16 takeBoundA s) :
    ((Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).loadInt
      s.regs.rdi.toBitVec 8).isSome = true := by
  have := (Mid.init (ra := ra) (by decide) hpre).wf.load_writable (inside_hdr0 (k := 0) (by decide))
  rwa [show wordAt (rdi s) 0 = s.regs.rdi.toBitVec by simp [wordAt]] at this

theorem arr_isSome (hpre : Pre 16 takeBoundA s) {x : BitVec 64} (k : BitVec 64)
    (hk : k = 64#64 ∨ k = 2112#64) (hx : x.toNat < (st s).len) :
    ((m0 s ra).loadInt (rdi s + x * 8#64 + k) 8).isSome = true := by
  have hw := (Mid.init (ra := ra) (by decide) hpre).wf
  have hl : (rd (m0 s ra) (wordAt (rdi s) 0)).toNat ≤ 256 := hw.len_le
  rw [← st_m0 (ra := ra) hpre, stOf_len_rd] at hx
  rcases hk with rfl | rfl
  · rw [addr_stack]
    exact hw.load_writable (inside_arr (by simp only [STACK]; omega) (by simp only [STACK, WORDS]; omega))
  · rw [addr_dest]
    exact hw.load_writable (inside_arr (by simp only [STACK, DEST]; omega) (by simp only [DEST, WORDS]; omega))

theorem len_lt : (st s).len < 2 ^ 64 := by
  rw [stOf_len_rd]; exact BitVec.isLt _

theorem val_m0_word (hpre : Pre 16 takeBoundA s) {x : Nat} (hx : x < (st s).len) :
    rd (m0 s ra) (wordAt (rdi s) (STACK + x)) = (st s).val x := by
  rw [← st_m0 (ra := ra) hpre] at hx ⊢
  rw [stOf_val_rd (by rwa [stOf_len_rd] at hx)]

-- The words of slot `c` in a state of the scan.
theorem scan_val (hpre : Pre 16 takeBoundA s) {t : MachineData} {c : Nat} (hk : Keep s ra t)
    (hdi : rdi t = rdi s) (hax : rax t = BitVec.ofNat 64 c) (hc : c < (st s).len) :
    rd t.dmem (rdi t + rax t * 8#64 + 64#64) = (st s).val c := by
  have hc' : (BitVec.ofNat 64 c).toNat < (st s).len := by
    rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hc
  rw [hk.mem, hdi, hax]
  have := val_m0 (ra := ra) hpre hc'
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hc len_lt)] at this

theorem scan_dest (hpre : Pre 16 takeBoundA s) {t : MachineData} {c : Nat} (hk : Keep s ra t)
    (hdi : rdi t = rdi s) (hax : rax t = BitVec.ofNat 64 c) (hc : c < (st s).len) :
    (rd t.dmem (rdi t + rax t * 8#64 + 2112#64)).toNat = (st s).dest c := by
  have hc' : (BitVec.ofNat 64 c).toNat < (st s).len := by
    rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hc
  rw [hk.mem, hdi, hax]
  have := dest_m0 (ra := ra) hpre hc'
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hc len_lt)] at this

theorem scan_isSome (hpre : Pre 16 takeBoundA s) {t : MachineData} {c : Nat} (hk : Keep s ra t)
    (hdi : rdi t = rdi s) (hax : rax t = BitVec.ofNat 64 c) (hc : c < (st s).len) (k : BitVec 64)
    (hkk : k = 64#64 ∨ k = 2112#64) :
    (t.dmem.loadInt (rdi t + rax t * 8#64 + k) 8).isSome = true := by
  have hc' : (BitVec.ofNat 64 c).toNat < (st s).len := by
    rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hc
  rw [hk.mem, hdi, hax]
  exact arr_isSome hpre k hkk hc'

/-! ## The exits -/

theorem Out.regs {t : MachineData} (h : Out s ra t) :
    ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q := by
  obtain ⟨-, -, hbx, hbp, h12, h13, h14, h15⟩ := h
  intro q hq
  cases q <;> simp_all

theorem Out.next {t t' : MachineData} (h : Out s ra t) (hm : Mid 16 s ra t'.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbx : t'.regs.rbx = t.regs.rbx)
    (hbp : t'.regs.rbp = t.regs.rbp) (h12 : t'.regs.r12 = t.regs.r12)
    (h13 : t'.regs.r13 = t.regs.r13) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) : Out s ra t' :=
  ⟨hm, by show t'.regs.get64 .rsp = _; rw [Reg64s.get64_rsp, hsp]; exact h.sp, hbx.trans h.bx,
    hbp.trans h.bp, h12.trans h.r12, h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

/-! Lemmas for a state literal. On a big kvcgen state, `rfl : t'.regs.rbx = t.regs.rbx` makes the
kernel compare `t'` with `t` field by field. Here the fields are variables, so it does not. -/

theorem Out.next_mk {t : MachineData}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Out s ra t) (hm : Mid 16 s ra d) (h6 : a6 = t.regs.rsp) (h1 : a1 = t.regs.rbx)
    (h7 : a7 = t.regs.rbp) (h12 : a12 = t.regs.r12) (h13 : a13 = t.regs.r13)
    (h14 : a14 = t.regs.r14) (h15 : a15 = t.regs.r15) :
    Out s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  h.next hm h6 h1 h7 h12 h13 h14 h15

theorem stack_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : a6 = (s.pushRa ra).regs.rsp) :
    (MachineData.mk ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
      z f d).StackAtOrBelow (s.pushRa ra) :=
  stack_pushRa h

theorem rdi_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d} :
    rdi ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      = a5.toBitVec := rfl

theorem rsi_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d} :
    rsi ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      = a4.toBitVec := rfl

theorem rsp_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d} :
    rsp ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      = a6.toBitVec := rfl

theorem Keep.out (hpre : Pre 16 takeBoundA s) {t : MachineData} (h : Keep s ra t) : Out s ra t :=
  ⟨h.mem ▸ Mid.init (by decide) hpre, by show t.regs.get64 .rsp = _; rw [Reg64s.get64_rsp, h.sp]; rfl,
    h.bx, h.bp, h.r12, h.r13, h.r14, h.r15⟩

-- `takeBoundR` reads only the memory and `rax`.
theorem R_congr {t t' : MachineData} (h : takeBoundR s t) (hm : t'.dmem = t.dmem)
    (hax : rax t' = rax t) : takeBoundR s t' := by
  unfold takeBoundR Res Ok st' at *
  rw [hm, hax]
  exact h

theorem res_ok {t : MachineData} {st1 : St} {b : Bool}
    (hres : takeBound (st s) (tN s) (bN s) = .ok (st1, b))
    (hax : rax t = if b then 0#64 else 1#64) (hst : stOf t.dmem (rdi s) = st1) :
    takeBoundR s t := by
  unfold takeBoundR
  rw [hres]
  exact ⟨hax, hst⟩

theorem Out.isSome (hpre : Pre 16 takeBoundA s) {t : MachineData} (h : Out s ra t) :
    t.retAddr.isSome = true := by
  rw [Mid.retAddr (by decide) hpre h.mid h.sp]; rfl

theorem Out.ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    {t : MachineData} (hpre : Pre 16 takeBoundA s) (h : Out s ra t) (hR : takeBoundR s t) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post 16 takeBoundR s t ∧ (mod 16 s).Agree s t) t.retAddr.get!
      { regs := t.regs.set64 Reg64.rsp (t.regs.get64 Reg64.rsp + 8#64), zmms := t.zmms,
        status := t.status, dmem := t.dmem } :=
  Mid.ret (by decide) hpre h.mid h.sp h.regs fun _ hm hax => R_congr hR hm hax

-- The state after a call from `c`, with the registers of `t`.
theorem Out.call {G : Nat} {t c t' : MachineData} (h : Out s ra t) (hm : Mid 16 s ra t'.dmem)
    (hag : (mod G c).Agree c t') (hsp : c.regs.rsp = t.regs.rsp) (hbx : c.regs.rbx = t.regs.rbx)
    (hbp : c.regs.rbp = t.regs.rbp) (h12 : c.regs.r12 = t.regs.r12)
    (h13 : c.regs.r13 = t.regs.r13) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) : Out s ra t' := by
  have e : ∀ q, q ∉ (mod G c).regs → t'.regs.get64 q = c.regs.get64 q := hag.1
  exact h.next hm (by rw [← hsp]; exact UInt64.eq_of_toBitVec_eq (e .rsp (by simp [mod])))
    (by rw [← hbx]; exact UInt64.eq_of_toBitVec_eq (e .rbx (by simp [mod])))
    (by rw [← hbp]; exact UInt64.eq_of_toBitVec_eq (e .rbp (by simp [mod])))
    (by rw [← h12]; exact UInt64.eq_of_toBitVec_eq (e .r12 (by simp [mod])))
    (by rw [← h13]; exact UInt64.eq_of_toBitVec_eq (e .r13 (by simp [mod])))
    (by rw [← h14]; exact UInt64.eq_of_toBitVec_eq (e .r14 (by simp [mod])))
    (by rw [← h15]; exact UInt64.eq_of_toBitVec_eq (e .r15 (by simp [mod])))

-- `Out.call` for a state literal `c`. See `Out.next_mk`.
theorem Out.call_mk {G : Nat} {t t' : MachineData}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Out s ra t) (hm : Mid 16 s ra t'.dmem)
    (hag : (mod G ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩).Agree
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ t')
    (h6 : a6 = t.regs.rsp) (h1 : a1 = t.regs.rbx) (h7 : a7 = t.regs.rbp) (h12 : a12 = t.regs.r12)
    (h13 : a13 = t.regs.r13) (h14 : a14 = t.regs.r14) (h15 : a15 = t.regs.r15) : Out s ra t' :=
  h.call hm hag h6 h1 h7 h12 h13 h14 h15

theorem Mid.nOf {F : Nat} {A : MachineData → Prop} {m : Mem 64} (hpre : Pre F A s)
    (h : Mid F s ra m) : nOf m (rdi s) = nOf s.dmem (rdi s) := by
  have := congrArg (fun e => e.target.length) (h.keeps hpre).1
  simpa [envOf, env] using this

-- `takeBoundR` after the call of `swap_with` from `c` and `cmovns`.
theorem call_res {c c' t' : MachineData} {pos : Nat} {st1 : St}
    {r : StatusFlags.from_result.Remaining}
    (hres : takeBound (st s) (tN s) (bN s) = (swapWith st1 pos).map (·, false))
    (hc : stOf c.dmem (rdi s) = st1) (hdi : rdi c = rdi s) (hp : (rsi c).toNat = pos)
    (hR : swapWithR c c') (hm : t'.dmem = c'.dmem)
    (hax : rax t' = if CondCode.ns.interp (StatusFlags.from_result (rax c' &&& rax c') r) = true
      then 1#64 else rax c') : takeBoundR s t' := by
  unfold swapWithR st at hR
  rw [hdi, hc, hp] at hR
  rw [ns_test] at hax
  refine (?_ : Res (rdi s) (takeBound (st s) (tN s) (bN s)) _ _)
  rw [hres]
  cases h : swapWith st1 pos with
  | ok st2 =>
    rw [h] at hR
    obtain ⟨h0, h2⟩ := hR
    refine ⟨?_, ?_⟩
    · rw [hax, h0]; simp
    · show stOf t'.dmem (rdi s) = st2
      rw [hm, ← hdi]; exact h2
  | error e =>
    rw [h] at hR
    cases e with
    | blocked p x =>
      obtain ⟨h0, h1, h2⟩ := hR
      refine ⟨?_, ?_, ?_⟩
      · rw [hax, h0]; decide
      · rw [hm]; exact h1
      · rw [hm]; exact h2
    | assertion =>
      show rax t' = -2#64
      rw [hax, hR]; decide

end
end TakeBound

open TakeBound in
theorem takeBound_body [Host] [FunDecls] (hswap : Spec "swap_with" swapWithF swapWithA swapWithR) :
    Body takeBoundAsm takeBoundF takeBoundA takeBoundR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 16 takeBoundA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "take_bound", t => t = s.pushRa ra
      | .label ".LB71", t => Scan s ra 1 t
      | .label ".LB70", t => Scan s ra 0 t
      | .label ".LB69", t => At69 s ra t
      | .label ".LB78", t => At78 s ra t
      | .label ".LB73", t => Keep s ra t ∧ bN s < tN s
      | .label ".LB75", t => At75 s ra t
      | .label ".LB68", t => At68 s ra t
      | .label ".LB66", t => Out s ra t ∧ takeBoundR s t
      | _, _ => False)
    V ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.left t ht =>
    subst ht
    kvcgen64
    all_goals bbu_norm at *
    all_goals have hb : s.regs.rdx.toBitVec.toNat < (st s).len := hpre.2.2.1
    case vc1 hc _ =>
      bbu_flags at hc
      rw [sub_toNat_int] at hc
      cfg_goto
      · exact stack_pushRa rfl
      · exact ⟨Keep.init.next rfl rfl rfl rfl rfl rfl rfl rfl, by omega⟩
      · simp [V]
    case vc2 hc _ =>
      bbu_flags at hc
      rw [sub_toNat_int] at hc
      exact arr_isSome (ra := ra) hpre _ (Or.inl rfl) hb
    case vc3 hc _ =>
      bbu_flags at hc
      rw [sub_toNat_int] at hc
      exact arr_isSome (ra := ra) hpre _ (Or.inl rfl) (by omega)
    case vc4 hc _ hz =>
      have heq := beq_iff_eq.mp ((z_sub _ _ _ _ _).symm.trans hz)
      bbu_flags at hc
      rw [sub_toNat_int] at hc
      rw [val_m0' hpre (by omega), val_m0' hpre hb] at heq
      cfg_goto
      · exact stack_pushRa rfl
      · exact ⟨⟨Keep.init.next rfl rfl rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl, hc⟩, heq, rfl⟩
      · simp [V]
    case vc5 => exact len_isSome hpre
    case vc6 hc _ hz hc2 =>
      have hne := beq_eq_false_iff_ne.mp ((z_sub _ _ _ _ _).symm.trans hz)
      bbu_flags at hc hc2
      rw [sub_toNat_int] at hc
      rw [val_m0' hpre (by omega), val_m0' hpre hb] at hne
      have hl := len_m0' (ra := ra) hpre
      have h1 := sub_one_toNat hl (by omega)
      rw [sub_toNat_int, h1] at hc2
      have hlt : (st s).len - 1 < 2 ^ 64 := by rw [← h1]; exact BitVec.isLt _
      cfg_goto
      · exact stack_pushRa rfl
      · refine ⟨⟨Keep.init.next rfl rfl rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl, hc⟩, hne, rfl,
          congrArg (rd (m0 s ra)) (addr_stack _ _), (st s).len - 1,
          BitVec.eq_of_toNat_eq (h1.trans (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt])),
          by tb_omega, by tb_omega, fun j hj1 hj2 => by tb_omega⟩
      · simp only [V]; exact Or.inl (v_lt _)
    case vc7 hc _ hz hc2 =>
      have hne := beq_eq_false_iff_ne.mp ((z_sub _ _ _ _ _).symm.trans hz)
      bbu_flags at hc hc2
      rw [sub_toNat_int] at hc
      rw [val_m0' hpre (by omega), val_m0' hpre hb] at hne
      have hl := len_m0' (ra := ra) hpre
      have h1 := sub_one_toNat hl (by omega)
      rw [sub_toNat_int, h1] at hc2
      cfg_goto
      · exact stack_pushRa rfl
      · refine ⟨⟨Keep.init.next rfl rfl rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl, hc⟩, hne, ?_⟩
        rw [movableCopy_none fun j h1 h2 => by tb_omega]
        simp
      · simp [V]
  case right.right.left t ht =>
    obtain ⟨⟨hk, hdi, hcx, hr8, hle⟩, hne, hsi, hdx, c, hax, hbc, hcl, hmv⟩ := ht
    have hc64 : c < 2 ^ 64 := Nat.lt_trans hcl len_lt
    have hc1 : (BitVec.ofNat 64 c - 1#64).toNat = c - 1 :=
      sub_one_toNat (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64]) (by omega)
    kvcgen64
    all_goals bbu_norm at *
    case vc1 hc _ =>
      bbu_flags at hc
      rw [sub_toNat_int, hax, hc1, hsi] at hc
      cfg_goto
      · exact stack_pushRa hk.sp
      · refine ⟨⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hdi, hcx, hr8, hle⟩, hne, ?_⟩
        have hmc : movableCopy (st s) (bN s) = none :=
          movableCopy_none fun j h1 h2 => hmv j (by tb_omega) h2
        rw [hmc]
        show t.regs.rsi.toBitVec = _
        rw [hsi]; simp
      · simp [V]
    case vc2 hc _ =>
      bbu_flags at hc
      rw [sub_toNat_int, hax, hc1, hsi] at hc
      refine ⟨⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hdi, hcx, hr8, hle⟩, hne, hsi, hdx, c - 1,
        ?_, by tb_omega, by tb_omega, fun j h1 h2 => hmv j (by tb_omega) h2⟩
      show t.regs.rax.toBitVec - 1#64 = _
      rw [hax]
      exact BitVec.eq_of_toNat_eq (hc1.trans (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
    case vc3 hc _ =>
      bbu_flags at hc
      rw [sub_toNat_int, hax, hc1, hsi] at hc
      simp only [V]
      left
      show 2 * (t.regs.rax.toBitVec - 1#64).toNat + 2 < 2 * t.regs.rax.toBitVec.toNat + 1
      rw [hax, hc1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64]
      omega
  case right.right.right.left t ht =>
    obtain ⟨⟨hk, hdi, hcx, hr8, hle⟩, hne, hsi, hdx, c, hax, hbc, hcl, hmv⟩ := ht
    have hv := scan_val hpre hk hdi hax hcl
    have hd := scan_dest hpre hk hdi hax hcl
    have hs1 := scan_isSome hpre hk hdi hax hcl _ (Or.inl rfl)
    have hs2 := scan_isSome hpre hk hdi hax hcl _ (Or.inr rfl)
    have hdx' : rdx t = (st s).val (bN s) := hdx.trans (val_m0_word hpre hpre.2.2.1)
    have hc64 : c < 2 ^ 64 := Nat.lt_trans hcl len_lt
    have hax' : (rax t).toNat = c := by rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64]
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact hs1
    case vc2 hz _ =>
      have h := (nz_sub _ _ _ _ _).symm.trans hz
      rw [hv, hdx'] at h
      have hneq : (st s).val c ≠ (st s).val (bN s) := fun h' => (bne_iff_ne.mp h) h'.symm
      cfg_goto
      · exact stack_pushRa hk.sp
      · refine ⟨⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hdi, hcx, hr8, hle⟩, hne, hsi, hdx, c, hax,
          hbc, hcl, fun j h1 h2 => ?_⟩
        by_cases hj : j = c
        · subst hj; simp [Mv, hneq]
        · exact hmv j (by tb_omega) h2
      · simp [V]
    case vc3 => exact hs2
    case vc4 hz hz2 _ =>
      have h := (nz_sub _ _ _ _ _).symm.trans hz
      rw [hv, hdx'] at h
      have hd2 := congrArg BitVec.toNat (beq_iff_eq.mp ((z_sub _ _ _ _ _).symm.trans hz2))
      rw [hd, hax'] at hd2
      cfg_goto
      · exact stack_pushRa hk.sp
      · refine ⟨⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hdi, hcx, hr8, hle⟩, hne, hsi, hdx, c, hax,
          hbc, hcl, fun j h1 h2 => ?_⟩
        by_cases hj : j = c
        · subst hj; simp [Mv]; exact fun _ => hd2
        · exact hmv j (by tb_omega) h2
      · simp [V]
    case vc5 hz hz2 _ =>
      have h := (nz_sub _ _ _ _ _).symm.trans hz
      rw [hv, hdx'] at h
      have hd2 := beq_eq_false_iff_ne.mp ((z_sub _ _ _ _ _).symm.trans hz2)
      have hdc : (st s).dest c ≠ c := fun h' => hd2 (BitVec.eq_of_toNat_eq (by rw [hd, hax']; exact h'))
      have hmc : movableCopy (st s) (bN s) = some c :=
        movableCopy_some hbc hcl (by simp at h; simp [Mv, hdc]; exact h.symm) fun j h1 h2 => hmv j (by tb_omega) h2
      refine ⟨⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hdi, hcx, hr8, hle⟩, hne, ?_⟩
      rw [hmc]
      exact hax
    case vc6 => simp [V]
  case right.right.right.right.left t ht =>
    obtain ⟨⟨hk, hdi, hcx, hr8, hle⟩, hne, hsi⟩ := ht
    have hpl : (movableCopy (st s) (bN s)).getD (bN s) < (st s).len := by
      cases h : movableCopy (st s) (bN s) with
      | none => exact hpre.2.2.1
      | some c => exact movableCopy_lt h
    have hres0 : takeBound (st s) (tN s) (bN s)
        = tail (st s) (tN s) (bN s) ((movableCopy (st s) (bN s)).getD (bN s)) := by
      rw [takeBound_eq]; simp only [show ¬ bN s < tN s by omega, hne, ↓reduceIte]
    generalize (movableCopy (st s) (bN s)).getD (bN s) = pos at hsi hpl hres0
    have ho := Keep.out (ra := ra) hpre hk
    have hb : bN s < (st s).len := hpre.2.2.1
    have hst : stOf t.dmem (rdi s) = st s := by rw [hk.mem]; exact st_m0 hpre
    have hp64 : pos < 2 ^ 64 := Nat.lt_trans hpl len_lt
    have hpN : (rsi t).toNat = pos := by rw [hsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp64]
    have haP : rdi t + (rsi t + 264#64) * 8#64 = wordAt (rdi s) (DEST + pos) := by
      rw [hdi, ← hpN]; simp only [wordAt, DEST]; bv_omega
    have haB : r8 t + 2112#64 = wordAt (rdi s) (DEST + bN s) := by rw [hr8, addr_dest]
    have hsP : (t.dmem.loadInt (rdi t + (rsi t + 264#64) * 8#64) 8).isSome = true := by
      rw [haP, hk.mem]
      have := arr_isSome (ra := ra) hpre (x := rsi t) _ (Or.inr rfl) (by rw [hpN]; exact hpl)
      rwa [addr_dest, hpN] at this
    have hsB : (t.dmem.loadInt (r8 t + 2112#64) 8).isSome = true := by
      rw [hk.mem, hr8]; exact arr_isSome hpre _ (Or.inr rfl) hb
    have hlen : (st s).len = (rd t.dmem (wordAt (rdi s) 0)).toNat := by rw [← hst, stOf_len_rd]
    have hsw := Mid.swap (by decide) hpre ho.mid (a := pos) (b := bN s) (by rw [hst]; exact hpl)
      (by rw [hst]; exact hb) (va := rd t.dmem (rdi t + (rsi t + 264#64) * 8#64))
      (vb := rd t.dmem (r8 t + 2112#64))
      (by rw [haP, stOf_dest_rd (by omega)]) (by rw [haB, stOf_dest_rd (by omega)])
    rw [← haP, ← haB, hst] at hsw
    have hL : ∀ m, stOf m (rdi s) = swapDest (st s) pos (bN s) → (rd m (rdi t)).toNat = (st s).len := by
      intro m hm
      have h := congrArg St.len hm
      rw [stOf_len_rd, swapDest_len, show wordAt (rdi s) 0 = rdi t by rw [hdi]; simp [wordAt]] at h
      exact h
    have hpt : rsi t = rcx t → pos = tN s := by
      intro h; have := congrArg BitVec.toNat h; rw [hpN, hcx] at this; exact this
    have hnt : ¬ rsi t = rcx t → pos ≠ tN s :=
      fun h hp => h (BitVec.eq_of_toNat_eq (by rw [hpN, hcx]; exact hp))
    have h75 : pos = tN s → takeBound (st s) (tN s) (bN s) = .ok (swapDest (st s) pos (bN s), true) := by
      intro hp; rw [hres0, hp, tail_t]
    have h66 : pos ≠ tN s → pos = (st s).len - 1 →
        takeBound (st s) (tN s) (bN s) = .ok (swapDest (st s) pos (bN s), false) :=
      fun h1 h2 => by rw [hres0, tail_top h1 h2]
    have h78 : pos ≠ tN s → 17 < (st s).len - pos →
        takeBound (st s) (tN s) (bN s) = .error (.blocked pos ((st s).len - pos - 17)) :=
      fun h1 h2 => by rw [hres0, tail_blk h1 h2]
    have hcl : pos ≠ tN s → pos ≠ (st s).len - 1 → (st s).len - pos ≤ 17 →
        takeBound (st s) (tN s) (bN s) = (swapWith (swapDest (st s) pos (bN s)) pos).map (·, false) :=
      fun h1 h2 h3 => by rw [hres0, tail_call h1 h2 h3]
    have hAw : ∀ c : MachineData, Mid 16 s ra c.dmem → rdi c = rdi s →
        stOf c.dmem (rdi s) = swapDest (st s) pos (bN s) → swapWithA c := by
      intro c hm hd hs
      unfold swapWithA st cap
      rw [hd, hs, swapDest_ops, hm.nOf hpre]
      exact hpre.2.2.2
    have hsp : rsp t = rsp s - 8#64 := ho.sp
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact hsP
    case vc2 => exact hsB
    case vc3 => exact hsP
    case vc4 => exact loadInt_isSome_store _ hsB
    case vc5 hz1 _ =>
      have hp := hpt (beq_iff_eq.mp ((z_sub _ _ _ _ _).symm.trans hz1))
      cfg_goto
      · exact stack_pushRa hk.sp
      · exact ⟨ho.next hsw.1 rfl rfl rfl rfl rfl rfl rfl,
          (h75 hp).trans (congrArg (fun x => Except.ok (x, true)) hsw.2.symm)⟩
      · simp [V]
    case vc6 =>
      have h := hsw.1.wf.load_writable (inside_hdr0 (k := 0) (by decide))
      rw [show wordAt (rdi s) 0 = t.regs.rdi.toBitVec by rw [hdi]; simp [wordAt]] at h
      exact h
    case vc7 hz1 _ hz2 =>
      have hnp := hnt (beq_eq_false_iff_ne.mp ((z_sub _ _ _ _ _).symm.trans hz1))
      have hp := (dec_eq_iff (hL _ hsw.2) hpN hpl).1 (beq_iff_eq.mp ((z_sub _ _ _ _ _).symm.trans hz2))
      cfg_goto
      · exact stack_pushRa hk.sp
      · exact ⟨ho.next hsw.1 rfl rfl rfl rfl rfl rfl rfl, res_ok (h66 hnp hp) rfl hsw.2⟩
      · exact Or.inr ⟨rfl, by decide⟩
    case vc8 hz1 _ _ ha =>
      have hnp := hnt (beq_eq_false_iff_ne.mp ((z_sub _ _ _ _ _).symm.trans hz1))
      have hl2 := hL _ hsw.2
      have h17 : 17 < (st s).len - pos :=
        depth_gt hl2 hpN hpl (by decide) (of_decide_eq_true ((a_sub _ _ _ _).symm.trans ha))
      cfg_goto
      · exact stack_mk hk.sp
      · exact ⟨ho.next_mk hsw.1 rfl rfl rfl rfl rfl rfl rfl, rdi_mk.trans hdi, pos,
          rsi_mk.trans hsi, hpl, sub_ofNat hl2 hpN hpl, h17, h78 hnp h17⟩
      · exact v_step (V_78 _) (V_69 _) (by decide)
    case vc9 =>
      rw [hsp]
      exact hsw.1.call_isSome (by decide) hpre
    case vc10 =>
      exact Mid.pre (by decide) hpre hsw.1 (by rfl) (by exact rsp_mk.trans hsp) (by exact rdi_mk.trans hdi)
        (hAw _ hsw.1 (by exact rdi_mk.trans hdi) hsw.2)
    case vc11 hz1 _ _ _ hz2 ha hpost hag =>
      have hM := Mid.call (by decide) hpre hsw.1 (by rfl) (by exact rsp_mk.trans hsp)
        (by exact rdi_mk.trans hdi) hpost hag
      have hO := ho.call_mk hM hag rfl rfl rfl rfl rfl rfl rfl
      exact Out.isSome hpre (hO.next_mk hO.mid rfl rfl rfl rfl rfl rfl rfl)
    case vc12 hz1 _ _ _ hz2 ha hpost hag =>
      have hnp := hnt (beq_eq_false_iff_ne.mp ((z_sub _ _ _ _ _).symm.trans hz1))
      have hl2 := hL _ hsw.2
      have he := beq_eq_false_iff_ne.mp ((z_sub _ _ _ _ _).symm.trans hz2)
      have hp1 : pos ≠ (st s).len - 1 := fun h => he ((dec_eq_iff hl2 hpN hpl).2 h)
      have h17 : (st s).len - pos ≤ 17 :=
        depth_le hl2 hpN hpl (by decide) (of_decide_eq_false ((a_sub _ _ _ _).symm.trans ha))
      have hM := Mid.call (by decide) hpre hsw.1 (by rfl) (by exact rsp_mk.trans hsp)
        (by exact rdi_mk.trans hdi) hpost hag
      have hO := ho.call_mk hM hag rfl rfl rfl rfl rfl rfl rfl
      exact Out.ret hpre (hO.next_mk hO.mid rfl rfl rfl rfl rfl rfl rfl)
        (call_res (hcl hnp hp1 h17) (by exact hsw.2) (by exact rdi_mk.trans hdi)
          (by rw [rsi_mk]; exact hpN) hpost.2.2 rfl rfl)
  case right.right.right.right.right.left t ht =>
    obtain ⟨ho, hdi, pos, hsi, hpl, hdx, h17, hres⟩ := ht
    have hw := ho.mid.wf
    have hb7 : rdi t + 56#64 = wordAt (rdi s) 7 := by rw [hdi]
    have hB0 : rd t.dmem (rdi t + 56#64) = blkOf t.dmem (rdi s) := by rw [hb7]; rfl
    have hs7 : (t.dmem.loadInt (rdi t + 56#64) 8).isSome = true := by
      rw [hb7]; exact hw.isSome_struct (by simp only [wordAt, WORDS]; bv_omega)
    have hsB : (t.dmem.loadInt (blkOf t.dmem (rdi s)) 8).isSome = true :=
      hw.load_writable (inside_writable (Or.inr (Or.inr (Or.inr (by simp)))))
    have e0 : wordAt (blkOf t.dmem (rdi s)) 0 = blkOf t.dmem (rdi s) := by simp [wordAt]
    have e1 : wordAt (blkOf t.dmem (rdi s)) 1 = blkOf t.dmem (rdi s) + 8#64 := rfl
    have hm1 := ho.mid.store_blk (by decide) hpre (j := 0) (by decide) (rsi t).toInt
    rw [e0] at hm1
    have hk1 : blkOf (t.dmem.storeInt (blkOf t.dmem (rdi s)) 8 (rsi t).toInt) (rdi s)
        = blkOf t.dmem (rdi s) := by
      have := rd_store_blk_struct hw (j := 0) (k := 7) (by decide) (by decide) (rsi t).toInt
      rw [e0] at this; exact this
    have hB1 : rd (t.dmem.storeInt (blkOf t.dmem (rdi s)) 8 (rsi t).toInt) (rdi t + 56#64)
        = blkOf t.dmem (rdi s) := by rw [hb7]; exact hk1
    have hs8 : ((t.dmem.storeInt (blkOf t.dmem (rdi s)) 8 (rsi t).toInt).loadInt
        (blkOf t.dmem (rdi s) + 8#64) 8).isSome = true := by
      refine hm1.wf.load_writable (inside_writable (Or.inr (Or.inr (Or.inr ?_))))
      rw [hk1]; bv_omega
    have hm2 := hm1.store_blk (by decide) hpre (j := 1) (by decide) (rdx t - 17#64).toInt
    have hk2 := rd_store_blk_struct hm1.wf (j := 1) (k := 7) (by decide) (by decide) (rdx t - 17#64).toInt
    rw [hk1, e1] at hm2 hk2
    have hR : ∀ t' : MachineData, t'.dmem = ((t.dmem.storeInt (blkOf t.dmem (rdi s)) 8
        (rsi t).toInt).storeInt (blkOf t.dmem (rdi s) + 8#64) 8 (rdx t - 17#64).toInt) →
        rax t' = -1#64 → takeBoundR s t' := by
      intro t' hm hax
      have hk2' : blkOf t'.dmem (rdi s) = blkOf t.dmem (rdi s) := by rw [hm]; exact hk2.trans hk1
      unfold takeBoundR
      rw [hres]
      refine ⟨hax, ?_, ?_⟩
      · rw [hk2', hm]
        rw [rd_store_other _ (by bv_omega), rd_store_same _ rfl, BitVec.ofInt_toInt]
        exact hsi
      · rw [hk2', e1, hm]
        rw [rd_store_same _ rfl, BitVec.ofInt_toInt]
        rw [hdx]
        have := @len_lt s
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
    kvcgen64
    all_goals bbu_norm at *
    all_goals try simp only [hB0, hB1]
    case vc1 => exact hs7
    case vc2 => exact hsB
    case vc3 => exact loadInt_isSome_store _ hs7
    case vc4 => exact hs8
    case vc5 => exact Out.isSome hpre (ho.next hm2 rfl rfl rfl rfl rfl rfl rfl)
    case vc6 => exact Out.ret hpre (ho.next hm2 rfl rfl rfl rfl rfl rfl rfl) (hR _ rfl rfl)
  case right.right.right.right.right.right.left t ht =>
    obtain ⟨hk, hlt⟩ := ht
    have ho := Keep.out (ra := ra) hpre hk
    kvcgen64
    case vc1 => exact Out.isSome hpre (ho.next ho.mid rfl rfl rfl rfl rfl rfl rfl)
    case vc2 =>
      refine Out.ret hpre (ho.next ho.mid rfl rfl rfl rfl rfl rfl rfl) ?_
      simp only [takeBoundR, takeBound_eq, hlt, ↓reduceIte, Res]
      rfl
  case right.right.right.right.right.right.right.left t ht =>
    obtain ⟨ho, hr⟩ := ht
    kvcgen64
    case vc1 => exact Out.isSome hpre (ho.next ho.mid rfl rfl rfl rfl rfl rfl rfl)
    case vc2 =>
      refine Out.ret hpre (ho.next ho.mid rfl rfl rfl rfl rfl rfl rfl) ?_
      simp only [takeBoundR, hr, Res]
      exact ⟨rfl, rfl⟩
  case right.right.right.right.right.right.right.right.right t ht =>
    obtain ⟨ho, hr⟩ := ht
    kvcgen64
    case vc1 => exact Out.isSome hpre ho
    case vc2 => exact Out.ret hpre ho hr
  case right.right.right.right.right.right.right.right.left t ht =>
    obtain ⟨⟨hk, hdi, hcx, hr8, hle⟩, heq, hax⟩ := ht
    have ho := Keep.out (ra := ra) hpre hk
    have hb : bN s < (st s).len := hpre.2.2.1
    have hT : tN s < (st s).len := by omega
    have hst : stOf t.dmem (rdi s) = st s := by rw [hk.mem]; exact st_m0 hpre
    have hlen : (st s).len = (rd t.dmem (wordAt (rdi s) 0)).toNat := by rw [← hst, stOf_len_rd]
    have haT : rax t + 2112#64 = wordAt (rdi s) (DEST + tN s) := by rw [hax, addr_dest]
    have haB : r8 t + 2112#64 = wordAt (rdi s) (DEST + bN s) := by rw [hr8, addr_dest]
    have hsT : (t.dmem.loadInt (rax t + 2112#64) 8).isSome = true := by
      rw [hk.mem, hax]; exact arr_isSome hpre _ (Or.inr rfl) hT
    have hsB : (t.dmem.loadInt (r8 t + 2112#64) 8).isSome = true := by
      rw [hk.mem, hr8]; exact arr_isSome hpre _ (Or.inr rfl) hb
    have hsw := Mid.swap (by decide) hpre ho.mid (a := tN s) (b := bN s) (by rw [hst]; exact hT)
      (by rw [hst]; exact hb) (va := rd t.dmem (rax t + 2112#64)) (vb := rd t.dmem (r8 t + 2112#64))
      (by rw [haT, stOf_dest_rd (by omega)]) (by rw [haB, stOf_dest_rd (by omega)])
    rw [← haT, ← haB, hst] at hsw
    have hres : takeBound (st s) (tN s) (bN s) = .ok (swapDest (st s) (tN s) (bN s), true) := by
      rw [takeBound_eq]; simp [show ¬ bN s < tN s by omega, heq, tail]
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact hsT
    case vc2 => exact hsB
    case vc3 => exact hsT
    case vc4 => exact loadInt_isSome_store _ hsB
    case vc5 => exact ho.next hsw.1 rfl rfl rfl rfl rfl rfl rfl
    case vc6 =>
      refine (?_ : Res (rdi s) (takeBound (st s) (tN s) (bN s)) _ _)
      have hres' : takeBound (st s) (tN s) (bN s) = _ := hres
      rw [hres']
      exact ⟨rfl, hsw.2⟩
    case vc7 => simp [V]

end Bbu
