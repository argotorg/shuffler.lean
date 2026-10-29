import BbuKraken.Fn.Loop.Defs

/-!
Machine lemmas of the proof of `loop_body`: the frame, the calls, the stores to the
struct and to the local `urgentToDup`, and some word arithmetic.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

/-! ## Words -/

theorem msb_small {u : Nat} (h : u ≤ 1024) : (BitVec.ofNat 64 u).msb = false := by
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
  omega

theorem toNat_small {u : Nat} (h : u < 2 ^ 64) : (BitVec.ofNat 64 u).toNat = u := by
  simp only [BitVec.toNat_ofNat]; omega

theorem ofNat_inj64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem ofNat_pred {k : Nat} (h : 0 < k) :
    BitVec.ofNat 64 k + -1#64 = BitVec.ofNat 64 (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, BitVec.ofNat_add, BitVec.add_assoc,
    show BitVec.ofNat 64 1 + -1#64 = 0#64 by decide, BitVec.add_zero]

theorem sub_of {L T : Nat} (hlt : T ≤ L) :
    BitVec.ofNat 64 L - BitVec.ofNat 64 T = BitVec.ofNat 64 (L - T) := by
  obtain ⟨j, rfl⟩ : ∃ j, L = j + T := ⟨L - T, by omega⟩
  rw [Nat.add_sub_cancel, BitVec.ofNat_add, BitVec.add_sub_cancel]

-- `encU` is `-1` only for none.
theorem encU_m1 {n u : Nat} (hn : n ≤ 1024) (hu : u ≤ n) : encU n u = -1#64 ↔ u = n := by
  unfold encU
  split
  · simp_all
  · rename_i h
    simp only [h, iff_false]
    intro h'
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    have : (-1#64 : Word).toNat = 2 ^ 64 - 1 := by decide
    omega

/-! ## The frame -/

section
variable {s : MachineData} {ra : Int64} {t c t' : MachineData}

theorem stack_of (h : t.regs.rsp.toBitVec = rsp s - 80#64) :
    t.StackAtOrBelow (s.pushRa ra) := by
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, pushRa_rsp, h]
  bv_omega

-- `stack_of` for a state literal of `kvcgen64`.
theorem stack_mk {r : Reg64s} {z f d} (h : r.rsp.toBitVec = rsp s - 80#64) :
    (MachineData.mk r z f d).StackAtOrBelow (s.pushRa ra) :=
  stack_of h

-- The pops of `.LB65` read the saved words.
theorem Fm.pops {m : Mem 64} (h : Fm s ra m) :
    rd m (rsp s - 56#64) = s.regs.rbx.toBitVec ∧ rd m (rsp s - 48#64) = s.regs.rbp.toBitVec
      ∧ rd m (rsp s - 40#64) = s.regs.r12.toBitVec ∧ rd m (rsp s - 32#64) = s.regs.r13.toBitVec
      ∧ rd m (rsp s - 24#64) = s.regs.r14.toBitVec
      ∧ rd m (rsp s - 16#64) = s.regs.r15.toBitVec :=
  ⟨h.saved 5 (by decide), h.saved 4 (by decide), h.saved 3 (by decide), h.saved 2 (by decide),
    h.saved 1 (by decide), h.saved 0 (by decide)⟩

-- The local `urgentToDup` lies in the frame.
theorem slot_in (hpre : Pre loopF loopA s) :
    Mem.Blocks.Inside (rsp s - 72#64) 8 [frame loopF s] := by
  have hle : 4224 ≤ (rsp s).toNat := hpre.2.1.le
  simp only [Mem.Blocks.Inside, or_false, loopF_eq]
  bv_omega

-- The local `urgentToDup` is not in the struct, the inputs or the ops buffer.
theorem slot_disj (hpre : Pre loopF loopA s) {m : Mem 64} (h : Fm s ra m) :
    Mem.Blocks.Disjoint (writable m (rdi s) ++ readable m (rdi s)) [(rsp s - 72#64, 8)] := by
  rw [(h.keeps hpre).2.2, (h.keeps hpre).2.1]
  exact fun x hx hy => hpre.2.1.disj x (Kit.inside_bytes (slot_in hpre) x hy) hx

-- A store to the local `urgentToDup` keeps `Fm` and the model state.
theorem Fm.slot (hpre : Pre loopF loopA s) {m : Mem 64} (h : Fm s ra m) (v : Int) :
    Fm s ra (m.storeInt (rsp s - 72#64) 8 v)
      ∧ stOf (m.storeInt (rsp s - 72#64) 8 v) (rdi s) = stOf m (rdi s) := by
  have hle : 4224 ≤ (rsp s).toNat := hpre.2.1.le
  have hu : Mem.UnchangedOutside [(rsp s - 72#64, 8)] m (m.storeInt (rsp s - 72#64) 8 v) :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  have hd := slot_disj hpre h
  refine ⟨⟨h.toMid.store (Or.inl (by simpa only [Mem.Blocks.Inside, or_false] using slot_in hpre))
    (fun x hx hy => ?_) v, Wf.congr_of_disjoint hu h.wf hd, fun i hi => ?_⟩, stOf_congr hu h.wf hd⟩
  · simp only [Mem.Blocks.Inside, or_false] at hx hy
    bv_omega
  · rw [rd_storeInt_of_disjoint ?_]
    · exact h.saved i hi
    · intro x hx hy
      simp only [regs, List.length_cons, List.length_nil] at hi
      simp only [Mem.Blocks.Inside, or_false] at hx hy
      have : (BitVec.ofNat 64 (8 * i + 16)).toNat = 8 * i + 16 := by
        simp only [BitVec.toNat_ofNat]; omega
      bv_omega

/-! ## Calls -/

-- A callee at `rsp s - 80` keeps `Base`.
theorem Base.call {G : Nat} {R : MachineData → MachineData → Prop} (hG : 80 + G ≤ loopF)
    (hpre : Pre loopF loopA s) (hb : Base s ra t) (hp : Post G R c t')
    (hag : (mod G c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s) (hbp : c.regs.rbp = t.regs.rbp) :
    Base s ra t' := by
  have hrsp : Bbu.rsp c = Bbu.rsp s - 80#64 := by
    simp only [Bbu.rsp, Reg64s.get64_rsp, hsp]; exact hb.rsp
  have hr := fun (q : Reg64) (hq : q ∉ (mod G c).regs) => hag.reg q hq
  simp only [mod, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h1 := hr .rsp (by decide)
  have h2 := hr .rbp (by decide)
  simp only [Reg64s.get64_rsp, Reg64s.get64_rbp] at h1 h2
  refine ⟨Kit.Fm.call (k := 80) (by decide) hG hpre hb.fm hc hrsp hdi hp hag, ?_, ?_⟩
  · rw [h1, hsp]; exact hb.rsp
  · rw [h2, hbp]; exact hb.rbp

-- A callee keeps the registers that it saves.
theorem call_regs {G : Nat} (hag : (mod G c).Agree c t') :
    t'.regs.rbx = c.regs.rbx ∧ t'.regs.r12 = c.regs.r12 ∧ t'.regs.r13 = c.regs.r13
      ∧ t'.regs.r14 = c.regs.r14 ∧ t'.regs.r15 = c.regs.r15 := by
  have hr := fun (q : Reg64) (hq : q ∉ (mod G c).regs) => hag.reg q hq
  simp only [mod, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h1 := hr .rbx (by decide)
  have h2 := hr .r12 (by decide)
  have h3 := hr .r13 (by decide)
  have h4 := hr .r14 (by decide)
  have h5 := hr .r15 (by decide)
  simp only [Reg64s.get64_rbx, Reg64s.get64_r12, Reg64s.get64_r13, Reg64s.get64_r14,
    Reg64s.get64_r15] at h1 h2 h3 h4 h5
  exact ⟨UInt64.toBitVec_inj.mp h1, UInt64.toBitVec_inj.mp h2, UInt64.toBitVec_inj.mp h3,
    UInt64.toBitVec_inj.mp h4, UInt64.toBitVec_inj.mp h5⟩

-- A callee at `rsp s - 80` keeps the local `urgentToDup`.
theorem slot_call {G : Nat} (hG : 80 + G ≤ loopF)
    (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hag : (mod G c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s) :
    urgentToDupWord s t' = urgentToDupWord s t := by
  have hle : 4224 ≤ (rsp s).toNat := hpre.2.1.le
  have hG' : G ≤ 4144 := by rw [loopF_eq] at hG; omega
  have hu : Mem.UnchangedOutside (frame G c :: writable s.dmem (rdi s)) t.dmem t'.dmem := by
    have := hag.2
    simp only [mod, hc, hdi, (hb.fm.keeps hpre).2.2] at this
    exact this
  have hrsp : rsp c = rsp s - 80#64 := by
    simp only [Bbu.rsp, Reg64s.get64_rsp, hsp]; exact hb.rsp
  refine rd_congr hu fun x hx hl => hl.elim (fun hl => ?_) fun hl => ?_
  · simp only [Mem.Blocks.Inside, or_false, hrsp] at hx hl
    bv_omega
  · have hd := slot_disj hpre hb.fm
    rw [(hb.fm.keeps hpre).2.2] at hd
    exact hd x (inside_append.mpr (Or.inl hl)) hx

theorem env_call (hpre : Pre loopF loopA s) (hb : Base s ra t) (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) : env c = env s := by
  show envOf c.dmem (rdi c) = _
  rw [hc, hdi]; exact (hb.fm.keeps hpre).1

theorem st_call (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) : st c = st' s t := by
  show stOf c.dmem (rdi c) = _
  rw [hc, hdi]

theorem cap_call (hpre : Pre loopF loopA s) (hb : Base s ra t) (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) : cap c = cap s := by
  show 6 * nOf c.dmem (rdi c) = _
  rw [hc, hdi, hb.fm.n hpre]

theorem positionOf_post (hp : Post positionOfF positionOfR c t') (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) :
    rax t' = encOpt (positionOf (st' s t) (rsi c).toNat) ∧ st' s t' = st' s t := by
  have h := hp.2.2
  unfold positionOfR at h
  rw [st_call hc hdi] at h
  exact ⟨h.1, by simpa only [st', hdi] using h.2⟩

theorem isSpilled_post (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hp : Post isSpilledF isSpilledR c t') (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) :
    rax t' = BitVec.ofNat 64 (isSpilled (env s) (rsi c)).toNat ∧ st' s t' = st' s t := by
  have h := hp.2.2
  unfold isSpilledR at h
  rw [st_call hc hdi, env_call hpre hb hc hdi] at h
  exact ⟨h.1, by simpa only [st', hdi] using h.2⟩

theorem shallowestCopy_post (hp : Post shallowestCopyF shallowestCopyR c t') (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) :
    rax t' = encOpt (shallowestCopyPosition (st' s t) (rsi c)) ∧ st' s t' = st' s t := by
  have h := hp.2.2
  unfold shallowestCopyR at h
  rw [st_call hc hdi] at h
  exact ⟨h.1, by simpa only [st', hdi] using h.2⟩

theorem generate_post (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hp : Post generateF generateR c t') (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) :
    Res (rdi s) (generate (env s) (st' s t) (rsi c).toNat)
      (fun r => rax t' = 0#64 ∧ st' s t' = r) t' := by
  have h := hp.2.2
  unfold generateR at h
  rw [hdi, env_call hpre hb hc hdi, st_call hc hdi] at h
  exact Res.imp h fun _ ⟨h1, h2⟩ => ⟨h1, by simpa only [st', hdi, id] using h2⟩

theorem swapWith_post (hp : Post swapWithF swapWithR c t') (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) :
    Res (rdi s) (swapWith (st' s t) (rsi c).toNat) (fun r => rax t' = 0#64 ∧ st' s t' = r) t' := by
  have h := hp.2.2
  unfold swapWithR at h
  rw [hdi, st_call hc hdi] at h
  exact Res.imp h fun _ ⟨h1, h2⟩ => ⟨h1, by simpa only [st', hdi, id] using h2⟩

theorem finish_post (hp : Post finishF finishR c t') (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) :
    Res (rdi s) (finish (st' s t)) (fun ops => rax t' = 0#64 ∧ (st' s t').trace = ops) t' := by
  have h := hp.2.2
  unfold finishR at h
  rw [hdi, st_call hc hdi] at h
  exact Res.imp h fun _ ⟨h1, h2⟩ => ⟨h1, by simpa only [st', hdi] using h2⟩

-- An ok result has a word with no sign bit in `rax`.
theorem res_ok_of_msb {α : Type} {S : Addr} {r : M α} {Q : α → Prop} {u : MachineData}
    (h : Res S r Q u) (hm : (rax u).msb = false) : ∃ a, r = .ok a ∧ Q a := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => rw [Res.msb h] at hm; cases hm

end

/-! ## Stores to the struct -/

section
variable {s : MachineData} {ra : Int64} {m : Mem 64}

-- A store to `writable` keeps a word of the frame.
theorem rd_store_frame (hpre : Pre loopF loopA s) {a b : Addr}
    (ha : Mem.Blocks.Inside a 8 (writable s.dmem (rdi s)))
    (hb : Mem.Blocks.Inside b 8 [frame loopF s]) (v : Int) :
    rd (m.storeInt a 8 v) b = rd m b :=
  rd_storeInt_of_disjoint fun x hx hy => hpre.2.1.disj x (Kit.inside_bytes hb x hy)
    (inside_append.mpr (Or.inl (Kit.inside_bytes ha x hx)))

-- A store of 8 bytes in `writable` that keeps `len` and `nops`, and the local `urgentToDup`.
theorem Fm.store (hpre : Pre loopF loopA s) (h : Fm s ra m) {a : Addr} {v : Int}
    (ha : Mem.Blocks.Inside a 8 (writable s.dmem (rdi s)))
    (h0 : rd (m.storeInt a 8 v) (wordAt (rdi s) 0) = rd m (wordAt (rdi s) 0))
    (h2 : rd (m.storeInt a 8 v) (wordAt (rdi s) 2) = rd m (wordAt (rdi s) 2)) :
    Fm s ra (m.storeInt a 8 v) ∧ rd (m.storeInt a 8 v) (rsp s - 72#64) = rd m (rsp s - 72#64) := by
  have hle : 4224 ≤ (rsp s).toNat := hpre.2.1.le
  have hm := h.toMid.store_w (by decide) hpre ha v
  refine ⟨⟨hm, hm.wf hpre (h0 ▸ h.wf.len_le) (by rw [h2, ← h.n hpre]; exact h.wf.nops_le),
    fun i hi => ?_⟩, rd_store_frame hpre ha (slot_in hpre) v⟩
  rw [rd_store_frame hpre ha ?_ v]
  · exact h.saved i hi
  · simp only [regs, List.length_cons, List.length_nil] at hi
    have : (BitVec.ofNat 64 (8 * i + 16)).toNat = 8 * i + 16 := by
      simp only [BitVec.toNat_ofNat]; omega
    simp only [Mem.Blocks.Inside, or_false, loopF_eq]
    bv_omega

end

section
variable {m : Mem 64} {S : Addr}

-- The dest word of slot `i` is in `writable`.
theorem inside_dest {i : Nat} (hi : i < 1024) :
    Mem.Blocks.Inside (wordAt S (DEST + i)) 8 (writable m S) := by
  have : wordAt S (DEST + i) = wordAt S STACK + BitVec.ofNat 64 (8 * (DEST + i - 8)) := by
    simp only [STACK, DEST_eq]; bv_omega
  rw [this]
  exact (Mem.Blocks.Inside.base_add (by simp only [BitVec.toNat_ofNat, MAX_N, DEST_eq]; omega)).tail

-- A store to the dest word of slot `i` keeps the other words of the struct.
theorem rd_store_dest_other (hw : Wf m S) {i k : Nat} (hi : i < 1024) (hk : k < WORDS)
    (hne : k ≠ DEST + i) (v : Int) :
    rd (m.storeInt (wordAt S (DEST + i)) 8 v) (wordAt S k) = rd m (wordAt S k) :=
  rd_storeInt_of_disjoint (disjoint_wordAt (Ne.symm hne) (by simp only [DEST_eq, WORDS_eq]; omega) hk
    hw.struct_lt)

-- A store to the dest word of slot `i` keeps the ops buffer.
theorem rd_store_dest_ops (hw : Wf m S) {i j : Nat} (hi : i < 1024) (hj : j < 12 * nOf m S) (v : Int) :
    rd (m.storeInt (wordAt S (DEST + i)) 8 v) (wordAt (opsOf m S) j) = rd m (wordAt (opsOf m S) j) := by
  have hs := hw.struct_lt
  have ho := hw.ops_lt
  refine rd_storeInt_of_disjoint fun x hx hy => hw.disj_struct x ?_ (Or.inl ?_)
  · simp only [Mem.Blocks.Inside, or_false, DEST_eq, WORDS_eq] at hx hs ⊢
    bv_omega
  · simp only [Mem.Blocks.Inside, or_false] at hy ⊢
    bv_omega

theorem stOf_store_dest (hw : Wf m S) {i : Nat} (hi : i < (rd m (wordAt S 0)).toNat) (v : Word) :
    stOf (m.storeInt (wordAt S (DEST + i)) 8 v.toInt) S =
      { stOf m S with slots := (stOf m S).slots.set i ⟨(stOf m S).val i, v.toNat⟩ } := by
  have hlen : _ ≤ 1024 := hw.len_le
  have hi' : i < 1024 := by omega
  have hk : ∀ {k}, k < WORDS → k ≠ DEST + i →
      rd (m.storeInt (wordAt S (DEST + i)) 8 v.toInt) (wordAt S k) = rd m (wordAt S k) :=
    fun hk hne => rd_store_dest_other hw hi' hk hne _
  have ho : opsOf (m.storeInt (wordAt S (DEST + i)) 8 v.toInt) S = opsOf m S :=
    hk (k := 6) (by decide) (by simp only [DEST_eq]; omega)
  have hnops := hw.nops_le
  rw [val_stOf hi]
  simp only [stOf, hk (k := 0) (by decide) (by simp only [DEST_eq]; omega),
    hk (k := 1) (by decide) (by simp only [DEST_eq]; omega),
    hk (k := 2) (by decide) (by simp only [DEST_eq]; omega)]
  congr 1
  · refine List.ext_getElem (by simp) fun j h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_set]
    simp only [List.getElem_map, List.getElem_range, slotOf]
    split
    · subst_vars
      rw [hk (by simp only [STACK, WORDS_eq]; omega) (by simp only [STACK, DEST_eq]; omega),
        rd_store_same _ rfl, BitVec.ofInt_toInt]
    · rw [hk (by simp only [STACK, WORDS_eq]; omega) (by simp only [STACK, DEST_eq]; omega),
        hk (by simp only [DEST_eq, WORDS_eq]; omega) (by omega)]
  · refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    simp only [opOf, ho, rd_store_dest_ops hw hi' (j := 2 * j) (by omega),
      rd_store_dest_ops hw hi' (j := 2 * j + 1) (by omega)]

theorem val_set_self (st : St) (a b x : Nat) :
    ({ st with slots := st.slots.set a ⟨st.val a, x⟩ } : St).val b = st.val b := by
  simp only [St.val, List.getElem?_set]
  by_cases hb : b < st.slots.length <;> split <;> simp_all [Nat.not_lt.mpr]

end

section
variable {s : MachineData} {ra : Int64} {m : Mem 64}

theorem Fm.store_dest (hpre : Pre loopF loopA s) (h : Fm s ra m) {i : Nat} (hi : i < 1024) (v : Int) :
    Fm s ra (m.storeInt (wordAt (rdi s) (DEST + i)) 8 v)
      ∧ rd (m.storeInt (wordAt (rdi s) (DEST + i)) 8 v) (rsp s - 72#64) = rd m (rsp s - 72#64) :=
  h.store hpre (inside_dest hi)
    (rd_store_dest_other h.wf hi (by decide) (by simp only [DEST_eq]; omega) v)
    (rd_store_dest_other h.wf hi (by decide) (by simp only [DEST_eq]; omega) v)

-- The two stores of the dest words of `a` and `b` give `swapDestinations`, and keep the local
-- `urgentToDup`.
theorem Fm.swap (hpre : Pre loopF loopA s) (h : Fm s ra m) {a b : Nat}
    (ha : a < (stOf m (rdi s)).len) (hb : b < (stOf m (rdi s)).len) {va vb : Word}
    (hva : va.toNat = (stOf m (rdi s)).dest a) (hvb : vb.toNat = (stOf m (rdi s)).dest b) :
    Fm s ra ((m.storeInt (wordAt (rdi s) (DEST + a)) 8 vb.toInt).storeInt
        (wordAt (rdi s) (DEST + b)) 8 va.toInt)
      ∧ stOf ((m.storeInt (wordAt (rdi s) (DEST + a)) 8 vb.toInt).storeInt
        (wordAt (rdi s) (DEST + b)) 8 va.toInt) (rdi s) = swapDestinations (stOf m (rdi s)) a b
      ∧ rd ((m.storeInt (wordAt (rdi s) (DEST + a)) 8 vb.toInt).storeInt
        (wordAt (rdi s) (DEST + b)) 8 va.toInt) (rsp s - 72#64) = rd m (rsp s - 72#64) := by
  have hl : _ ≤ 1024 := h.wf.len_le
  rw [len_stOf] at ha hb
  obtain ⟨h1, r1⟩ := h.store_dest hpre (i := a) (by omega) vb.toInt
  have e1 := stOf_store_dest h.wf ha vb
  have hb1 : b < (rd (m.storeInt (wordAt (rdi s) (DEST + a)) 8 vb.toInt) (wordAt (rdi s) 0)).toNat := by
    rw [rd_store_dest_other h.wf (by omega) (by decide) (by simp only [DEST_eq]; omega)]
    exact hb
  obtain ⟨h2, r2⟩ := h1.store_dest hpre (i := b) (by omega) va.toInt
  refine ⟨h2, ?_, r2.trans r1⟩
  rw [stOf_store_dest h1.wf hb1 va, e1]
  simp only [swapDestinations, val_set_self, hva, hvb]

-- The two stores to `blocked` of a blocked error give `Res`, and keep `Fm`.
theorem Fm.blocked (hpre : Pre loopF loopA s) (h : Fm s ra m) {u : MachineData} {c k : Nat}
    (hm : u.dmem = (m.storeInt (wordAt (blkOf m (rdi s)) 0) 8 (BitVec.ofNat 64 c).toInt).storeInt
      (wordAt (blkOf m (rdi s)) 1) 8 (BitVec.ofNat 64 k).toInt) (hr : rax u = -1#64) :
    Fm s ra u.dmem ∧ Res (rdi s) (.error (.blocked c k) : M (List Op))
      (fun ops => rax u = 0#64 ∧ (st' s u).trace = ops) u := by
  have hb := h.wf.blk_lt
  refine ⟨hm ▸ h.blk (by decide) hpre _ _, hr, ?_, ?_⟩
  · rw [hm, blkOf_store2 h.wf, rd_store_other _ (by simp only [wordAt]; bv_omega),
      rd_store_same _ (by simp only [wordAt]; bv_omega), BitVec.ofInt_toInt]
  · rw [hm, blkOf_store2 h.wf, rd_store_same _ rfl, BitVec.ofInt_toInt]

end

end Loop

end Bbu
