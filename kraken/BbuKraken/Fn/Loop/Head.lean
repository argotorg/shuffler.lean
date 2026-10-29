import BbuKraken.Fn.Loop.Machine
import BbuKraken.Fn.Loop.Model

/-!
The loop head of `buildBottomUp`: `.LB64` (the next offset), `.LB85` (skip a final
slot), `.LB63` (start the `urgentToDup` scan) and `.LB92`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

/-! ## Helpers -/

section
variable {s : MachineData} {ra : Int64} {t : MachineData}

-- The word `n` of the struct.
theorem rd_n (hpre : Pre loopF loopA s) {m : Mem 64} (h : Fm s ra m) :
    rd m (rdi s + 24#64) = BitVec.ofNat 64 (env s).n := by
  rw [show (env s).n = nOf s.dmem (rdi s) from n_envOf, ← h.n hpre]
  apply BitVec.eq_of_toNat_eq
  simp [nOf, wordAt]

theorem n_le (hpre : Pre loopF loopA s) {m : Mem 64} (h : Fm s ra m) : (env s).n ≤ 1024 := by
  rw [show (env s).n = nOf s.dmem (rdi s) from n_envOf, ← h.n hpre]
  exact h.wf.n_le

-- The word `len` of the struct.
theorem rd_len (hb : Base s ra t) : rd t.dmem t.regs.rbp.toBitVec = BitVec.ofNat 64 (st' s t).len := by
  rw [len_stOf, hb.rbp]
  apply BitVec.eq_of_toNat_eq
  simp [wordAt]

theorem isSome_len (hb : Base s ra t) : (t.dmem.loadInt t.regs.rbp.toBitVec 8).isSome := by
  rw [hb.rbp]
  exact hb.fm.wf.isSome_struct (by simp [WORDS_eq])

theorem len_le (hb : Base s ra t) : (st' s t).len ≤ 1024 := by
  rw [len_stOf]; exact Nat.le_trans hb.fm.wf.len_le hb.fm.wf.n_le

-- The address of the dest word of slot `T`.
theorem dest_addr (hb : Base s ra t) {T : Nat} (hT : t.regs.r14.toBitVec = BitVec.ofNat 64 T) :
    t.regs.rbp.toBitVec + t.regs.r14.toBitVec * 8#64 + 72#64 = wordAt (rdi s) (DEST + T) := by
  rw [hb.rbp, hT]
  simp only [wordAt, DEST_eq]
  bv_omega

theorem dest_eq_iff (hb : Base s ra t) {T : Nat} (hT : t.regs.r14.toBitVec = BitVec.ofNat 64 T)
    (hlt : T < (st' s t).len) :
    rd t.dmem (t.regs.rbp.toBitVec + t.regs.r14.toBitVec * 8#64 + 72#64) = t.regs.r14.toBitVec
      ↔ (st' s t).dest T = T := by
  have := len_le hb
  rw [dest_addr hb hT, dest_stOf (by rw [← len_stOf]; exact hlt), hT]
  constructor
  · intro h; rw [h, BitVec.toNat_ofNat]; omega
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]; omega

theorem isSome_dest (hb : Base s ra t) {T : Nat} (hT : t.regs.r14.toBitVec = BitVec.ofNat 64 T)
    (hlt : T < 1024) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + t.regs.r14.toBitVec * 8#64 + 72#64) 8).isSome := by
  rw [dest_addr hb hT]
  refine hb.fm.wf.isSome_struct ?_
  simp only [wordAt, DEST_eq, WORDS_eq]
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  omega

-- A load of a word of the struct succeeds.
theorem isSome_word (hb : Base s ra t) {k : Nat} (hk : k < WORDS) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + BitVec.ofNat 64 (8 * k)) 8).isSome := by
  rw [hb.rbp]
  refine hb.fm.wf.isSome_struct ?_
  simp only [WORDS_eq] at hk ⊢
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  omega

-- The word `m_pendingGenerations` of the struct.
theorem pending_eq (hb : Base s ra t) :
    (st' s t).pendingGenerations = (rd t.dmem (t.regs.rbp.toBitVec + BitVec.ofNat 64 8)).toNat := by
  rw [hb.rbp]; rfl

-- The local `urgentToDup` at `8(%rsp)`.
theorem slot_addr (hb : Base s ra t) :
    t.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 8) = rsp s - 72#64 := by
  rw [disp1, hb.rsp]; simp only [wordAt]; bv_omega

theorem isSome_slot (hpre : Pre loopF loopA s) (hb : Base s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 8)) 8).isSome := by
  rw [slot_addr hb]
  exact Mem.Mapped.loadInt_isSome hb.fm.toMid.map
    (Or.inl (by simpa only [Mem.Blocks.Inside, or_false] using slot_in hpre))

-- `.LB63` to `.LB66`: `rbx := T`, `urgentToDup := -1`.
theorem at66_mk (hpre : Pre loopF loopA s) (hb : Base s ra t)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f}
    (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp)
    (h13 : a13.toBitVec = BitVec.ofNat 64 (env s).n)
    (h15 : a15.toBitVec = BitVec.ofNat 64 (st' s t).len) {T : Nat}
    (h14 : a14.toBitVec = BitVec.ofNat 64 T) (h1 : a1.toBitVec = BitVec.ofNat 64 T)
    (hc : Ctx s T (st' s t)) (hnf : ¬ (T < (st' s t).len ∧ (st' s t).dest T = T))
    (hp : (st' s t).pendingGenerations ≠ 0) :
    At66 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f,
      Mem.storeInt t.dmem (t.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 8)) 8 (-1)⟩ := by
  subst h6 h7
  obtain ⟨hfm, hst⟩ := Fm.slot hpre hb.fm (-1)
  rw [slot_addr hb]
  have hst' : st' s ⟨⟨a0, a1, a2, a3, a4, a5, t.regs.rsp, t.regs.rbp, a8, a9, a10, a11, a12, a13,
      a14, a15⟩, z, f, t.dmem.storeInt (rsp s - 72#64) 8 (-1)⟩ = st' s t := hst
  refine ⟨T, T, (env s).n, ⟨⟨hfm, hb.rsp, hb.rbp⟩, h13, ?_, h14, h1, ?_, Nat.le_refl _, hc.1, ?_, ?_⟩, ?_⟩
  · rw [hst']; exact h15
  · show rd (t.dmem.storeInt (rsp s - 72#64) 8 (-1)) (rsp s - 72#64) = _
    rw [rd_store_same _ rfl]; simp [encU]
  · rw [hst']; exact hc
  · rw [hst']; exact hp
  · rw [hst']; exact step_urgent hnf hp

end

set_option experimental.vcgen true

variable [Host] [FunDecls] {s : MachineData} {ra : Int64}

-- The next offset: `.LB62` at `n`, else `.LB85`.
theorem lb64 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB64") := by
  loop_case
  intro t ht
  have h : At64 s ra t := ht
  obtain ⟨hb, T', hT', hinv, hl⟩ := h
  have hn := rd_n hpre hb.fm
  have hnle : (env s).n ≤ 1024 := n_le hpre hb.fm
  have hlen : (st' s t).len ≤ 1024 := len_le hb
  have hTle : T' ≤ 1024 := Nat.le_trans hinv.2 hlen
  have e1 := toNat_small (show T' < 2 ^ 64 by omega)
  have e2 := toNat_small (show (env s).n < 2 ^ 64 by omega)
  have hT1 : 1#64 + t.regs.r14.toBitVec = BitVec.ofNat 64 T' := by rw [BitVec.add_comm]; exact hT'
  kvcgen64
  · exact isSome_word hb (k := 3) (by decide)
  · rename_i hf
    bbu_norm at hf
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', Kit.cf_sub'] at hf
    simp only [hb.rbp, hn, hT1, e1, e2] at hf
    loop_goto
    · exact stack_of hb.rsp
    · show At62 s ra _
      refine ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, ?_, loop_end (Nat.not_lt.mpr hf) hl⟩
      show rd t.dmem (t.regs.rbp.toBitVec + 24#64) = _
      rw [hb.rbp, hn]
    · simp only [V]
      omega
  · rename_i hf
    bbu_norm at hf
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hf
    simp only [hb.rbp, hn, hT1, e1, e2] at hf
    show At85 s ra _
    refine ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, ?_, T', hT1, hf, hinv, hl⟩
    show rd t.dmem (t.regs.rbp.toBitVec + 24#64) = _
    rw [hb.rbp, hn]
  · simp only [V, outer, st', hT1, hT']
    omega

-- A final slot at `T` goes to `.LB64`, else `.LB63`.
theorem lb85 : OblAt s ra (.label ".LB85") := by
  loop_case
  intro t ht
  have h : At85 s ra t := ht
  obtain ⟨hb, h13, T, hT, hc⟩ := h
  have hlen := len_le hb
  have hTlen : T ≤ (st' s t).len := (ctx_bounds hc).2.2.1
  have hTn : T < (env s).n := hc.1
  have e1 := toNat_small (show T < 2 ^ 64 by omega)
  have e2 := toNat_small (show (st' s t).len < 2 ^ 64 by omega)
  have hl := rd_len hb
  kvcgen64
  · bbu_norm
    exact isSome_len hb
  · rename_i hf
    bbu_norm at hf
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', Kit.cf_sub'] at hf
    simp only [hl, hT, e1, e2] at hf
    loop_goto
    · exact stack_of hb.rsp
    · show At63 s ra _
      exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, h13, by bbu_norm; exact hl, T, hT, hc, fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h.1 hf)⟩
    · simp only [V, outer, st']
      omega
  · rename_i hf
    bbu_norm at hf
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hf
    simp only [hl, hT, e1, e2] at hf
    bbu_norm
    exact isSome_dest hb hT (by omega)
  · rename_i hf hz
    bbu_norm at hf hz
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hf
    simp only [hl, hT, e1, e2] at hf
    rw [Kit.z_sub, beq_iff_eq, dest_eq_iff hb hT hf] at hz
    have hd := hz
    obtain ⟨hinv, hloop⟩ := iter_next (by have := ctx_iter hc; rwa [step_done ⟨hf, hd⟩] at this)
    loop_goto
    · exact stack_of hb.rsp
    · show At64 s ra _
      exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, T + 1, by rw [hT, BitVec.ofNat_add], hinv, hloop⟩
    · have hn : T < (env s).n := hTn
      simp only [V, outer, W, st', hT, ← BitVec.ofNat_add, toNat_small (show T + 1 < 2 ^ 64 by omega), e1]
      omega
  · rename_i hf hz
    bbu_norm at hf hz
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hf
    simp only [hl, hT, e1, e2] at hf
    rw [Kit.z_sub, beq_eq_false_iff_ne, ne_eq, dest_eq_iff hb hT hf] at hz
    show At63 s ra _
    refine ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, h13, by bbu_norm; exact hl, T, hT, hc, fun h => hz h.2⟩
  · simp only [V, outer, st']
    omega

-- `.LB65` if no slot is pending, else store `-1` in `urgentToDup` and go to `.LB66`
-- (`.LB67` is dead: `T < n`).
theorem lb63 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB63") := by
  loop_case
  intro t ht
  have h : At63 s ra t := ht
  obtain ⟨hb, h13, h15, T, hT, hc, hnf⟩ := h
  have hnle : (env s).n ≤ 1024 := n_le hpre hb.fm
  have hTn : T < (env s).n := hc.1
  have e1 := toNat_small (show T < 2 ^ 64 by omega)
  have e2 := toNat_small (show (env s).n < 2 ^ 64 by omega)
  have hp := pending_eq hb
  have hst : stOf (Mem.storeInt t.dmem (t.regs.rsp.toBitVec + BitVec.ofInt 64 (Int64.toInt 8)) 8 (-1))
      (rdi s) = st' s t := by
    rw [slot_addr hb]; exact (Fm.slot hpre hb.fm (-1)).2
  kvcgen64
  · exact isSome_word hb (k := 1) (by decide)
  · rename_i hz
    bbu_norm at hz
    rw [Kit.z_sub, beq_iff_eq] at hz
    have hp0 : (st' s t).pendingGenerations = 0 := by rw [hp, hz]; rfl
    loop_goto
    · exact stack_of hb.rsp
    · show At65 s ra _
      exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, h13, h15, T, hc, hnf, hp0⟩
    · simp only [V]
      omega
  · bbu_norm
    exact isSome_slot hpre hb
  · rename_i hz hf
    bbu_norm at hz
    rw [Kit.z_sub, beq_eq_false_iff_ne, ne_eq] at hz
    have hp0 : (st' s t).pendingGenerations ≠ 0 := by
      rw [hp]; intro h; exact hz (BitVec.eq_of_toNat_eq (by simpa using h))
    loop_goto
    · exact stack_of hb.rsp
    · show At66 s ra _
      exact at66_mk hpre hb rfl rfl h13 h15 hT hT hc hnf hp0
    · simp only [V, outer, W, st', hst, hT, e1]
      have hn' : (env s).n ≤ 1024 := hnle
      exact Or.inl (show 8192 * (((env s).n - T) * 2048 + (st' s t).pendingGenerations) + 3002
        + 3 * ((env s).n - T)
        < 8192 * (((env s).n - T) * 2048 + (st' s t).pendingGenerations) + 7999 by omega)
  all_goals
    rename_i hz hf
    bbu_norm at hf
    simp only [CondCode.interp_c, StatusFlags.cf_from_result, Kit.cf_sub'] at hf
    simp only [h13, hT, e1, e2] at hf
    exact absurd hTn (Nat.not_lt.mpr hf)

-- The offset in `rsi` goes to `r14`.
theorem lb92 : OblAt s ra (.label ".LB92") := by
  loop_case
  intro t ht
  kvcgen64
  loop_goto
  · exact stack_of ht.1.rsp
  · have h : At92 s ra t := ht
    show At64 s ra _
    exact ⟨⟨h.1.fm, h.1.rsp, h.1.rbp⟩, h.2⟩
  · simp only [V, outer, st']
    omega

end Loop

end Bbu
