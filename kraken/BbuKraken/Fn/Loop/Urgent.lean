import BbuKraken.Fn.Loop.Machine
import BbuKraken.Fn.Loop.Model

/-!
The `urgentToDup` scan of `buildBottomUp`: `.LB70` (the slot bound for `d`), `.LB100`
(`isSpilled` and `shallowestCopyPosition` of the target word of `d`) and `.LB73` (the
next `d`).
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

set_option experimental.vcgen true


/-! ## Helpers -/

section
variable {s : MachineData} {ra : Int64}
variable {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z : RegZmms}
  {f : StatusFlags} {dm : Mem 64}

-- The bound `n ≤ 1024` of a scan.
theorem Scan.n_le {T d u : Nat} {t : MachineData} (h : Scan s ra T d u t) : (env s).n ≤ 1024 :=
  (ctx_bounds h.2.2.2.2.2.2.2.2.1).2.1

/- A state literal of the scan at `d'`, with the fields of `t` but `rbx`. As `stack_mk` in
old `Fn/Urgent.lean`: each field is a variable, so the kernel does not unfold the literal. -/
theorem scan_mk {T d d' u : Nat} {t : MachineData} (h : Scan s ra T d u t) (hm : dm = t.dmem)
    (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp) (h13 : a13 = t.regs.r13)
    (h14 : a14 = t.regs.r14) (h15 : a15 = t.regs.r15) (hbx : a1.toBitVec = BitVec.ofNat 64 d')
    (hd : d' < (env s).n) :
    Scan s ra T d' u
    ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, dm⟩ := by
  subst hm h6 h7 h13 h14 h15
  obtain ⟨hb, h13, h15, h14, -, hsl, hun, -, hctx, hpd⟩ := h
  exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, h13, h15, h14, hbx, hsl, hun, hd, hctx, hpd⟩

-- `At73` for a state literal with the fields of `x`. See `scan_mk`.
theorem at73_mk {T d u : Nat} {x : MachineData} (h : Scan s ra T d u x) (hm : dm = x.dmem)
    (h6 : a6 = x.regs.rsp) (h7 : a7 = x.regs.rbp) (h1 : a1 = x.regs.rbx) (h13 : a13 = x.regs.r13)
    (h14 : a14 = x.regs.r14) (h15 : a15 = x.regs.r15)
    (hstep : step (env s) (st' s x) T
      = (urgentFrom (env s) (st' s x) T (d + 1) u).bind (afterUrgent (env s) (st' s x) T)) :
    At73 s ra
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, dm⟩ := by
  subst hm h1
  exact ⟨T, d, u, scan_mk h rfl h6 h7 h13 h14 h15 h.2.2.2.2.1 h.2.2.2.2.2.2.2.1, hstep⟩

-- `At100` for a state literal with the fields of `x`. See `scan_mk`.
theorem at100_mk {T d u : Nat} {x : MachineData} (h : Scan s ra T d u x) (hm : dm = x.dmem)
    (h6 : a6 = x.regs.rsp) (h7 : a7 = x.regs.rbp) (h1 : a1 = x.regs.rbx) (h13 : a13 = x.regs.r13)
    (h14 : a14 = x.regs.r14) (h15 : a15 = x.regs.r15)
    (hstep : step (env s) (st' s x) T
      = (urgentFrom (env s) (st' s x) T d u).bind (afterUrgent (env s) (st' s x) T))
    (h12 : a12.toBitVec = (env s).target[d]!) (hp : positionOf (st' s x) d = none)
    (hf : isFree (env s).target[d]! = false) :
    At100 s ra
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, dm⟩ := by
  subst hm h1
  exact ⟨T, d, u, scan_mk h rfl h6 h7 h13 h14 h15 h.2.2.2.2.1 h.2.2.2.2.2.2.2.1, hstep, h12, hp,
    hf⟩

-- A call with `rdi = rbp` keeps the scan. `c` is the state at the call.
theorem Scan.call {G T d u : Nat} {R : MachineData → MachineData → Prop} {t c t' : MachineData}
    (hG : 80 + G ≤ loopF) (hpre : Pre loopF loopA s) (h : Scan s ra T d u t)
    (hp : Post G R c t') (hag : (mod G c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s) (hbp : c.regs.rbp = t.regs.rbp)
    (hbx : c.regs.rbx = t.regs.rbx) (h13 : c.regs.r13 = t.regs.r13) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hst : st' s t' = st' s t) : Scan s ra T d u t' := by
  obtain ⟨hb, h13', h15', h14', hbx', hsl, hun, hd, hctx, hpd⟩ := h
  obtain ⟨r1, -, r3, r4, r5⟩ := call_regs hag
  refine ⟨hb.call hG hpre hp hag hc hsp hdi hbp, ?_, ?_, ?_, ?_, ?_, hun, hd, ?_, ?_⟩
  · rw [r3, h13]; exact h13'
  · rw [r5, h15, hst]; exact h15'
  · rw [r4, h14]; exact h14'
  · rw [r1, hbx]; exact hbx'
  · rw [slot_call hG hpre hb hag hc hsp hdi]; exact hsl
  · rw [hst]; exact hctx
  · rw [hst]; exact hpd

-- The bound `len ≤ 1024` of a scan.
theorem Scan.len_le {T d u : Nat} {t : MachineData} (h : Scan s ra T d u t) :
    (st' s t).len ≤ 1024 := by
  have := (ctx_bounds h.2.2.2.2.2.2.2.2.1).1
  have := h.n_le
  omega

-- The call of `positionOf d` in the scan.
theorem scan_pos {T d u : Nat} {t c t' : MachineData} (hpre : Pre loopF loopA s)
    (h : Scan s ra T d u t) (hp : Post positionOfF positionOfR c t')
    (hag : (mod positionOfF c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s) (hbp : c.regs.rbp = t.regs.rbp)
    (hbx : c.regs.rbx = t.regs.rbx) (h13 : c.regs.r13 = t.regs.r13) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hsi : rsi c = t.regs.rbx.toBitVec) :
    Scan s ra T d u t' ∧ st' s t' = st' s t
      ∧ t'.regs.rax.toBitVec = encOpt (positionOf (st' s t) d) := by
  obtain ⟨hr, hst⟩ := positionOf_post hp hc hdi
  have hn := h.n_le
  have hd : d < (env s).n := h.2.2.2.2.2.2.2.1
  refine ⟨h.call (by decide) hpre hp hag hc hsp hdi hbp hbx h13 h14 h15 hst, hst, ?_⟩
  rw [hsi, h.2.2.2.2.1, toNat_small (by omega)] at hr
  exact hr

-- The result of `positionOf` is not `-1` for a bound slot.
theorem none_of_enc {o : Option Nat} (h : ∀ p, o = some p → p < 1024)
    (hz : (!(encOpt o == 18446744073709551615#64)) = false) : o = none := by
  cases o with
  | none => rfl
  | some p =>
    have hp := h p rfl
    simp only [encOpt, Bool.not_eq_false', beq_iff_eq] at hz
    have := ofNat_inj64 (by omega) (by decide) hz
    omega

theorem some_of_enc {o : Option Nat} (hz : (!(encOpt o == 18446744073709551615#64)) = true) :
    o.isSome = true := by
  cases o with
  | none => exact absurd hz (by decide)
  | some p => rfl

-- The target word of `d` in the scan.
theorem tgt_word {d : Nat} {x : MachineData} (hpre : Pre loopF loopA s) (hb : Base s ra x)
    (hbx : x.regs.rbx.toBitVec = BitVec.ofNat 64 d) (hd : d < (env s).n) :
    rd x.dmem (rd x.dmem (x.regs.rbp.toBitVec + 32#64) + x.regs.rbx.toBitVec * 8#64)
      = (env s).target[d]! := by
  have he := (hb.fm.keeps hpre).1
  have hn : d < nOf x.dmem (rdi s) := by rw [← n_envOf, he]; exact hd
  rw [← he, target_get hn, hb.rbp, hbx]
  show rd _ (tgtOf x.dmem (rdi s) + _) = rd _ (tgtOf x.dmem (rdi s) + BitVec.ofNat 64 (8 * d))
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem tgt_some {d : Nat} {x : MachineData} (hpre : Pre loopF loopA s) (hb : Base s ra x)
    (hbx : x.regs.rbx.toBitVec = BitVec.ofNat 64 d) (hd : d < (env s).n) :
    (x.dmem.loadInt (rd x.dmem (x.regs.rbp.toBitVec + 32#64) + x.regs.rbx.toBitVec * 8#64) 8).isSome
      = true := by
  have he := (hb.fm.keeps hpre).1
  have hn : nOf x.dmem (rdi s) = (env s).n := by rw [← n_envOf, he]
  have hw := hb.fm.wf
  have ht := hw.tgt_lt
  have hle := hw.n_le
  rw [hb.rbp, hbx]
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr (Or.inr ?_))
  refine inside_of_mem (p := (tgtOf x.dmem (rdi s), 8 * nOf x.dmem (rdi s)))
    (by simp [readable]) (Or.inl ?_)
  change (tgtOf x.dmem (rdi s)).toNat + _ ≤ _ at ht
  rw [hn] at ht hle ⊢
  simp only [MAX_N] at hle
  change (tgtOf x.dmem (rdi s) + BitVec.ofNat 64 d * 8#64 - tgtOf x.dmem (rdi s)).toNat + 8 ≤ _
  rw [BitVec.add_comm (tgtOf _ _), BitVec.add_sub_cancel, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

-- The zero flag of `testb $1, x`.
theorem z_odd (x : Word) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (x.take 8 &&& 1#8) f) = (x.toNat % 2 == 0) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  have h : (x.take 8 &&& 1#8).toNat = x.toNat % 2 := by
    simp only [BitVec.take, BitVec.toNat_and, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      BitVec.toNat_ofNat]
    rw [show 1 % 2 ^ 8 = 1 from rfl, Nat.and_one_is_mod]
    omega
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← h]
  constructor
  · intro h3; rw [h3]; rfl
  · intro h3; exact BitVec.eq_of_toNat_eq (by rw [h3]; rfl)

theorem isFree_zero : isFree 0#64 = true := by decide

theorem isFree_one : isFree 1#64 = false := by decide

theorem isFree_odd {v : Word} (ho : v.toNat % 2 = 1) (h1 : v ≠ 1#64) : isFree v = true := by
  simp [isFree, ho, h1]

theorem isFree_even {v : Word} (h0 : v ≠ 0#64) (he : v.toNat % 2 = 0) : isFree v = false := by
  simp [isFree, h0, he]

-- The flag of `test eax, eax` for a `bool` result.
theorem nz_bool (b : Bool) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result
      ((BitVec.ofNat 64 b.toNat).take 32 &&& (BitVec.ofNat 64 b.toNat).take 32) f) = b := by
  cases b <;> simp [CondCode.interp, StatusFlags.from_result] <;> decide

-- The depth `len - 1 - c` in `rcx`.
theorem depth {L c : Nat} (hc : c < L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 L - BitVec.ofNat 64 c + -1#64).toNat = L - 1 - c := by
  rw [sub_of (Nat.le_of_lt hc), ofNat_pred (by omega), toNat_small (by omega)]
  omega

-- The address of the local `urgentToDup`.
theorem slot_addr' {t : MachineData} (hb : Base s ra t) :
    t.regs.rsp.toBitVec + 8#64 = rsp s - 72#64 := by
  rw [hb.rsp]; bv_omega

theorem isSome_slot' {t : MachineData} (hpre : Pre loopF loopA s) (hb : Base s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome := by
  rw [slot_addr' hb]
  exact Mem.Mapped.loadInt_isSome hb.fm.toMid.map
    (Or.inl (by simpa only [Mem.Blocks.Inside, or_false] using slot_in hpre))

-- The call of `isSpilled` on `r12` in the scan.
theorem scan_spill {T d u : Nat} {t c t' : MachineData} (hpre : Pre loopF loopA s)
    (h : Scan s ra T d u t) (hp : Post isSpilledF isSpilledR c t')
    (hag : (mod isSpilledF c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s) (hbp : c.regs.rbp = t.regs.rbp)
    (hbx : c.regs.rbx = t.regs.rbx) (h12 : c.regs.r12 = t.regs.r12) (h13 : c.regs.r13 = t.regs.r13)
    (h14 : c.regs.r14 = t.regs.r14) (h15 : c.regs.r15 = t.regs.r15)
    (hsi : rsi c = t.regs.r12.toBitVec) :
    Scan s ra T d u t' ∧ st' s t' = st' s t ∧ t'.regs.r12 = t.regs.r12
      ∧ t'.regs.rax.toBitVec = BitVec.ofNat 64 (isSpilled (env s) t.regs.r12.toBitVec).toNat := by
  obtain ⟨hr, hst⟩ := isSpilled_post hpre h.1 hp hc hdi
  rw [hsi] at hr
  exact ⟨h.call (by decide) hpre hp hag hc hsp hdi hbp hbx h13 h14 h15 hst, hst,
    (call_regs hag).2.1.trans h12, hr⟩

-- The call of `shallowestCopyPosition` on `r12` in the scan.
theorem scan_copy {T d u : Nat} {t c t' : MachineData} (hpre : Pre loopF loopA s)
    (h : Scan s ra T d u t) (hp : Post shallowestCopyF shallowestCopyR c t')
    (hag : (mod shallowestCopyF c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s) (hbp : c.regs.rbp = t.regs.rbp)
    (hbx : c.regs.rbx = t.regs.rbx) (h12 : c.regs.r12 = t.regs.r12) (h13 : c.regs.r13 = t.regs.r13)
    (h14 : c.regs.r14 = t.regs.r14) (h15 : c.regs.r15 = t.regs.r15)
    (hsi : rsi c = t.regs.r12.toBitVec) :
    Scan s ra T d u t' ∧ st' s t' = st' s t ∧ t'.regs.r12 = t.regs.r12
      ∧ t'.regs.rax.toBitVec = encOpt (shallowestCopyPosition (st' s t) t.regs.r12.toBitVec) := by
  obtain ⟨hr, hst⟩ := shallowestCopy_post hp hc hdi
  rw [hsi] at hr
  exact ⟨h.call (by decide) hpre hp hag hc hsp hdi hbp hbx h13 h14 h15 hst, hst,
    (call_regs hag).2.1.trans h12, hr⟩

-- `At107` for a state literal with the frame of `x`. See `scan_mk`.
theorem at107_mk {c k : Nat} {x : MachineData} (h : Base s ra x) (hm : dm = x.dmem)
    (h6 : a6 = x.regs.rsp) (h7 : a7 = x.regs.rbp) (hc : a0.toBitVec = BitVec.ofNat 64 c)
    (hk : a3.toBitVec - 16#64 = BitVec.ofNat 64 k) (hr : R0 s = .error (.blocked c k)) :
    At107 s ra
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, dm⟩ := by
  subst hm h6 h7
  exact ⟨⟨h.fm, h.rsp, h.rbp⟩, c, k, hc, hk, hr⟩

-- `At73` after the store of `w` to the local `urgentToDup`. See `scan_mk`.
theorem at73_slot {T d u u' : Nat} {x : MachineData} {w : Word} (hpre : Pre loopF loopA s)
    (h : Scan s ra T d u x) (hm : dm = x.dmem.storeInt (x.regs.rsp.toBitVec + 8#64) 8 w.toInt)
    (hw : w = encU (env s).n u') (hu : u' ≤ (env s).n)
    (h6 : a6 = x.regs.rsp) (h7 : a7 = x.regs.rbp) (h1 : a1 = x.regs.rbx) (h13 : a13 = x.regs.r13)
    (h14 : a14 = x.regs.r14) (h15 : a15 = x.regs.r15)
    (hstep : step (env s) (st' s x) T
      = (urgentFrom (env s) (st' s x) T (d + 1) u').bind (afterUrgent (env s) (st' s x) T)) :
    At73 s ra
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, dm⟩
      ∧ st' s
          ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, dm⟩
        = st' s x := by
  obtain ⟨hb, h13', h15', h14', hbx', -, -, hd, hctx, hpd⟩ := h
  subst hm h6 h7 h1 h13 h14 h15
  obtain ⟨hfm, hst⟩ := Fm.slot hpre hb.fm w.toInt
  rw [slot_addr' hb]
  have hst' : st' s ⟨⟨a0, x.regs.rbx, a2, a3, a4, a5, x.regs.rsp, x.regs.rbp, a8, a9, a10, a11,
      a12, x.regs.r13, x.regs.r14, x.regs.r15⟩, z, f, x.dmem.storeInt (rsp s - 72#64) 8 w.toInt⟩
      = st' s x := hst
  refine ⟨⟨T, d, u', ⟨⟨hfm, hb.rsp, hb.rbp⟩, h13', ?_, h14', hbx', ?_, hu, hd, ?_, ?_⟩, ?_⟩,
    hst'⟩
  · rw [hst']; exact h15'
  · show rd (x.dmem.storeInt (rsp s - 72#64) 8 w.toInt) (rsp s - 72#64) = _
    rw [rd_store_same _ rfl, BitVec.ofInt_toInt, hw]
  · rw [hst']; exact hctx
  · rw [hst']; exact hpd
  · rw [hst']; exact hstep

-- The variant from `.LB100` to `.LB73`.
theorem v73_lt {t y : MachineData} (hst : st' s y = st' s t)
    (h14 : y.regs.r14.toBitVec = t.regs.r14.toBitVec)
    (hbx : y.regs.rbx.toBitVec = t.regs.rbx.toBitVec) : V s ".LB73" y < V s ".LB100" t := by
  simp only [V, outer, hst, h14, hbx]
  omega

-- `v73_lt` for a state literal with the memory of `x`. See `scan_mk`.
theorem v73_mk {t x : MachineData} (hm : dm = x.dmem) (hst : st' s x = st' s t)
    (h14 : a14.toBitVec = t.regs.r14.toBitVec) (hbx : a1.toBitVec = t.regs.rbx.toBitVec) :
    V s ".LB73"
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, dm⟩
      < V s ".LB100" t := by
  subst hm
  exact v73_lt hst h14 hbx

-- The argument of `isSpilled` is the target word of `d`.
theorem spill_pre {c t : MachineData} {d : Nat} (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) (hd : d < (env s).n)
    (hv : (env s).target[d]! = rsi c) : isSpilledA c := by
  refine ⟨d, ?_, ?_⟩ <;> rw [env_call hpre hb hc hdi]
  · exact hd
  · exact hv

-- The `cmove` of `.LB100`: `urgentToDup := d` if it is none.
theorem slot_sel {T d u : Nat} {y : MachineData} {r : StatusFlags.from_result.Remaining}
    (h : Scan s ra T d u y) :
    (if CondCode.z.interp (StatusFlags.from_result
          (rd y.dmem (y.regs.rsp.toBitVec + 8#64) - 18446744073709551615#64) r) = true
      then y.regs.rbx.toBitVec else rd y.dmem (y.regs.rsp.toBitVec + 8#64))
      = encU (env s).n (if u = (env s).n then d else u) := by
  have hn := h.n_le
  have hun := h.2.2.2.2.2.2.1
  have hd := h.2.2.2.2.2.2.2.1
  have hsl : rd y.dmem (rsp s - 72#64) = encU (env s).n u := h.2.2.2.2.2.1
  rw [Kit.z_sub, slot_addr' h.1, hsl, h.2.2.2.2.1,
    show (18446744073709551615#64 : Word) = -1#64 by decide]
  by_cases hu : u = (env s).n
  · rw [ite_eq_left (beq_iff_eq.mpr ((encU_m1 hn hun).mpr hu)), ite_eq_left hu, encU,
      ite_eq_right (by omega)]
  · rw [ite_eq_right (by rw [beq_iff_eq, encU_m1 hn hun]; exact hu), ite_eq_right hu]

end

variable [Host] [FunDecls] {s : MachineData} {ra : Int64}

-- `positionOf d`: a bound slot goes to `.LB73`; else a free target word goes to
-- `.LB73`, and a word that is not free goes to `.LB100`.
theorem lb70 (hpos : Spec "positionOf" positionOfF positionOfA positionOfR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB70") := by
  loop_case
  intro t ht
  kvcgen64 [hpos]
  all_goals try bbu_norm at *
  all_goals
    obtain ⟨T, d, u, hsc, hstep⟩ := (ht : At70 s ra t)
    have hn : (env s).n ≤ 1024 := hsc.n_le
    have hd : d < (env s).n := hsc.2.2.2.2.2.2.2.1
  case vc1 => rw [hsc.1.rsp]; exact hsc.1.fm.toMid.call_isSome (k := 80) (by decide) hpre
  case vc2 => exact Kit.Fm.pre (k := 80) (by decide) hpre hsc.1.fm rfl hsc.1.rsp hsc.1.rbp trivial
  all_goals
    have hp := ‹Post positionOfF positionOfR _ _›
    have hag := ‹(mod positionOfF _).Agree _ _›
    obtain ⟨hsx, hstx, hrax⟩ :=
      scan_pos hpre hsc hp hag rfl rfl hsc.1.rbp rfl rfl rfl rfl rfl rfl
    have e1 := congrArg BitVec.toNat (hsx.2.2.2.1.trans hsc.2.2.2.1.symm)
    have e2 := congrArg BitVec.toNat (hsx.2.2.2.2.1.trans hsc.2.2.2.2.1.symm)
    have e3 := congrArg St.pendingGenerations hstx
    simp only [st'] at e3
  case vc3 =>
    have hz := (by with_reducible assumption :
      CondCode.nz.interp (StatusFlags.from_result (_ - 18446744073709551615#64) _) = true)
    rw [Kit.nz_sub, hrax] at hz
    loop_goto
    · exact stack_mk hsx.1.rsp
    · show At73 s ra _
      exact at73_mk hsx rfl rfl rfl rfl rfl rfl rfl
        (by rw [hstx, hstep, uf_skip hd (Or.inl (some_of_enc hz))])
    · simp only [V, outer, st', e1, e2, e3]
      omega
  case vc4 =>
    rw [hsx.1.rbp]; exact hsx.1.fm.wf.word_isSome hsx.1.fm.wf.mapped (k := 4) (by decide)
  case vc5 => exact tgt_some hpre hsx.1 hsx.2.2.2.2.1 hd
  all_goals
    have hv := tgt_word hpre hsx.1 hsx.2.2.2.2.1 hd
    have hpn : positionOf (st' s t) d = none := by
      have hz := (by with_reducible assumption :
        CondCode.nz.interp (StatusFlags.from_result (_ - 18446744073709551615#64) _) = false)
      rw [Kit.nz_sub, hrax] at hz
      exact none_of_enc (fun p hp => by have := positionOf_some hp; have := hsc.len_le; omega) hz
  case vc6 =>
    have hz := (by with_reducible assumption :
      CondCode.z.interp (StatusFlags.from_result (rd _ _ &&& rd _ _) _) = true)
    rw [Kit.z_test, hv, beq_iff_eq] at hz
    loop_goto
    · exact stack_mk hsx.1.rsp
    · show At73 s ra _
      exact at73_mk hsx rfl rfl rfl rfl rfl rfl rfl
        (by rw [hstx, hstep, uf_skip hd (Or.inr (Or.inl (by
          rw [hz, show isFree 0 = true by decide, Bool.true_or])))])
    · simp only [V, outer, st', e1, e2, e3]
      omega
  all_goals
    have h0 := (by with_reducible assumption :
      CondCode.z.interp (StatusFlags.from_result (rd _ _ &&& rd _ _) _) = false)
    rw [Kit.z_test, hv, beq_eq_false_iff_ne] at h0
    have he := (by with_reducible assumption :
      CondCode.z.interp (StatusFlags.from_result (BitVec.take _ 8 &&& 1#8) _) = _)
    rw [z_odd, hv] at he
  case vc7 =>
    rw [beq_iff_eq] at he
    loop_goto
    · exact stack_mk hsx.1.rsp
    · show At100 s ra _
      exact at100_mk hsx rfl rfl rfl rfl rfl rfl rfl (by rw [hstx]; exact hstep) hv
        (by rw [hstx]; exact hpn) (isFree_even h0 he)
    · simp only [V, outer, st', e1, e2, e3]
      omega
  all_goals
    rw [beq_eq_false_iff_ne] at he
    have h1 := (by with_reducible assumption :
      CondCode.nz.interp (StatusFlags.from_result (_ - 1#64) _) = _)
    rw [Kit.nz_sub, hv] at h1
  case vc8 =>
    rw [Bool.not_eq_true', beq_eq_false_iff_ne] at h1
    loop_goto
    · exact stack_mk hsx.1.rsp
    · show At73 s ra _
      exact at73_mk hsx rfl rfl rfl rfl rfl rfl rfl
        (by rw [hstx, hstep, uf_skip hd (Or.inr (Or.inl (by
          rw [isFree_odd (by omega) h1, Bool.true_or])))])
    · simp only [V, outer, st', e1, e2, e3]
      omega
  case vc9 =>
    rw [Bool.not_eq_false', beq_iff_eq] at h1
    show At100 s ra _
    exact at100_mk hsx rfl rfl rfl rfl rfl rfl rfl (by rw [hstx]; exact hstep) hv
      (by rw [hstx]; exact hpn) (by rw [h1]; exact isFree_one)
  case vc10 =>
    left
    simp only [V, outer, st', e1, e2, e3]
    omega

-- `isSpilled` and `shallowestCopyPosition` of the target word of `d`: a copy out of reach
-- goes to `.LB107`; a copy at depth 16 that is not at `T` sets `urgentToDup` to `d` if it
-- is none; then `.LB73`.
theorem lb100 (hspill : Spec "isSpilled" isSpilledF isSpilledA isSpilledR)
    (hcopy : Spec "shallowestCopyPosition" shallowestCopyF shallowestCopyA shallowestCopyR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB100") := by
  loop_case
  intro t ht
  kvcgen64 [hspill, hcopy]
  all_goals try bbu_norm at *
  all_goals
    obtain ⟨T, d, u, hsc, hstep, h12, hpn, hfr⟩ := (ht : At100 s ra t)
    have hn : (env s).n ≤ 1024 := hsc.n_le
    have hd : d < (env s).n := hsc.2.2.2.2.2.2.2.1
    have e14 := hsc.2.2.2.1
    have ebx := hsc.2.2.2.2.1
  case vc1 => rw [hsc.1.rsp]; exact hsc.1.fm.toMid.call_isSome (k := 80) (by decide) hpre
  case vc2 =>
    exact Kit.Fm.pre (k := 80) (by decide) hpre hsc.1.fm rfl hsc.1.rsp hsc.1.rbp
      (spill_pre hpre hsc.1 rfl hsc.1.rbp hd h12.symm)
  all_goals
    have hp := ‹Post isSpilledF isSpilledR _ _›
    obtain ⟨hsx, hstx, h12x, hraxx⟩ :=
      scan_spill hpre hsc hp ‹_› rfl rfl hsc.1.rbp rfl rfl rfl rfl rfl rfl rfl
    have hs := (by with_reducible assumption :
      CondCode.nz.interp (StatusFlags.from_result (BitVec.take _ 32 &&& _) _) = _)
    rw [hraxx, nz_bool, h12] at hs
  case vc3 =>
    loop_goto
    · exact stack_mk hsx.1.rsp
    · show At73 s ra _
      exact at73_mk hsx rfl rfl rfl rfl rfl rfl rfl
        (by rw [hstx, hstep, uf_skip hd (Or.inr (Or.inl (by rw [hfr, hs]; rfl)))])
    · exact Or.inl (v73_lt hstx (hsx.2.2.2.1.trans e14.symm) (hsx.2.2.2.2.1.trans ebx.symm))
  case vc4 => rw [hsx.1.rsp]; exact hsx.1.fm.toMid.call_isSome (k := 80) (by decide) hpre
  case vc5 => exact Kit.Fm.pre (k := 80) (by decide) hpre hsx.1.fm rfl hsx.1.rsp hsx.1.rbp trivial
  all_goals
    have hp2 := ‹Post shallowestCopyF shallowestCopyR _ _›
    obtain ⟨hsy, hsty, -, hraxy⟩ :=
      scan_copy hpre hsx hp2 ‹_› rfl rfl hsx.1.rbp rfl rfl rfl rfl rfl rfl rfl
    rw [h12x, h12, hstx] at hraxy
    rw [hstx] at hsty
    have hlen := hsy.len_le
    rw [hsty] at hlen
    have hsk : (isFree (env s).target[d]! || isSpilled (env s) (env s).target[d]!) = false := by
      rw [hfr, hs]; rfl
    have y14 := hsy.2.2.2.1.trans e14.symm
    have ybx := hsy.2.2.2.2.1.trans ebx.symm
    have hz := (by with_reducible assumption :
      CondCode.z.interp (StatusFlags.from_result (_ - 18446744073709551615#64) _) = _)
    rw [Kit.z_sub, hraxy] at hz
  case vc6 =>
    have hnone := none_of_enc (fun p hp => Nat.lt_of_lt_of_le (shallowestCopy_lt hp) hlen)
      (by rw [hz]; rfl)
    loop_goto
    · exact stack_mk hsy.1.rsp
    · show At73 s ra _
      exact at73_mk hsy rfl rfl rfl rfl rfl rfl rfl
        (by rw [hsty, hstep, uf_skip hd (Or.inr (Or.inr hnone))])
    · exact Or.inl (v73_lt hsty y14 ybx)
  all_goals
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (some_of_enc (by rw [hz]; rfl))
    have hcl := shallowestCopy_lt hc
    have hraxc : _ = BitVec.ofNat 64 c := hraxy.trans (by rw [hc]; rfl)
    have h15y := hsy.2.2.1
    rw [hsty] at h15y
    have hctx := hsc.2.2.2.2.2.2.2.2.1
    have hT := (ctx_bounds hctx).2.2.1
    have ha := (by with_reducible assumption : CondCode.a.interp _ = _)
    rw [Kit.a_sub_imm _ _ (by decide), h15y, hraxc, depth hcl (by omega)] at ha
  case vc7 =>
    simp only [decide_eq_true_eq] at ha
    loop_goto
    · exact stack_mk hsy.1.rsp
    · show At107 s ra _
      refine at107_mk (k := (st' s t).len - c - 16) hsy.1 rfl rfl rfl hraxc ?_ ?_
      · dsimp only
        rw [h15y, hraxc, sub_of (Nat.le_of_lt hcl), sub_of (by omega)]
      · apply iter_err
        have := ctx_iter hctx
        rwa [hstep, uf_far hd hpn hsk hc (by unfold MAX_DUP_DEPTH; omega),
          show (st' s t).len - 1 - c - MAX_DUP_DEPTH = (st' s t).len - c - 16 by
            unfold MAX_DUP_DEPTH; omega] at this
    · left; simp only [V]; omega
  all_goals
    simp only [decide_eq_false_iff_not, Nat.not_lt] at ha
    rw [uf_near hd hpn hsk hc (by unfold MAX_DUP_DEPTH; omega)] at hstep
    have h16 := (by with_reducible assumption :
      CondCode.nz.interp (StatusFlags.from_result (_ - _ - 16#64) _) = _)
    rw [Kit.nz_sub, h15y, hraxc, sub_of (Nat.le_of_lt hcl)] at h16
  case vc8 =>
    have hne : (st' s t).len - c ≠ 16 := fun h => by rw [h] at h16; exact absurd h16 (by decide)
    rw [ite_eq_right (fun h => by unfold MAX_DUP_DEPTH at h; omega)] at hstep
    loop_goto
    · exact stack_mk hsy.1.rsp
    · show At73 s ra _
      exact at73_mk hsy rfl rfl rfl rfl rfl rfl rfl (by rw [hsty, hstep])
    · exact Or.inl (v73_mk rfl hsty y14 ybx)
  case vc10 => exact isSome_slot' hpre hsy.1
  case vc11 => exact isSome_slot' hpre hsy.1
  all_goals
    simp only [Bool.not_eq_false', beq_iff_eq] at h16
    have he16 := ofNat_inj64 (by omega) (by decide) h16
    have hzT := (by with_reducible assumption :
      CondCode.z.interp (StatusFlags.from_result (_ - UInt64.toBitVec _) _) = _)
    rw [Kit.z_sub, hraxc, hsy.2.2.2.1] at hzT
  case vc9 =>
    rw [beq_iff_eq] at hzT
    have hcT := ofNat_inj64 (by omega) (by omega) hzT
    rw [ite_eq_right (fun h => h.2.1 hcT)] at hstep
    loop_goto
    · exact stack_mk hsy.1.rsp
    · show At73 s ra _
      exact at73_mk hsy rfl rfl rfl rfl rfl rfl rfl (by rw [hsty, hstep])
    · exact Or.inl (v73_mk rfl hsty y14 ybx)
  case vc12 =>
    rw [beq_eq_false_iff_ne] at hzT
    have hcT : c ≠ T := fun h => hzT (by rw [h])
    have hA : ((st' s t).len - 1 - c = MAX_DUP_DEPTH) = True :=
      eq_true (by unfold MAX_DUP_DEPTH; omega)
    simp only [hA, ne_eq, hcT, not_false_eq_true, true_and] at hstep
    have hun := hsc.2.2.2.2.2.2.1
    loop_goto
    · exact stack_mk hsy.1.rsp
    · show At73 s ra _
      exact (at73_slot hpre hsy rfl (slot_sel hsy) (by split <;> omega) rfl rfl rfl rfl rfl rfl
        (by rw [hsty, hstep])).1
    · refine Or.inl (v73_lt ?_ y14 ybx)
      exact (at73_slot hpre hsy rfl (slot_sel hsy) (by split <;> omega) rfl rfl rfl rfl rfl rfl
        (by rw [hsty, hstep])).2.trans hsty

-- The next `d`: `.LB106` at `n`, else `.LB70`.
theorem lb73 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB73") := by
  loop_case
  intro t ht
  kvcgen64
  all_goals try bbu_norm
  all_goals
    obtain ⟨T, d, u, hsc, hstep⟩ := (ht : At73 s ra t)
    have hn : (env s).n ≤ 1024 := hsc.n_le
    have hdn : d < (env s).n := hsc.2.2.2.2.2.2.2.1
    have hbx1 : 1#64 + t.regs.rbx.toBitVec = BitVec.ofNat 64 (d + 1) := by
      rw [hsc.2.2.2.2.1, BitVec.ofNat_add, BitVec.add_comm]
  case vc1 =>
    rename_i hz
    rw [Kit.z_sub, beq_iff_eq, hbx1, hsc.2.1] at hz
    have hd1 : d + 1 = (env s).n := ofNat_inj64 (by omega) (by omega) hz
    obtain ⟨hb, h13, h15, h14, -, hsl, hun, -, hctx, hpd⟩ := hsc
    loop_goto
    · exact stack_mk hb.rsp
    · show At106 s ra _
      refine ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, h13, h15, T, u, h14, hsl, hun, hctx, hpd, ?_⟩
      rw [hstep, hd1, uf_end]; rfl
    · simp only [V, outer, st']
      omega
  case vc2 =>
    rename_i hz
    rw [Kit.z_sub, beq_eq_false_iff_ne, hbx1, hsc.2.1] at hz
    have hd1 : d + 1 < (env s).n := by
      have : d + 1 ≠ (env s).n := fun h => hz (by rw [h])
      omega
    show At70 s ra _
    exact ⟨T, d + 1, u, scan_mk hsc rfl rfl rfl rfl rfl rfl hbx1 hd1, hstep⟩
  case vc3 =>
    left
    simp only [V, outer, st']
    rw [hbx1, hsc.2.2.2.2.1, toNat_small (show d + 1 < 2 ^ 64 by omega),
      toNat_small (show d < 2 ^ 64 by omega)]
    omega

end Loop

end Bbu
