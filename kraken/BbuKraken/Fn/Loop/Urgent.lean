import BbuKraken.Fn.Loop.Machine
import BbuKraken.Fn.Loop.Model

/-!
The `urgentToDup` scan of `buildBottomUp`: `.LB73` (the next `offset`) and `.LB66` (the
slot bound for `offset`, the kind of its target slot, `isSpilled` and
`shallowestCopyPosition` of it).
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

/- A state literal of the scan at `d'`, with the fields of `t` but `rbx`. Each field is a
variable, so the kernel does not unfold the literal. -/
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

-- The address of the target word of `offset`.
theorem tgt_addr {d : Nat} {x : MachineData} (hb : Base s ra x)
    (hbx : x.regs.rbx.toBitVec = BitVec.ofNat 64 d) :
    rd x.dmem (x.regs.rbp.toBitVec + 32#64) + x.regs.rbx.toBitVec * 8#64
      = wordAt (tgtOf x.dmem (rdi s)) d := by
  rw [hb.rbp, hbx]
  show tgtOf x.dmem (rdi s) + _ = tgtOf x.dmem (rdi s) + BitVec.ofNat 64 (8 * d)
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

-- The target slot of `offset` is the target word of `offset`.
theorem tgt_word {d : Nat} {x : MachineData} (hpre : Pre loopF loopA s) (hb : Base s ra x)
    (hbx : x.regs.rbx.toBitVec = BitVec.ofNat 64 d) (hd : d < (env s).n) :
    StackSlot.ofWord (rd x.dmem (rd x.dmem (x.regs.rbp.toBitVec + 32#64)
      + x.regs.rbx.toBitVec * 8#64)) = (env s).target[d]! := by
  have he := (hb.fm.keeps hpre).1
  have hn : d < nOf x.dmem (rdi s) := by rw [← n_envOf, he]; exact hd
  rw [tgt_addr hb hbx, ← he, target_get hn]

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

-- The byte `k` of a word in memory.
theorem rdb_word {m : Mem 64} {a : Addr} (h : (m.loadInt a 8).isSome) {k : Nat} (hk : k < 8) :
    (m.loadInt (a + BitVec.ofNat 64 k) 1).isSome
      ∧ BitVec.ofInt 8 (m.loadInt (a + BitVec.ofNat 64 k) 1).get!
        = (rd m a).extractLsb' (8 * k) 8 := by
  simp only [Mem.loadInt, Option.isSome_map] at h
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp h
  have hl := List.allSome_eq_map_some hbs
  have hlen : bs.length = 8 := by simpa using (congrArg List.length hl).symm
  have hk' : k < bs.length := hlen ▸ hk
  have hg : m.get? (a + BitVec.ofNat 64 k) = some bs[k] := by
    have := congrArg (·[k]?) hl
    simp [hk, List.getElem?_eq_getElem hk'] at this; exact this
  rw [Mem.loadInt_one, hg, rd, Mem.loadInt, hbs]
  refine ⟨rfl, ?_⟩
  simp only [Option.map_some, Option.get!_some]
  match bs, hlen with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Int.ofBytes_cons]
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp [Int.ofBytes, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
      omega

-- The bytes 4 and 5 of a slot word: `kind` and `valueOpcode`.
theorem kind_byte {m : Mem 64} {a : Addr} (h : (m.loadInt a 8).isSome) :
    BitVec.ofInt 8 (m.loadInt (a + 4#64) 1).get! = (StackSlot.ofWord (rd m a)).kind :=
  (rdb_word h (k := 4) (by decide)).2

theorem op_byte {m : Mem 64} {a : Addr} (h : (m.loadInt a 8).isSome) :
    BitVec.ofInt 8 (m.loadInt (a + 5#64) 1).get! = (StackSlot.ofWord (rd m a)).valueOpcode :=
  (rdb_word h (k := 5) (by decide)).2

-- The word that `.LB66` builds from the bytes `kind` and `valueOpcode` of `w`.
theorem mask_word (w : Word) :
    ((w &&& 18446742978492891135#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (w.extractLsb' 32 8))).take 8)) <<< 32)
      &&& 18446463698244468735#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (w.extractLsb' 40 8))).take 8)) <<< 40) = w := by
  have c1 : ∀ i (hi : i < 64),
      (18446742978492891135#64)[i] = !(decide (32 ≤ i) && decide (i < 40)) := by
    decide
  have c2 : ∀ i (hi : i < 64),
      (18446463698244468735#64)[i] = !(decide (40 ≤ i) && decide (i < 48)) := by
    decide
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_shiftLeft,
    BitVec.getElem_setWidth, BitVec.take, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    c1 i hi, c2 i hi]
  by_cases h32 : i < 32
  · simp [h32, show i < 40 by omega, show ¬ 40 ≤ i by omega]
  by_cases h40 : i < 40
  · simp [h32, h40, show 32 ≤ i by omega, show i - 32 < 8 by omega, show i - 32 < 32 by omega,
      show i - 32 < 64 by omega, show ¬ 40 ≤ i by omega,
      Nat.add_sub_cancel' (show 32 ≤ i by omega), ← BitVec.getLsbD_eq_getElem]
  by_cases h48 : i < 48
  · simp [h32, h40, h48, show 32 ≤ i by omega, show 40 ≤ i by omega, show i - 40 < 8 by omega,
      show ¬ i - 32 < 8 by omega, show i - 40 < 32 by omega, show i - 40 < 64 by omega,
      Nat.add_sub_cancel' (show 40 ≤ i by omega), ← BitVec.getLsbD_eq_getElem]
  · simp [h32, h40, h48, show ¬ i - 32 < 8 by omega, show ¬ i - 40 < 8 by omega]

theorem mask_rd {m : Mem 64} {a : Addr} (h : (m.loadInt a 8).isSome) :
    ((rd m a &&& 18446742978492891135#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofInt 8 (m.loadInt (a + 4#64) 1).get!))).take 8)) <<< 32)
      &&& 18446463698244468735#64 ||| BitVec.setWidth 64 (BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofInt 8 (m.loadInt (a + 5#64) 1).get!))).take 8)) <<< 40) = rd m a := by
  rw [kind_byte h, op_byte h]
  exact mask_word _

-- `movzbl`: the low byte of the zero extension of a byte.
theorem take_zext (b : BitVec 8) : (BitVec.setWidth 64 (BitVec.setWidth 32 b)).take 8 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth]
  have := b.isLt
  omega

-- `leal -1(%rdx), %ecx` on the zero extension of a byte.
theorem take_pred (b : BitVec 8) : (BitVec.setWidth 64 (BitVec.setWidth 32
    (BitVec.setWidth 64 (BitVec.setWidth 32 b) + -1#64))).take 8 = b - 1#8 := by
  apply BitVec.eq_of_toNat_eq
  have hm : (-1#64 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
  have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
  rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth, hm,
    BitVec.toNat_sub, h1]
  have := b.isLt
  omega

-- `leal -1(%rdx), %ecx; cmpb $1, %cl; jbe` jumps iff the byte is 1 or 2.
theorem be_kind (b : BitVec 8) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result
      ((BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.setWidth 64 (BitVec.setWidth 32 b) + -1#64))).take 8 - 1#8)
      { cf := ((((BitVec.setWidth 64 (BitVec.setWidth 32
            (BitVec.setWidth 64 (BitVec.setWidth 32 b) + -1#64))).take 8 - 1#8).toNat : Int)
          != (((BitVec.setWidth 64 (BitVec.setWidth 32
            (BitVec.setWidth 64 (BitVec.setWidth 32 b) + -1#64))).take 8).toNat : Int) - 1),
        af, of }) = (b == 1#8 || b == 2#8) := by
  have := b.isLt
  have h1 : (b - 1#8).toNat = (b.toNat + 255) % 256 := by
    rw [BitVec.toNat_sub]; show (2 ^ 8 - 1 + b.toNat) % 2 ^ 8 = _; omega
  have h2 : (b - 1#8 - 1#8).toNat = (b.toNat + 254) % 256 := by
    rw [BitVec.toNat_sub, h1]; show (2 ^ 8 - 1 + (b.toNat + 255) % 256) % 2 ^ 8 = _; omega
  rw [take_pred, CondCode.interp_be, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq, ← BitVec.toNat_inj, h1, h2]
  show _ ↔ b.toNat = 1 ∨ b.toNat = 2
  rw [show (BitVec.zero 8).toNat = 0 from rfl]
  omega

-- `testb %al, %al` on a byte.
theorem z_test8 (v : BitVec 8) (r : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (v &&& v) r) = (v == 0) := by
  simp [CondCode.interp, StatusFlags.from_result]

-- `testb %al, %cl` on two `set` results.
theorem z_and_bool (a b : Bool) (r : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.ofNat 8 a.toNat &&& BitVec.ofNat 8 b.toNat) r) = !(a && b) := by
  cases a <;> cases b <;> simp [CondCode.interp, StatusFlags.from_result] <;> decide

-- The flag of `test eax, eax` for a `bool` result.
theorem nz_bool (b : Bool) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result
      ((BitVec.ofNat 64 b.toNat).take 32 &&& (BitVec.ofNat 64 b.toNat).take 32) f) = b := by
  cases b <;> simp [CondCode.interp, StatusFlags.from_result] <;> decide

-- A result `-1` is none for a result that is less than 1024.
theorem none_of_enc {o : Option Nat} (h : ∀ p, o = some p → p < 1024)
    (hz : (encOpt o == 18446744073709551615#64) = true) : o = none := by
  cases o with
  | none => rfl
  | some p =>
    have hp := h p rfl
    simp only [encOpt, beq_iff_eq] at hz
    have := ofNat_inj64 (by omega) (by decide) hz
    omega

-- The depth `len - 1 - c` in `rdx`.
theorem depth {L c : Nat} (hc : c < L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 L - BitVec.ofNat 64 c + -1#64).toNat = L - 1 - c := by
  rw [sub_of (Nat.le_of_lt hc), ofNat_pred (by omega), toNat_small (by omega)]
  omega

-- The `testb` of `.LB66`: the copy is at the maximum depth and is not at `offset`.
theorem near_test {L c T : Nat} (hc : c < L) (hL : L ≤ 1024) (hT : T ≤ 1024) :
    (!(!(BitVec.ofNat 64 c == BitVec.ofNat 64 T)
      && (BitVec.ofNat 64 L - BitVec.ofNat 64 c + -1#64 == 15#64)))
      = !decide (L - 1 - c = MAX_DUP_DEPTH ∧ c ≠ T) := by
  have h1 : (BitVec.ofNat 64 c == BitVec.ofNat 64 T) = decide (c = T) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨ofNat_inj64 (by omega) (by omega), fun h => h ▸ rfl⟩
  have h2 : (BitVec.ofNat 64 L - BitVec.ofNat 64 c + -1#64 == 15#64)
      = decide (L - 1 - c = MAX_DUP_DEPTH) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, depth hc (by omega)]
    exact Iff.rfl
  rw [h1, h2]
  by_cases a : L - 1 - c = MAX_DUP_DEPTH <;> by_cases b : c = T <;> simp [a, b]

-- The address of the local `urgentToDup`.
theorem slot_addr' {t : MachineData} (hb : Base s ra t) :
    t.regs.rsp.toBitVec + 8#64 = rsp s - 72#64 := by
  rw [hb.rsp]; bv_omega

theorem isSome_slot' {t : MachineData} (hpre : Pre loopF loopA s) (hb : Base s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome := by
  rw [slot_addr' hb]
  exact Mem.Mapped.loadInt_isSome hb.fm.toMid.map
    (Or.inl (by simpa only [Mem.Blocks.Inside, or_false] using slot_in hpre))

-- `At103` for a state literal with the frame of `x`. See `scan_mk`.
theorem at103_mk {c k : Nat} {x : MachineData} (h : Base s ra x) (hm : dm = x.dmem)
    (h6 : a6 = x.regs.rsp) (h7 : a7 = x.regs.rbp) (hc : a0.toBitVec = BitVec.ofNat 64 c)
    (hk : a2.toBitVec - 16#64 = BitVec.ofNat 64 k) (hr : R0 s = .error (.blocked c k)) :
    At103 s ra
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

-- The variant from `.LB66` to `.LB73`.
theorem v73_lt {t y : MachineData} (hst : st' s y = st' s t)
    (h14 : y.regs.r14.toBitVec = t.regs.r14.toBitVec)
    (hbx : y.regs.rbx.toBitVec = t.regs.rbx.toBitVec) : V s ".LB73" y < V s ".LB66" t := by
  simp only [V, outer, hst, h14, hbx]
  omega

-- `v73_lt` for a state literal with the memory of `x`. See `scan_mk`.
theorem v73_mk {t x : MachineData} (hm : dm = x.dmem) (hst : st' s x = st' s t)
    (h14 : a14.toBitVec = t.regs.r14.toBitVec) (hbx : a1.toBitVec = t.regs.rbx.toBitVec) :
    V s ".LB73"
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, dm⟩
      < V s ".LB66" t := by
  subst hm
  exact v73_lt hst h14 hbx

-- The slot tests of `.LB66`: `kind - 1 ≤ 1` and `valueOpcode = Const`.
theorem skip_kind {x : StackSlot} (e : Env) (h : (x.kind == 1#8 || x.kind == 2#8) = true) :
    (isJunk x || canBeFreelyGenerated x || isSpilled e x) = true := by
  simp only [isJunk, canBeFreelyGenerated, Junk, FunctionCallReturnLabel, Bool.or_eq_true] at h ⊢
  rcases h with h | h <;> simp [h]

theorem skip_op {x : StackSlot} (e : Env) (h : (x.valueOpcode == 0#8) = true) :
    (isJunk x || canBeFreelyGenerated x || isSpilled e x) = true := by
  simp only [canBeFreelyGenerated, isLiteralValue, Const] at h ⊢
  simp [h]

theorem skip_spill {x : StackSlot} (e : Env) (hk : (x.kind == 1#8 || x.kind == 2#8) = false)
    (ho : (x.valueOpcode == 0#8) = false) :
    (isJunk x || canBeFreelyGenerated x || isSpilled e x) = isSpilled e x := by
  simp only [Bool.or_eq_false_iff] at hk
  have h1 : (x.kind == Junk) = false := hk.1
  have h2 : (x.kind == FunctionCallReturnLabel) = false := hk.2
  have h3 : isLiteralValue x = false := ho
  simp only [isJunk, canBeFreelyGenerated, h1, h2, h3, Bool.false_or]


-- A name for the state after a call.
theorem post_name {G : Nat} {R : MachineData → MachineData → Prop} {c x : MachineData}
    (_ : Post G R c x) : ∃ y, y = x := ⟨x, rfl⟩


-- The `cmove` of `.LB66`: `urgentToDup := offset` if it is none.
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

-- The next `offset`: `.LB102` at `n`, else `.LB66`.
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
    · show At102 s ra _
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
    show At66 s ra _
    exact ⟨T, d + 1, u, scan_mk hsc rfl rfl rfl rfl rfl rfl hbx1 hd1, hstep⟩
  case vc3 =>
    left
    simp only [V, outer, st']
    rw [hbx1, hsc.2.2.2.2.1, toNat_small (show d + 1 < 2 ^ 64 by omega),
      toNat_small (show d < 2 ^ 64 by omega)]
    omega

-- `offset`: a bound slot, a junk or free slot, a spilled slot, and a slot with no copy go to
-- `.LB73`; a copy out of reach goes to `.LB103`; a copy at depth 15 that is not at
-- `targetOffset` sets `urgentToDup` to `offset` if it is none; then `.LB73`.
theorem lb66 (hspill : Spec "isSpilled" isSpilledF isSpilledA isSpilledR)
    (hcopy : Spec "shallowestCopyPosition" shallowestCopyF shallowestCopyA shallowestCopyR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB66") := by
  loop_case
  intro t ht
  kvcgen64 [hspill, hcopy]
  all_goals try bbu_norm at *
  all_goals
    obtain ⟨T, d, u, hsc, hstep⟩ := (ht : At66 s ra t)
    have hn : (env s).n ≤ 1024 := hsc.n_le
    have hd : d < (env s).n := hsc.2.2.2.2.2.2.2.1
    have e14 := hsc.2.2.2.1
    have ebx := hsc.2.2.2.2.1
    have hnd : d < nOf t.dmem (rdi s) := by rw [← n_envOf, (hsc.1.fm.keeps hpre).1]; exact hd
    have hpa : t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 8264#64
        = wordAt (rdi s) (POS + d) := by
      rw [hsc.1.rbp, ebx, POS_eq]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
  case vc1 =>
    rw [hpa]
    exact hsc.1.fm.wf.word_isSome hsc.1.fm.wf.mapped (by rw [WORDS_eq, POS_eq]; omega)
  case vc2 =>
    rename_i hz
    rw [Kit.nz_sub, hpa] at hz
    have hp : (positionOf (st' s t) d).isSome := by
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hz
      rw [positionOf_stOf hnd, optOf]
      split
      · exact absurd ‹_› hz
      · rfl
    loop_goto
    · exact stack_mk hsc.1.rsp
    · show At73 s ra _
      exact at73_mk hsc rfl rfl rfl rfl rfl rfl rfl (by rw [hstep, uf_skip hd (Or.inl hp)])
    · simp only [V, outer, st']
      omega
  case vc3 =>
    rw [hsc.1.rbp]; exact hsc.1.fm.wf.word_isSome hsc.1.fm.wf.mapped (k := 4) (by decide)
  case vc4 => exact tgt_some hpre hsc.1 ebx hd
  case vc5 => exact (rdb_word (tgt_some hpre hsc.1 ebx hd) (k := 4) (by decide)).1
  case vc6 => exact (rdb_word (tgt_some hpre hsc.1 ebx hd) (k := 5) (by decide)).1
  all_goals
    have hpn : positionOf (st' s t) d = none := by
      have hz := (by with_reducible assumption :
        CondCode.nz.interp (StatusFlags.from_result (_ - 18446744073709551615#64) _) = false)
      rw [Kit.nz_sub, hpa] at hz
      simp only [Bool.not_eq_false', beq_iff_eq] at hz
      rw [positionOf_stOf hnd, optOf]
      split
      · rfl
      · exact absurd hz ‹_›
    have hts := tgt_some hpre hsc.1 ebx hd
    have htw := tgt_word hpre hsc.1 ebx hd
    have hbe := (by with_reducible assumption : CondCode.be.interp _ = _)
    rw [kind_byte hts, be_kind, htw] at hbe
  case vc7 =>
    loop_goto
    · exact stack_mk hsc.1.rsp
    · show At73 s ra _
      exact at73_mk hsc rfl rfl rfl rfl rfl rfl rfl
        (by rw [hstep, uf_skip hd (Or.inr (Or.inl (skip_kind _ hbe)))])
    · simp only [V, outer, st']
      omega
  all_goals
    have hz5 := (by with_reducible assumption :
      CondCode.z.interp (StatusFlags.from_result (BitVec.take _ 8 &&& _) _) = _)
    rw [op_byte hts, take_zext, z_test8, htw] at hz5
  case vc8 =>
    loop_goto
    · exact stack_mk hsc.1.rsp
    · show At73 s ra _
      exact at73_mk hsc rfl rfl rfl rfl rfl rfl rfl
        (by rw [hstep, uf_skip hd (Or.inr (Or.inl (skip_op _ hz5)))])
    · simp only [V, outer, st']
      omega
  case vc9 => decide
  case vc10 => decide
  all_goals
    have hsk := skip_spill (env s) hbe hz5
  case vc11 => rw [hsc.1.rsp]; exact hsc.1.fm.toMid.call_isSome (k := 80) (by decide) hpre
  case vc12 =>
    have he := (hsc.1.fm.keeps hpre).1
    refine Kit.Fm.pre (k := 80) (by decide) hpre hsc.1.fm rfl hsc.1.rsp hsc.1.rbp ⟨d, ?_, ?_⟩
    · show d < (envOf t.dmem t.regs.rbp.toBitVec).n
      rw [hsc.1.rbp, he]; exact hd
    · show (envOf t.dmem t.regs.rbp.toBitVec).target[d]!
        = StackSlot.ofWord ((rd t.dmem _ &&& _ ||| _) &&& _ ||| _)
      rw [mask_rd hts, htw, hsc.1.rbp, he]
  all_goals
    have hp1 := ‹Post isSpilledF isSpilledR _ _›
    have hag1 := ‹(mod isSpilledF _).Agree _ _›
    obtain ⟨x, hx⟩ := post_name hp1
    subst hx
    obtain ⟨hr1, hst1⟩ := isSpilled_post hpre hsc.1 hp1 rfl hsc.1.rbp
    change x.regs.rax.toBitVec = BitVec.ofNat 64 (isSpilled (env s)
      (StackSlot.ofWord ((rd t.dmem _ &&& _ ||| _) &&& _ ||| _))).toNat at hr1
    rw [mask_rd hts, htw] at hr1
    have hsx := hsc.call (by decide) hpre hp1 hag1 rfl rfl hsc.1.rbp rfl rfl rfl rfl rfl hst1
    have x14 := hsx.2.2.2.1.trans e14.symm
    have xbx := hsx.2.2.2.2.1.trans ebx.symm
    have h12 : x.regs.r12.toBitVec = rd t.dmem
        (rd t.dmem (t.regs.rbp.toBitVec + 32#64) + t.regs.rbx.toBitVec * 8#64) :=
      (congrArg UInt64.toBitVec (call_regs hag1).2.1).trans (mask_rd hts)
    have hs := (by with_reducible assumption :
      CondCode.nz.interp (StatusFlags.from_result (BitVec.take _ 32 &&& _) _) = _)
    rw [hr1, nz_bool] at hs
  case vc13 =>
    loop_goto
    · exact stack_mk hsx.1.rsp
    · show At73 s ra _
      exact at73_mk hsx rfl rfl rfl rfl rfl rfl rfl
        (by rw [hst1, hstep, uf_skip hd (Or.inr (Or.inl (by rw [hsk, hs])))])
    · exact Or.inl (v73_lt hst1 x14 xbx)
  case vc14 => rw [hsx.1.rsp]; exact hsx.1.fm.toMid.call_isSome (k := 80) (by decide) hpre
  case vc15 => exact Kit.Fm.pre (k := 80) (by decide) hpre hsx.1.fm rfl hsx.1.rsp hsx.1.rbp trivial
  all_goals
    have hp2 := ‹Post shallowestCopyF shallowestCopyR _ _›
    have hag2 := (by with_reducible assumption : (mod shallowestCopyF _).Agree _ _)
    obtain ⟨y, hy⟩ := post_name hp2
    subst hy
    obtain ⟨hr2, hst2⟩ := shallowestCopy_post (t := x) hp2 rfl hsx.1.rbp
    have hsy := hsx.call (by decide) hpre hp2 hag2 rfl rfl hsx.1.rbp rfl rfl rfl rfl rfl hst2
    change y.regs.rax.toBitVec = encOpt (shallowestCopyPosition (st' s x)
      (StackSlot.ofWord x.regs.r12.toBitVec)) at hr2
    rw [h12, htw, hst1] at hr2
    rw [hst1] at hst2
    have hlen := hsy.len_le
    rw [hst2] at hlen
    have y14 := hsy.2.2.2.1.trans e14.symm
    have ybx := hsy.2.2.2.2.1.trans ebx.symm
    have hz := (by with_reducible assumption :
      CondCode.z.interp (StatusFlags.from_result (_ - 18446744073709551615#64) _) = _)
    rw [Kit.z_sub, hr2] at hz
  case vc16 =>
    have hnone := none_of_enc (fun p hp => Nat.lt_of_lt_of_le (shallowestCopy_lt hp) hlen) hz
    loop_goto
    · exact stack_mk hsy.1.rsp
    · show At73 s ra _
      exact at73_mk hsy rfl rfl rfl rfl rfl rfl rfl
        (by rw [hst2, hstep, uf_skip hd (Or.inr (Or.inr hnone))])
    · exact Or.inl (v73_lt hst2 y14 ybx)
  all_goals
    obtain ⟨p, hcp⟩ : ∃ p, shallowestCopyPosition (st' s t) (env s).target[d]! = some p := by
      cases ho : shallowestCopyPosition (st' s t) (env s).target[d]! with
      | none => rw [ho] at hz; exact absurd hz (by decide)
      | some p => exact ⟨p, rfl⟩
    have hpl := shallowestCopy_lt hcp
    have hraxc : y.regs.rax.toBitVec = BitVec.ofNat 64 p := by rw [hr2, hcp]; rfl
    have h15y : y.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len := by
      rw [← hst2]; exact hsy.2.2.1
    have hf : (isJunk (env s).target[d]! || canBeFreelyGenerated (env s).target[d]!
        || isSpilled (env s) (env s).target[d]!) = false := by rw [hsk, hs]
    have ha := (by with_reducible assumption :
      CondCode.a.interp (StatusFlags.from_result (_ - 15#64) _) = _)
    rw [Kit.a_sub_imm _ _ (by decide), h15y, hraxc, depth hpl (by omega)] at ha
  case vc17 =>
    have hfar : MAX_DUP_DEPTH < (st' s t).len - 1 - p := by
      unfold MAX_DUP_DEPTH; simpa using ha
    have hi := ctx_iter hsc.2.2.2.2.2.2.2.2.1
    rw [hstep, uf_far hd hpn hf hcp hfar] at hi
    loop_goto
    · exact stack_mk hsy.1.rsp
    · show At103 s ra _
      refine at103_mk hsy.1 rfl rfl rfl hraxc ?_ (iter_err hi)
      show y.regs.r15.toBitVec - y.regs.rax.toBitVec - 16#64 = _
      rw [h15y, hraxc, sub_of (by omega), show (16#64 : Word) = BitVec.ofNat 64 16 from rfl,
        sub_of (by unfold MAX_DUP_DEPTH at hfar; omega),
        show (st' s t).len - p - 16 = (st' s t).len - 1 - p - MAX_DUP_DEPTH by
          unfold MAX_DUP_DEPTH; omega]
    · left
      simp only [V]
      omega
  all_goals
    have hnear : (st' s t).len - 1 - p ≤ MAX_DUP_DEPTH := by
      unfold MAX_DUP_DEPTH; simp only [decide_eq_false_iff_not] at ha; omega
    rw [uf_near hd hpn hf hcp hnear] at hstep
    have hT := (ctx_bounds hsc.2.2.2.2.2.2.2.2.1).2.2.1
    have htb := (by with_reducible assumption :
      CondCode.z.interp (StatusFlags.from_result (BitVec.ofNat 8 _ &&& BitVec.ofNat 8 _) _) = _)
    rw [Kit.nz_sub, Kit.z_sub, z_and_bool, hraxc, hsy.2.2.2.1, h15y,
      near_test hpl hlen (by omega)] at htb
  case vc18 =>
    have hif : ¬ ((st' s t).len - 1 - p = MAX_DUP_DEPTH ∧ p ≠ T ∧ u = (env s).n) := by
      intro h
      simp [h.1, h.2.1] at htb
    loop_goto
    · exact stack_mk hsy.1.rsp
    · show At73 s ra _
      exact at73_mk hsy rfl rfl rfl rfl rfl rfl rfl (by rw [hst2, hstep, ite_eq_right hif])
    · exact Or.inl (v73_mk rfl hst2 y14 ybx)
  case vc19 => exact isSome_slot' hpre hsy.1
  case vc20 => exact isSome_slot' hpre hsy.1
  case vc21 =>
    have hab : (st' s t).len - 1 - p = MAX_DUP_DEPTH ∧ p ≠ T := by simpa using htb
    have hif : (if (st' s t).len - 1 - p = MAX_DUP_DEPTH ∧ p ≠ T ∧ u = (env s).n then d else u)
        = (if u = (env s).n then d else u) := by
      by_cases hu : u = (env s).n <;> simp [hab.1, hab.2, hu]
    have hun := hsc.2.2.2.2.2.2.1
    have hu' : (if u = (env s).n then d else u) ≤ (env s).n := by split <;> omega
    have hsy' : step (env s) (st' s y) T = (urgentFrom (env s) (st' s y) T (d + 1)
        (if u = (env s).n then d else u)).bind (afterUrgent (env s) (st' s y) T) := by
      rw [hst2, hstep, hif]
    loop_goto
    · exact stack_mk hsy.1.rsp
    · exact (at73_slot hpre hsy rfl (slot_sel hsy) hu' rfl rfl rfl rfl rfl rfl hsy').1
    · refine Or.inl (v73_lt (Eq.trans ?_ hst2) y14 ybx)
      exact (at73_slot hpre hsy rfl (slot_sel hsy) hu' rfl rfl rfl rfl rfl rfl hsy').2

end Loop

end Bbu
