module

public import BbuKraken.Contracts
import all BbuKraken.Contracts
public import BbuKraken.Kit
import all BbuKraken.Kit

@[expose] public section

/-!
Lemmas for the body of `produce` (`c/bbu/<Names.produce>.S`): the bytes of a word, the model
facts of `emit`, and the local byte at `rsp s - 57`.
-/

namespace Bbu
namespace Produce

/-! ## The bytes of a word -/
theorem natOfBytes (bs : List UInt8) : Int.ofBytes bs = (Nat.ofBytes bs : Int) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [Int.ofBytes_cons, ih, show Nat.ofBytes (b :: bs) = Nat.ofBytes bs * 256 + b.toNat from rfl]
    rw [Int.natCast_add, Int.natCast_mul]; rfl

theorem natOfBytes_lt (bs : List UInt8) : Nat.ofBytes bs < 256 ^ bs.length := by
  have := Int.ofBytes_lt bs
  rw [natOfBytes] at this
  exact Int.ofNat_lt.mp (by rw [Int.natCast_pow]; exact this)

-- The byte `k` of the bytes `bs`.
theorem ofBytes_byte : ∀ (bs : List UInt8) (k : Nat) (hk : k < bs.length),
    Nat.ofBytes bs / 256 ^ k % 256 = bs[k].toNat
  | b :: bs, 0, _ => by
    show (Nat.ofBytes bs * 256 + b.toNat) / 1 % 256 = b.toNat
    have := b.toNat_lt
    omega
  | b :: bs, k + 1, hk => by
    have hk' : k < bs.length := by simp at hk; omega
    have ih := ofBytes_byte bs k hk'
    have := b.toNat_lt
    rw [List.getElem_cons_succ]
    show (Nat.ofBytes bs * 256 + b.toNat) / 256 ^ (k + 1) % 256 = _
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k), ← Nat.div_div_eq_div_mul,
      show (Nat.ofBytes bs * 256 + b.toNat) / 256 = Nat.ofBytes bs by omega]
    exact ih

-- A load of one byte of a mapped word.
theorem load_byte {m : Mem 64} {a : Addr} (h : (m.loadInt a 8).isSome = true) {k : Nat}
    (hk : k < 8) :
    (m.loadInt (a + BitVec.ofNat 64 k) 1).isSome = true
      ∧ BitVec.ofInt 8 (m.loadInt (a + BitVec.ofNat 64 k) 1).get! = (rd m a).extractLsb' (8 * k) 8 := by
  simp only [Mem.loadInt, Option.isSome_map] at h
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp h
  have hl := List.allSome_eq_map_some hbs
  have hlen : bs.length = 8 := by
    have := congrArg List.length hl; simp at this; omega
  have hk' : k < bs.length := by omega
  have hg := congrArg (·[k]?) hl
  simp only [List.getElem?_map, List.getElem?_range hk, List.getElem?_eq_getElem hk',
    Option.map_some, Option.some.injEq] at hg
  have h1 : m.loadBytes (a + BitVec.ofNat 64 k) 1 = some [bs[k]] := by
    simp only [Mem.loadBytes, List.range_one, List.map_cons, List.map_nil,
      BitVec.add_zero, hg, List.allSome, List.mapM_cons, List.mapM_nil, id]
    rfl
  simp only [Mem.loadInt, h1, Option.isSome_some, true_and, Option.map_some,
    Option.get!_some, rd, hbs]
  apply BitVec.eq_of_toNat_eq
  rw [natOfBytes, natOfBytes, BitVec.toNat_ofInt, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt]
  have hlt := natOfBytes_lt bs
  rw [hlen] at hlt
  have hb := ofBytes_byte bs k hk'
  have hbk := bs[k].toNat_lt
  rw [show Nat.ofBytes [bs[k]] = bs[k].toNat by simp [Nat.ofBytes], ← Int.natCast_emod,
    ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show Nat.ofBytes bs < 2 ^ 64 by simpa using hlt), Nat.pow_mul]
  simpa using hb.symm


-- `movzbl` then a byte compare: the low byte of the zero extension.
theorem take_setWidth (x : BitVec 8) : (BitVec.setWidth 64 (BitVec.setWidth 32 x)).take 8 = x := by
  unfold BitVec.take
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have := x.isLt
  omega

-- The byte that a store of one byte writes.
theorem rdb_store_same {m : Mem 64} {a : Addr} (x : BitVec 8) : rdb (m.storeInt a 1 x.toInt) a = x := by
  rw [rdb, Mem.loadInt_storeInt _ _ _ _ (by decide), Option.get!_some]
  exact BitVec.ofInt_ofBytes_toBytes 8 1 rfl x

/-! ## The model -/

section
variable {e : Env} {st : St} {d c : Nat}

-- No copy of `slot` is in reach.
abbrev Far (st : St) (slot : StackSlot) : Prop :=
  ∀ c, shallowestCopyPosition st slot = some c → MAX_DUP_DEPTH < st.len - 1 - c

theorem filter_none {slot : StackSlot} (hf : Far st slot) :
    (shallowestCopyPosition st slot).filter (fun c => st.len - 1 - c ≤ MAX_DUP_DEPTH) = none := by
  cases hc : shallowestCopyPosition st slot with
  | none => rfl
  | some c => have := hf c hc; simp; omega

-- The value at the position that `shallowestCopyPosition` returns.
theorem val_of_copy {slot : StackSlot} (h : shallowestCopyPosition st slot = some c) :
    st.val c = slot := by
  simpa using List.find?_some h

theorem emit_junk (h : isJunk e.target[d]! = true) :
    emit e st d = add st e.target[d]! d (.push e.target[d]!) := by
  simp only [emit, h, ↓reduceIte]

theorem emit_dup (hj : isJunk e.target[d]! = false)
    (hc : shallowestCopyPosition st e.target[d]! = some c) (hb : st.len - 1 - c ≤ MAX_DUP_DEPTH)
    (hl : (e.target[d]!.kind == FunctionReturnLabel) = false) :
    emit e st d = add st e.target[d]! d (.dup (st.len - c)) := by
  have hf : (shallowestCopyPosition st e.target[d]!).filter
      (fun c => st.len - 1 - c ≤ MAX_DUP_DEPTH) = some c := by
    simp only [hc, Option.filter_some, hb, decide_true, ↓reduceIte]
  simp only [emit, hj, Bool.false_eq_true, ↓reduceIte, hf, hl]

theorem emit_push (hj : isJunk e.target[d]! = false) (hf : Far st e.target[d]!)
    (hp : (canBeFreelyGenerated e.target[d]! || isSpilled e e.target[d]!) = true) :
    emit e st d = add st e.target[d]! d (.push e.target[d]!) := by
  simp only [emit, hj, Bool.false_eq_true, ↓reduceIte, filter_none hf, hp]

theorem emit_blocked (hj : isJunk e.target[d]! = false) (hf : Far st e.target[d]!)
    (hp : (canBeFreelyGenerated e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopyPosition st e.target[d]! = some c) :
    emit e st d = .error (.blocked c (st.len - 1 - c - MAX_DUP_DEPTH) st) := by
  have h0 := filter_none hf
  rw [hc] at h0
  simp only [emit, hj, Bool.false_eq_true, ↓reduceIte, hp, hc, h0]

theorem emit_none (hj : isJunk e.target[d]! = false)
    (hp : (canBeFreelyGenerated e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopyPosition st e.target[d]! = none) : emit e st d = .error .assertion := by
  have hf : Far st e.target[d]! := fun c h => absurd (hc.symm.trans h) (by simp)
  have h0 := filter_none hf
  rw [hc] at h0
  simp only [emit, hj, Bool.false_eq_true, ↓reduceIte, hp, hc, h0]

-- The part of `produce` after `emit`.
def tail (d : Nat) (st : St) : M St :=
  if positionOf st d ≠ some (st.len - 1) then .error .assertion
  else .ok { st with pendingGenerations := sizeDec st.pendingGenerations }

theorem produce_eq : produce e st d = (emit e st d).bind (tail d) := rfl

theorem produce_err {x : Err} (h : emit e st d = .error x) : produce e st d = .error x := by
  rw [produce_eq, h]; rfl

theorem tail_bad (h : positionOf st d ≠ some (st.len - 1)) : tail d st = .error .assertion := by
  simp [tail, h]

theorem tail_ok (h : positionOf st d = some (st.len - 1)) :
    tail d st = .ok { st with pendingGenerations := sizeDec st.pendingGenerations } := by
  simp [tail, h]

end
-- The position that `shallowestCopyPosition` returns is on the stack.
theorem copy_lt {st : St} {slot : StackSlot} {c : Nat}
    (h : shallowestCopyPosition st slot = some c) : c < st.len := by
  have := List.mem_of_find?_eq_some h
  simpa using this

/-! ## Flags -/

-- The zero flag of `cmpb`.
theorem z_sub8 (a b : BitVec 8) (r : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a - b) r) = (a == b) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq,
    BitVec.zero_eq]
  constructor <;> intro h <;> bv_omega

/-! ## The frame -/

-- The registers that `produce` saves, in the order of the pushes.
abbrev regs : List Reg64 := [.r15, .r14, .r13, .r12, .rbp, .rbx]

-- The memory of `produce`: the frame of 72 bytes, the saved words and the struct.
abbrev Fm := Kit.Fm 72 regs

section
variable (s : MachineData) (ra : Int64)

-- The offset `d`, its target slot and the copy of the slot.
abbrev dd : Nat := (rsi s).toNat
abbrev sl : StackSlot := (env s).target[(rsi s).toNat]!
abbrev cp : Option Nat := shallowestCopyPosition (st s) (sl s)

-- The memory after the pushes, and the address of the target slot `d`.
abbrev m0 : Mem 64 := Kit.pushes s ra regs
abbrev tw : Addr := wordAt (tgtOf (m0 s ra) (rdi s)) (dd s)
-- The memory after the store of the opcode to the local byte.
abbrev m1 : Mem 64 := (m0 s ra).storeInt (s.regs.rsp.toBitVec - 57#64) 1 (sl s).valueOpcode.toInt

-- The frame.
structure Base (t : MachineData) : Prop where
  fm : Fm s ra t.dmem
  rsp : t.regs.rsp.toBitVec = rsp s - 64#64

-- The struct in `rbx`, `d` in `rbp` and `8 * d` in `r14`.
structure Hold (t : MachineData) : Prop extends Base s ra t where
  rbx : t.regs.rbx.toBitVec = rdi s
  rbp : t.regs.rbp.toBitVec = rsi s
  r14 : t.regs.r14.toBitVec = rsi s * 8#64

-- After `shallowestCopyPosition`: the slot in `r13` and its kind in `r15`.
structure Lp (t : MachineData) : Prop extends Hold s ra t where
  st : stOf t.dmem (rdi s) = st s
  r13 : StackSlot.ofWord t.regs.r13.toBitVec = sl s
  r15 : t.regs.r15.toBitVec.take 8 = (sl s).kind

end

section
variable {s : MachineData} {ra : Int64}

theorem stack_of {t : MachineData} (h : t.regs.rsp.toBitVec = rsp s - 64#64) :
    t.StackAtOrBelow (s.pushRa ra) := by
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, pushRa_rsp, h]
  bv_omega

-- The frame is mapped before the pushes.
theorem map0 (hpre : Pre 72 produceA s) : Mem.Mapped (mod 72 s).mem s.dmem := fun x hx =>
  hx.elim (fun h => hpre.2.1.mapped x (Or.inl h))
    (fun h => hpre.1.mapped x (inside_append.mpr (Or.inl h)))

-- A load from the frame.
theorem fr_ld {m : Mem 64} (hm : Mem.Mapped (mod 72 s).mem m) {a : Addr} {n : Nat}
    (ha : (a - (s.regs.rsp.toBitVec - 72#64)).toNat + n ≤ 72) : (m.loadInt a n).isSome = true :=
  Mem.Mapped.loadInt_isSome hm (Or.inl ha)

-- The memory after the pushes, as `kvcgen64` gives it.
theorem pushes_eq : ((((((Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 8#64) 8 s.regs.r15.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64) 8 s.regs.r14.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.r13.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.r12.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 s.regs.rbx.toBitVec.toInt
    = m0 s ra := rfl

theorem fm0 (hpre : Pre 72 produceA s) : Fm s ra (m0 s ra) := Kit.Fm.init (by decide) hpre

/-! ## The target slot -/

-- The addresses of the frame, as `kvcgen64` gives them.
theorem a64 (x : BitVec 64) :
    x - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 = x - 64#64 := by bv_omega
theorem a57 (x : BitVec 64) : x - 64#64 + 7#64 = x - 57#64 := by bv_omega
theorem a72 (x : BitVec 64) : x - 64#64 - 8#64 = x - 72#64 := by bv_omega

theorem dd_lt (hpre : Pre 72 produceA s) : dd s < nOf (m0 s ra) (rdi s) := by
  rw [(fm0 hpre).n hpre, ← n_envOf]
  exact hpre.2.2.1

theorem tw_slot (hpre : Pre 72 produceA s) : StackSlot.ofWord (rd (m0 s ra) (tw s ra)) = sl s := by
  have := target_get (dd_lt (ra := ra) hpre)
  rw [((fm0 hpre).keeps hpre).1] at this
  exact this.symm

/-! ## The local byte -/

theorem byte_ar (hpre : Pre 72 produceA s) :
    ((s.regs.rsp.toBitVec - 57#64) - (frame 72 s).1).toNat + 1 ≤ (frame 72 s).2 := by
  have hle : 72 ≤ (rsp s).toNat := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle ⊢
  bv_omega

theorem byte_in (hpre : Pre 72 produceA s) :
    Mem.Blocks.Inside (s.regs.rsp.toBitVec - 57#64) 1 [frame 72 s] := Or.inl (byte_ar hpre)

theorem byte_disj (hpre : Pre 72 produceA s) {m : Mem 64} (h : Fm s ra m) :
    Mem.Blocks.Disjoint (writable m (rdi s) ++ readable m (rdi s))
      [(s.regs.rsp.toBitVec - 57#64, 1)] := by
  rw [(h.keeps hpre).2.2, (h.keeps hpre).2.1]
  exact fun x hx hy => hpre.2.1.disj x (Kit.inside_bytes (byte_in hpre) x hy) hx

-- A store to the local byte keeps `Fm` and the model state.
theorem Fm.byte (hpre : Pre 72 produceA s) {m : Mem 64} (h : Fm s ra m) (v : Int) :
    Fm s ra (m.storeInt (s.regs.rsp.toBitVec - 57#64) 1 v)
      ∧ stOf (m.storeInt (s.regs.rsp.toBitVec - 57#64) 1 v) (rdi s) = stOf m (rdi s) := by
  have hle : 72 ≤ (rsp s).toNat := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  have hu : Mem.UnchangedOutside [(s.regs.rsp.toBitVec - 57#64, 1)] m
      (m.storeInt (s.regs.rsp.toBitVec - 57#64) 1 v) :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 1)) _
  have hd := byte_disj hpre h
  refine ⟨⟨h.toMid.store (Or.inl (byte_ar hpre))
    (fun x hx hy => ?_) v, Wf.congr_of_disjoint hu h.wf hd, fun i hi => ?_⟩, stOf_congr hu h.wf hd⟩
  · simp only [Mem.Blocks.Inside, or_false, rsp, Reg64s.get64_rsp] at hx hy
    bv_omega
  · rw [rd_congr hu ?_]
    · exact h.saved i hi
    · intro x hx hy
      simp only [regs, List.length_cons, List.length_nil] at hi
      simp only [Mem.Blocks.Inside, or_false, rsp, Reg64s.get64_rsp] at hx hy
      have : (BitVec.ofNat 64 (8 * i + 16)).toNat = 8 * i + 16 := by
        simp only [BitVec.toNat_ofNat]; omega
      bv_omega

theorem fm1 (hpre : Pre 72 produceA s) : Fm s ra (m1 s ra) := (Fm.byte hpre (fm0 hpre) _).1

theorem st1 (hpre : Pre 72 produceA s) : stOf (m1 s ra) (rdi s) = st s :=
  (Fm.byte hpre (fm0 hpre) _).2.trans (Kit.st_pushes (by decide) hpre)

-- The load of the local byte before the call, and of the return address slot of the call.
theorem byte_isSome (hpre : Pre 72 produceA s) :
    ((m0 s ra).loadInt (s.regs.rsp.toBitVec - 57#64) 1).isSome = true :=
  Mem.Mapped.loadInt_isSome (fm0 hpre).map (Or.inl (byte_ar hpre))

/-! ## The call of `shallowestCopyPosition` -/

-- The state after the call: `Lp`, the copy in `rax` and the opcode in the local byte.
theorem after_copy {c t : MachineData} (hpre : Pre 72 produceA s)
    (hp : Post shallowestCopyF shallowestCopyR c t) (hag : (mod shallowestCopyF c).Agree c t)
    (hc : c.dmem = m1 s ra) (hrsp : c.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 64#64)
    (hrdi : c.regs.rdi.toBitVec = s.regs.rdi.toBitVec)
    (hrsi : c.regs.rsi.toBitVec = rd (m0 s ra) (tw s ra))
    (hrbx : c.regs.rbx.toBitVec = s.regs.rdi.toBitVec)
    (hrbp : c.regs.rbp.toBitVec = s.regs.rsi.toBitVec)
    (hr14 : c.regs.r14.toBitVec = s.regs.rsi.toBitVec * 8#64)
    (hr13 : c.regs.r13.toBitVec = rd (m0 s ra) (tw s ra))
    (hr15 : c.regs.r15.toBitVec = BitVec.setWidth 64 (BitVec.setWidth 32 (sl s).kind)) :
    Lp s ra t ∧ rax t = encOpt (cp s)
      ∧ rdb t.dmem (s.regs.rsp.toBitVec - 57#64) = (sl s).valueOpcode := by
  have hle : 72 ≤ (rsp s).toNat := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  have hrsp' : rsp c = rsp s - BitVec.ofNat 64 64 := by
    simp only [rsp, Reg64s.get64_rsp, hrsp]
  have hrdi' : rdi c = rdi s := by simp only [rdi, Reg64s.get64_rdi, hrdi]
  have h1 := fm1 (ra := ra) hpre
  have hfm : Fm s ra t.dmem := Kit.Fm.call (k := 64) (by decide) (by decide) hpre h1 hc hrsp' hrdi' hp hag
  have hr := fun (q : Reg64) (hq : q ∉ (mod shallowestCopyF c).regs) => hag.reg q hq
  simp only [mod, List.mem_cons, List.not_mem_nil, or_false] at hr
  have e1 := hr .rsp (by decide)
  have e2 := hr .rbx (by decide)
  have e3 := hr .rbp (by decide)
  have e4 := hr .r13 (by decide)
  have e5 := hr .r14 (by decide)
  have e6 := hr .r15 (by decide)
  simp only [Reg64s.get64_rsp, Reg64s.get64_rbx, Reg64s.get64_rbp, Reg64s.get64_r13,
    Reg64s.get64_r14, Reg64s.get64_r15] at e1 e2 e3 e4 e5 e6
  have hst : st c = st s := by
    show stOf c.dmem (rdi c) = _
    rw [hc, hrdi']; exact st1 hpre
  have hsl : slot c = sl s := by
    show StackSlot.ofWord c.regs.rsi.toBitVec = _
    rw [hrsi]; exact tw_slot hpre
  obtain ⟨hax, hst'⟩ := hp.2.2
  rw [hst, hsl] at hax
  rw [hst] at hst'
  -- the local byte stays
  have hu : Mem.UnchangedOutside (frame shallowestCopyF c :: writable s.dmem (rdi s)) (m1 s ra) t.dmem := by
    have := hag.2
    simp only [mod, hc, hrdi', (h1.keeps hpre).2.2] at this
    exact this
  have hb : rdb t.dmem (s.regs.rsp.toBitVec - 57#64) = (sl s).valueOpcode := by
    rw [rdb_congr hu fun x hx hl => ?_, rdb_store_same]
    rcases hl with hl | hl
    · simp only [Mem.Blocks.Inside, or_false, hrsp', shallowestCopyF, rsp, Reg64s.get64_rsp] at hx hl
      bv_omega
    · exact hpre.2.1.disj x (Kit.inside_bytes (byte_in hpre) x hx) (inside_append.mpr (Or.inl hl))
  refine ⟨⟨⟨⟨hfm, ?_⟩, ?_, ?_, ?_⟩, by simpa only [st', hrdi'] using hst', ?_, ?_⟩, hax, hb⟩
  · rw [e1, hrsp]; rfl
  · rw [e2, hrbx]; rfl
  · rw [e3, hrbp]; rfl
  · rw [e5, hr14]; rfl
  · rw [e4, hr13]; exact tw_slot hpre
  · rw [e6, hr15]; exact take_setWidth _

end

/-! ## The branches after the call -/

section
variable {s : MachineData} {ra : Int64}

theorem Lp.mov {t u : MachineData} (h : Lp s ra t) (hd : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) (hbx : u.regs.rbx = t.regs.rbx) (hbp : u.regs.rbp = t.regs.rbp)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14) (h15 : u.regs.r15 = t.regs.r15) :
    Lp s ra u := by
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp only [hd, hsp, hbx, hbp, h13, h14, h15]
  · exact h.fm
  · exact h.rsp
  · exact h.rbx
  · exact h.rbp
  · exact h.r14
  · exact h.st
  · exact h.r13
  · exact h.r15

theorem len_lt : (st s).len < 2 ^ 64 := by
  rw [st, len_stOf]; exact BitVec.isLt _

-- `cmpb $1, r15b`: the slot is junk.
theorem junk_of {t : MachineData} {r : StatusFlags.from_result.Remaining} {b : Bool} (h : Lp s ra t)
    (hz : CondCode.z.interp (StatusFlags.from_result (t.regs.r15.toBitVec.take 8 - 1#8) r) = b) :
    isJunk (sl s) = b := by
  rw [z_sub8, h.r15] at hz; exact hz

-- `cmpq $-1, x`: there is no copy.
theorem cp_isNone {x : Word} {r : StatusFlags.from_result.Remaining} {b : Bool}
    (hx : x = encOpt (cp s))
    (hz : CondCode.z.interp (StatusFlags.from_result (x - 18446744073709551615#64) r) = b) :
    (cp s).isNone = b := by
  rw [Kit.z_sub, hx] at hz
  rw [← hz]
  cases hc : cp s with
  | none => rfl
  | some c =>
    have h1 := copy_lt hc
    have h2 : (st s).len < 2 ^ 64 := len_lt
    simp only [encOpt, Option.isNone_some]
    symm
    rw [beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    omega

-- `cmpq $-1, rax`: there is no copy.
theorem cp_of {t : MachineData} {r : StatusFlags.from_result.Remaining} {b : Bool}
    (hax : rax t = encOpt (cp s))
    (hz : CondCode.z.interp
      (StatusFlags.from_result (t.regs.rax.toBitVec - 18446744073709551615#64) r) = b) :
    (cp s).isNone = b :=
  cp_isNone (by simpa only [rax, Reg64s.get64_rax] using hax) hz

theorem nz_sub8 (a b : BitVec 8) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) r) = !(a == b) := by
  rw [CondCode.interp_nz, ← CondCode.interp_z, z_sub8]

theorem free_eq (slot : StackSlot) : canBeFreelyGenerated slot
    = (isLiteralValue slot || isJunk slot || slot.kind == FunctionCallReturnLabel) := rfl

-- The local byte at `rsp + 7`.
theorem byte_addr {t : MachineData} (h : Base s ra t) :
    t.regs.rsp.toBitVec + 7#64 = rsp s - 57#64 := by
  rw [h.rsp]; bv_omega

theorem byte_ld (hpre : Pre 72 produceA s) {t : MachineData} (h : Base s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 7#64) 1).isSome = true := by
  rw [byte_addr h]
  exact Mem.Mapped.loadInt_isSome h.fm.map (Or.inl (byte_ar hpre))

-- `cmpb $0, 7(rsp)`: the opcode is `Const`.
theorem lit_of {t : MachineData} {r : StatusFlags.from_result.Remaining} {b : Bool} (h : Base s ra t)
    (hb : rdb t.dmem (rsp s - 57#64) = (sl s).valueOpcode)
    (hz : CondCode.z.interp (StatusFlags.from_result
      (BitVec.ofInt 8 (t.dmem.loadInt (t.regs.rsp.toBitVec + 7#64) 1).get! - 0#8) r) = b) :
    isLiteralValue (sl s) = b := by
  rw [z_sub8, byte_addr h] at hz
  change (rdb t.dmem _ == 0#8) = b at hz
  rw [hb] at hz
  exact hz

-- `cmpb $2, r15b`: the slot is a return label.
theorem ret_of {t : MachineData} {r : StatusFlags.from_result.Remaining} {b : Bool} (h : Lp s ra t)
    (hz : CondCode.nz.interp (StatusFlags.from_result (t.regs.r15.toBitVec.take 8 - 2#8) r) = b) :
    ((sl s).kind == FunctionCallReturnLabel) = !b := by
  rw [nz_sub8, h.r15] at hz
  rw [← hz, Bool.not_not]
  rfl
end

/-! ## The calls at `rsp s - 64` -/

section
variable {s : MachineData} {ra : Int64}

-- The return address slot of a call.
theorem ra_ld (hpre : Pre 72 produceA s) {t : MachineData} (h : Base s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true := by
  rw [h.rsp]; exact h.fm.call_isSome (k := 64) (by decide) hpre

-- A callee keeps the registers that it saves.
theorem call_regs {G : Nat} {c t' : MachineData} (hag : (mod G c).Agree c t') :
    t'.regs.rsp = c.regs.rsp ∧ t'.regs.rbx = c.regs.rbx ∧ t'.regs.rbp = c.regs.rbp
      ∧ t'.regs.r12 = c.regs.r12 ∧ t'.regs.r13 = c.regs.r13 ∧ t'.regs.r14 = c.regs.r14
      ∧ t'.regs.r15 = c.regs.r15 := by
  have hr := fun (q : Reg64) (hq : q ∉ (mod G c).regs) => hag.reg q hq
  simp only [mod, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h0 := hr .rsp (by decide)
  have h1 := hr .rbx (by decide)
  have h6 := hr .rbp (by decide)
  have h2 := hr .r12 (by decide)
  have h3 := hr .r13 (by decide)
  have h4 := hr .r14 (by decide)
  have h5 := hr .r15 (by decide)
  simp only [Reg64s.get64_rsp, Reg64s.get64_rbx, Reg64s.get64_rbp, Reg64s.get64_r12,
    Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15] at h0 h1 h2 h3 h4 h5 h6
  exact ⟨UInt64.toBitVec_inj.mp h0, UInt64.toBitVec_inj.mp h1, UInt64.toBitVec_inj.mp h6,
    UInt64.toBitVec_inj.mp h2, UInt64.toBitVec_inj.mp h3, UInt64.toBitVec_inj.mp h4,
    UInt64.toBitVec_inj.mp h5⟩

-- The struct, the environment, the model state and the capacity of a callee.
theorem ctx (hpre : Pre 72 produceA s) {t c : MachineData} (h : Hold s ra t) (hc : c.dmem = t.dmem)
    (hdi : c.regs.rdi.toBitVec = t.regs.rbx.toBitVec) :
    rdi c = rdi s ∧ env c = env s ∧ stOf c.dmem (rdi c) = stOf t.dmem (rdi s) ∧ cap c = cap s := by
  have e1 : rdi c = rdi s := by simp only [rdi, Reg64s.get64_rdi, hdi]; exact h.rbx
  have hk := h.fm.keeps hpre
  refine ⟨e1, ?_, ?_, ?_⟩
  · simp only [env, hc, e1]; exact hk.1
  · rw [hc, e1]
  · simp only [cap, hc, e1]; rw [h.fm.n hpre]

-- A callee keeps `Hold`.
theorem Hold.call {G : Nat} {R : MachineData → MachineData → Prop} {t c t' : MachineData}
    (hG : 64 + G ≤ 72) (hpre : Pre 72 produceA s) (h : Hold s ra t)
    (hp : Post G R c t') (hag : (mod G c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : c.regs.rdi.toBitVec = t.regs.rbx.toBitVec)
    (hbx : c.regs.rbx = t.regs.rbx) (hbp : c.regs.rbp = t.regs.rbp) (h14 : c.regs.r14 = t.regs.r14) :
    Hold s ra t' := by
  have hrsp : rsp c = rsp s - BitVec.ofNat 64 64 := by
    simp only [rsp, Reg64s.get64_rsp, hsp]; exact h.rsp
  obtain ⟨e0, e1, e2, -, -, e4, -⟩ := call_regs hag
  refine ⟨⟨Kit.Fm.call (k := 64) (by decide) hG hpre h.fm hc hrsp (ctx hpre h hc hdi).1 hp hag,
    ?_⟩, ?_, ?_, ?_⟩
  · rw [e0, hsp]; exact h.rsp
  · rw [e1, hbx]; exact h.rbx
  · rw [e2, hbp]; exact h.rbp
  · rw [e4, h14]; exact h.r14

-- The precondition of `push`.
theorem push_pre (hpre : Pre 72 produceA s) {t c : MachineData} (h : Lp s ra t)
    (hc : c.dmem = t.dmem) (hsp : c.regs.rsp = t.regs.rsp)
    (hdi : c.regs.rdi.toBitVec = t.regs.rbx.toBitVec)
    (hdx : c.regs.rdx.toBitVec = t.regs.rbp.toBitVec) : Pre pushF pushA c := by
  obtain ⟨e1, e2, e3, e4⟩ := ctx hpre h.toHold hc hdi
  have hrsp : rsp c = rsp s - BitVec.ofNat 64 64 := by
    simp only [rsp, Reg64s.get64_rsp, hsp]; exact h.rsp
  refine Kit.Fm.pre (k := 64) (by decide) hpre h.fm hc hrsp e1 ?_
  have hA := hpre.2.2
  simp only [pushA, produceA, st, e2, e3, e4, h.st, rdx, Reg64s.get64_rdx, hdx, h.rbp] at hA ⊢
  exact ⟨hA.1, hA.2.1, hA.2.2.1⟩

-- The precondition of `dup` for the copy `c0`.
theorem dup_pre (hpre : Pre 72 produceA s) {t c : MachineData} {c0 : Nat} (h : Lp s ra t)
    (hc0 : cp s = some c0) (hc : c.dmem = t.dmem) (hsp : c.regs.rsp = t.regs.rsp)
    (hdi : c.regs.rdi.toBitVec = t.regs.rbx.toBitVec)
    (hsi : c.regs.rsi.toBitVec = BitVec.ofNat 64 c0)
    (hdx : c.regs.rdx.toBitVec = t.regs.rbp.toBitVec) : Pre dupF dupA c := by
  obtain ⟨e1, e2, e3, e4⟩ := ctx hpre h.toHold hc hdi
  have hrsp : rsp c = rsp s - BitVec.ofNat 64 64 := by
    simp only [rsp, Reg64s.get64_rsp, hsp]; exact h.rsp
  have h1 := copy_lt hc0
  have h2 : (st s).len < 2 ^ 64 := len_lt
  refine Kit.Fm.pre (k := 64) (by decide) hpre h.fm hc hrsp e1 ?_
  have hA := hpre.2.2
  simp only [dupA, produceA, st, e2, e3, e4, h.st, rdx, Reg64s.get64_rdx, hdx, h.rbp, rsi,
    Reg64s.get64_rsi, hsi, BitVec.toNat_ofNat] at hA h1 h2 ⊢
  exact ⟨by omega, hA.1, hA.2.1, hA.2.2.1⟩

end
/-! ## The result of `emit` -/

-- `add` puts one slot on the stack.
theorem add_len {st st' : St} {v : StackSlot} {d : Nat} {op : Op} (h : add st v d op = .ok st') :
    st'.len = st.len + 1 := by
  rw [add_eq] at h
  split at h
  · cases h
  · cases h; simp [St.len]

theorem emit_len {e : Env} {st st' : St} {d : Nat} (h : emit e st d = .ok st') :
    st'.len = st.len + 1 := by
  dsimp only [emit] at h
  split at h
  · exact add_len h
  · split at h
    · split at h
      · cases h
      · exact add_len h
    · split at h
      · exact add_len h
      · split at h <;> cases h

section
variable {S : Addr} {t : MachineData}

-- An error of `emit` is an error of `produce`.
theorem Res.bind_err {r : M St} {f : St → M St} {Q Q' : St → Prop} (h : Res S r Q t)
    (hQ : ∀ a, Q a → rax t = 0#64) (hx : rax t ≠ 0#64) : Res S (r.bind f) Q' t := by
  cases r with
  | ok a => exact absurd (hQ a h) hx
  | error e => exact Res.err h

end

-- The flags of `test v, v`.
theorem nz_test {n : Nat} (v : BitVec n) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (v &&& v) r) = !(v == 0) := by
  simp [CondCode.interp, StatusFlags.from_result]

-- `cmpq len - 1, positionOf[d]`.
theorem pos_iff {w r : Word} {L : Nat} (hr : r.toNat = L) (hL : 1 ≤ L) :
    w = r + -1#64 ↔ optOf w = some (L - 1) := by
  subst hr
  unfold optOf
  split
  · rename_i h; subst h
    simp only [reduceCtorEq, iff_false]
    bv_omega
  · rename_i h
    simp only [Option.some.injEq]
    constructor <;> intro h' <;> bv_omega

/-! ## The store of `pendingGenerations - 1` -/

theorem produce_of_emit {e : Env} {st st' : St} {d : Nat} (h : emit e st d = .ok st') :
    produce e st d = tail d st' := by
  rw [produce_eq, h]; rfl

section
variable {s : MachineData} {ra : Int64}

-- The address of `positionOf[d]`: `8264(rbx, r14)`.
theorem pos_addr :
    wordAt (rdi s) (POS + dd s) = rdi s + rsi s * 8#64 + 8248#64 := by
  simp only [wordAt, POS_eq, dd]
  bv_omega

-- The loads of `.LB.Emission.produce.2`.
theorem at30_isSome (hpre : Pre 72 produceA s) {t : MachineData} (h : Hold s ra t) :
    (t.dmem.loadInt t.regs.rbx.toBitVec 8).isSome = true
      ∧ (t.dmem.loadInt (t.regs.rbx.toBitVec + t.regs.r14.toBitVec + 8248#64) 8).isSome = true
      ∧ (t.dmem.loadInt (t.regs.rbx.toBitVec + 8#64) 8).isSome = true := by
  have hd : dd s < nOf t.dmem (rdi s) := by
    rw [h.fm.n hpre, ← (fm0 (ra := ra) hpre).n hpre]; exact dd_lt hpre
  have hn := h.fm.wf.n_le
  simp only [MAX_N] at hn
  have hw := fun k (hk : k < WORDS) => h.fm.wf.word_isSome h.fm.wf.mapped hk
  rw [h.rbx, h.r14]
  refine ⟨by simpa [wordAt] using hw 0 (by decide), ?_, hw 1 (by decide)⟩
  have := hw (POS + dd s) (by simp only [WORDS_eq, POS_eq]; omega)
  rwa [pos_addr] at this

-- The pops of `.LB.Emission.produce.3` read the saved registers.
theorem Fm.pops {m : Mem 64} (h : Fm s ra m) {a : Addr} (ha : a = 8#64 + (rsp s - 64#64)) :
    rd m a = s.regs.rbx.toBitVec ∧ rd m (a + 8#64) = s.regs.rbp.toBitVec
      ∧ rd m (a + 8#64 + 8#64) = s.regs.r12.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64) = s.regs.r13.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64 + 8#64) = s.regs.r14.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) = s.regs.r15.toBitVec := by
  subst ha
  have hk : ∀ i (hi : i < 6) (b : Addr), b = rsp s - BitVec.ofNat 64 (8 * i + 16) →
      rd m b = s.regs.get64 regs[i] := fun i hi b hb => hb ▸ h.saved i hi
  exact ⟨hk 5 (by decide) _ (by bv_omega), hk 4 (by decide) _ (by bv_omega),
    hk 3 (by decide) _ (by bv_omega), hk 2 (by decide) _ (by bv_omega),
    hk 1 (by decide) _ (by bv_omega), hk 0 (by decide) _ (by bv_omega)⟩

end


/-! ## The call to `isSpilled` and the blocked error -/

section
variable {s : MachineData} {ra : Int64}

-- The precondition of `isSpilled`.
theorem spill_pre (hpre : Pre 72 produceA s) {t c : MachineData} (h : Lp s ra t)
    (hc : c.dmem = t.dmem) (hsp : c.regs.rsp = t.regs.rsp)
    (hdi : c.regs.rdi.toBitVec = t.regs.rbx.toBitVec)
    (hsi : c.regs.rsi.toBitVec = t.regs.r13.toBitVec) : Pre isSpilledF isSpilledA c := by
  obtain ⟨e1, e2, -, -⟩ := ctx hpre h.toHold hc hdi
  have hrsp : rsp c = rsp s - BitVec.ofNat 64 64 := by
    simp only [rsp, Reg64s.get64_rsp, hsp]; exact h.rsp
  refine Kit.Fm.pre (k := 64) (by decide) hpre h.fm hc hrsp e1 ⟨dd s, ?_, ?_⟩
  · rw [e2]; exact hpre.2.2.1
  · rw [e2]; simp only [slot, rsi, Reg64s.get64_rsi, hsi]; exact h.r13.symm

-- `testl eax, eax` after `isSpilled`.
theorem spill_of {t : MachineData} {b b' : Bool} {r : StatusFlags.from_result.Remaining}
    (hax : rax t = BitVec.ofNat 64 b.toNat)
    (hx : CondCode.nz.interp (StatusFlags.from_result
      (t.regs.rax.toBitVec.take 32 &&& t.regs.rax.toBitVec.take 32) r) = b') : b = b' := by
  rw [nz_test] at hx
  simp only [rax, Reg64s.get64_rax] at hax
  rw [hax] at hx
  rw [← hx]
  cases b <;> decide

-- `rbx + 56` holds the pointer to `blocked`.
theorem ptr_addr {t : MachineData} (h : Hold s ra t) :
    t.regs.rbx.toBitVec + 56#64 = wordAt (rdi s) 7 := by
  rw [h.rbx]

-- `len - 16 - c`, in words.
theorem far_nat {L c : Nat} (hf : 15 < L - 1 - c) :
    BitVec.ofNat 64 L + (18446744073709551600#64 - BitVec.ofNat 64 c)
      = BitVec.ofNat 64 (L - 1 - c - 15) := by
  bv_omega

-- The excess of a far copy is not zero.
theorem far_nz {k : Nat} {r : StatusFlags.from_result.Remaining} (h0 : 0 < k) (hk : k < 2 ^ 64) :
    CondCode.z.interp (StatusFlags.from_result (BitVec.ofNat 64 k) r) = false := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result, beq_eq_false_iff_ne, BitVec.zero_eq]
  intro h
  bv_omega

end
end Produce
end Bbu
