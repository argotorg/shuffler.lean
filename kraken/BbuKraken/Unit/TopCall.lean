import BbuKraken.Unit.TopRet

/-!
# The call of `buildBottomUp` in `build_bottom_up`
-/

namespace Bbu.Unit
open Bbu.Sep

namespace Top

-- The state after the call of `buildBottomUp`: `st` and `fs` are the result of the flat model
-- on the struct of the constructor.
structure TQ (s : MachineData) (ra : Int64) (st : Flat.Status) (fs : Flat.St) (t : MachineData) :
    Prop where
  res : Flat.buildBottomUp (topCtor s (u0 s ra)) = (st, fs)
  sp : t.regs.rsp.toBitVec = topS s
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  g : TopGuard s
  ra : t.dmem.loadInt (rsp s - 8#64) 8 = (s.pushRa ra).dmem.loadInt (rsp s - 8#64) 8
  mapped : Mem.Mapped [frame topF s] t.dmem
  out : Mem.UnchangedOutside (frame topF s :: topOut s) s.dmem t.dmem
  blkp : t.dmem.loadInt (topS s + BitVec.ofNat 64 offBlk) 8 = s.dmem.loadInt (rsp s + 8#64) 8
  blkm : Mem.Mapped [(blkArg s, 16)] t.dmem
  nops : (t.dmem.loadInt (topS s + 48#64) 8).isSome ∧
    rd t.dmem (topS s + 48#64) = BitVec.ofNat 64 fs.trace.length
  off : (t.dmem.loadInt (topS s + 16448#64) 8).isSome ∧
    rd t.dmem (topS s + 16448#64) = fs.blockedOffset
  exc : (t.dmem.loadInt (topS s + 16456#64) 8).isSome ∧
    rd t.dmem (topS s + 16456#64) = fs.blockedExcess
  len : fs.trace.length ≤ 6 * nArg s
  size : fs.size.toNat ≤ nArg s
  ops : (List.range fs.trace.length).map (topOp s t) = fs.trace
  data : (List.range fs.size.toNat).map (topData s t) = Flat.slotsOf fs

/-! ## The status in `al` -/

theorem sub_beq8 (a b : BitVec 8) : (a - b == BitVec.zero 8) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, show BitVec.zero 8 = 0#8 from rfl]
  constructor <;> intro h <;> bv_omega

theorem ext_al {x : BitVec 64} {st : Flat.Status} (hal : BitVec.setWidth 8 x = code st) :
    BitVec.extractLsb' 0 8 x = code st := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide)]; exact hal

-- `cmpb $1,%al; je`: the jump is for `blocked`.
theorem st_blocked {x : BitVec 64} {st : Flat.Status} (hal : BitVec.setWidth 8 x = code st)
    (h : (BitVec.extractLsb' 0 8 x - 1#8 == BitVec.zero 8) = true) : st = .blocked := by
  rw [ext_al hal] at h
  cases st <;> first | rfl | exact absurd h (by decide)

-- `cmpb $2,%al; jne`: the jump is for `done`.
theorem st_done {x : BitVec 64} {st : Flat.Status} (hal : BitVec.setWidth 8 x = code st)
    (h1 : (BitVec.extractLsb' 0 8 x - 1#8 == BitVec.zero 8) = false)
    (h2 : (!BitVec.extractLsb' 0 8 x - 2#8 == BitVec.zero 8) = true) : st = .done := by
  rw [ext_al hal] at h1 h2
  cases st <;> first | rfl | exact absurd h1 (by decide) | exact absurd h2 (by decide)

-- No jump: `assertionFailed`.
theorem st_fail {x : BitVec 64} {st : Flat.Status} (hal : BitVec.setWidth 8 x = code st)
    (h1 : (BitVec.extractLsb' 0 8 x - 1#8 == BitVec.zero 8) = false)
    (h2 : (!BitVec.extractLsb' 0 8 x - 2#8 == BitVec.zero 8) = false) :
    st = .assertionFailed := by
  rw [ext_al hal] at h1 h2
  cases st <;> first | rfl | exact absurd h1 (by decide) | exact absurd h2 (by decide)

/-! ## The state after the call -/

section
variable {s : MachineData} {ra : Int64} {st : Flat.Status} {fs : Flat.St} {t u : MachineData}

theorem TQ.next (h : TQ s ra st fs t) (hd : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (e1 : u.regs.rbx = t.regs.rbx) (e2 : u.regs.rbp = t.regs.rbp) (e3 : u.regs.r12 = t.regs.r12)
    (e4 : u.regs.r13 = t.regs.r13) (e5 : u.regs.r14 = t.regs.r14) (e6 : u.regs.r15 = t.regs.r15) :
    TQ s ra st fs u := by
  have eo : topOp s u = topOp s t := by funext i; simp only [topOp, hd]
  have ed : topData s u = topData s t := by funext i; simp only [topData, hd]
  exact ⟨h.res, by rw [hsp]; exact h.sp, e1.trans h.rbx, e2.trans h.rbp, e3.trans h.r12,
    e4.trans h.r13, e5.trans h.r14, e6.trans h.r15, h.g, by rw [hd]; exact h.ra,
    by rw [hd]; exact h.mapped, by rw [hd]; exact h.out, by rw [hd]; exact h.blkp,
    by rw [hd]; exact h.blkm,
    by rw [hd]; exact h.nops, by rw [hd]; exact h.off, by rw [hd]; exact h.exc, h.len, h.size,
    by rw [eo]; exact h.ops, by rw [ed]; exact h.data⟩

theorem TQ.stack_of (h : TQ s ra st fs t) (e : u.regs.rsp = t.regs.rsp) :
    u.StackAtOrBelow (s.pushRa ra) := by
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp, e, h.sp, topS, offOps]
  bv_omega

-- No jump after the call: `rdx` is `-2`, and the result is `-2`.
theorem TQ.fail (h : TQ s ra .assertionFailed fs t) (hd : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) (e1 : u.regs.rbx = t.regs.rbx) (e2 : u.regs.rbp = t.regs.rbp)
    (e3 : u.regs.r12 = t.regs.r12) (e4 : u.regs.r13 = t.regs.r13) (e5 : u.regs.r14 = t.regs.r14)
    (e6 : u.regs.r15 = t.regs.r15) : TR s ra (topS s) 18446744073709551614#64 u := by
  refine ⟨by rw [hsp]; exact h.sp, by rw [hd]; exact h.ra, e1.trans h.rbx, e2.trans h.rbp,
    e3.trans h.r12, e4.trans h.r13, e5.trans h.r14, e6.trans h.r15, by rw [hd]; exact h.mapped,
    by rw [hd]; exact h.out, u0 s ra, ?_⟩
  rw [topRes_fail h.g h.res]
  refine ⟨rfl, fun fs' e1 e2 => ?_⟩
  obtain rfl := Option.some.inj e1
  have hl := h.len
  have hn := h.g.n_le'
  have e3 := congrArg BitVec.toNat e2
  simp at e3
  omega

end

/-! ## The stores to `blocked` -/

section
variable {s : MachineData} {ra : Int64} {st : Flat.Status} {fs : Flat.St} {t u : MachineData}

theorem in_blk0 : Mem.Blocks.Inside (blkArg s) 8 [(blkArg s, 16)] :=
  Mem.Blocks.Inside.base (by decide)

theorem in_blk1 : Mem.Blocks.Inside (blkArg s + 8#64) 8 [(blkArg s, 16)] :=
  Mem.Blocks.Inside.base_add (by decide)

theorem blk_out {b : Addr} (hb : Mem.Blocks.Inside b 1 [(blkArg s, 16)]) :
    Mem.Blocks.Inside b 1 (topOut s ++ (dstArg s, 8 * mArg s) :: topRd s) :=
  Or.inr (Or.inr (Or.inl (hb.resolve_right id)))

-- `blocked` is not in the frame.
theorem fr_blk (hm : TopMem s) {b : Addr} (hf : Mem.Blocks.Inside b 1 [frame topF s]) :
    ¬Mem.Blocks.Inside b 1 [(blkArg s, 16)] := fun hb => hm.disj_frame b hf (blk_out hb)

theorem get?_st2 {m : Mem 64} {x y : Int} {b : Addr} (hb : ¬Mem.Blocks.Inside b 1 [(blkArg s, 16)]) :
    ((m.storeInt (blkArg s) 8 x).storeInt (blkArg s + 8#64) 8 y).get? b = m.get? b := by
  rw [in_blk1.get?_storeInt hb, in_blk0.get?_storeInt hb]

-- A load of `k` bytes in `(A, N)` reads the same in two memories that agree on `(A, N)`.
theorem ld_eq {m m' : Mem 64} {A a : Addr} {N k : Nat} (h : ∀ b, In A N b → m.get? b = m'.get? b)
    (hin : (a - A).toNat + k ≤ N) : m.loadInt a k = m'.loadInt a k := by
  have hin' : Mem.Blocks.Inside a k [(A, N)] := Or.inl hin
  exact Mem.loadInt_congr fun _ hi => h _ (inside_one_nil.mp (hin'.add_ofNat hi))

theorem rd_eq {m m' : Mem 64} {A a : Addr} {N : Nat} (h : ∀ b, In A N b → m.get? b = m'.get? b)
    (hin : (a - A).toNat + 8 ≤ N) : rd m a = rd m' a := by
  simp only [rd]; rw [ld_eq h hin]

theorem rdb_eq {m m' : Mem 64} {A a : Addr} {N : Nat} (h : ∀ b, In A N b → m.get? b = m'.get? b)
    (hin : (a - A).toNat + 1 ≤ N) : rdb m a = rdb m' a := by
  simp only [rdb]; rw [ld_eq h hin]

theorem add_sub_self (a x : Addr) : a + x - a = x := by rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem topOp_congr {i : Nat} (hn : nArg s ≤ 1024) (hi : i < 6 * nArg s)
    (h : ∀ b, In (opsArg s) (72 * nArg s) b → u.dmem.get? b = t.dmem.get? b) :
    topOp s u i = topOp s t i := by
  simp only [topOp]
  -- `omega` does not prove `(12 * i + 4) % 2 ^ 64 + 8 ≤ 72 * n` from `i < 6 * n` and `n ≤ 1024`.
  rw [rdb_eq h ?_, rdb_eq h ?_, rd_eq h ?_] <;>
    simp only [BitVec.add_assoc, add_sub_self, ← BitVec.ofNat_add, BitVec.toNat_ofNat] <;>
    rw [Nat.mod_eq_of_lt ?_] <;> omega

theorem topData_congr {i : Nat} (hn : nArg s ≤ 1024) (hi : i < nArg s)
    (h : ∀ b, In (dataArg s) (8 * nArg s) b → u.dmem.get? b = t.dmem.get? b) :
    topData s u i = topData s t i := by
  simp only [topData]
  rw [rd_eq h ?_]; bv_omega

-- A store in `blocked` does not change a word of the struct.
theorem TQ.ld (h : TQ s ra st fs t) (hp : TopPre s) {k : Nat} {x : Addr} {v : Int} {m : Mem 64}
    (off : Nat) (hx : Mem.Blocks.Inside x k [(blkArg s, 16)]) (hoff : off + 8 ≤ offOps := by decide) :
    (m.storeInt x k v).loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 =
      m.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 :=
  Mem.loadInt_congr fun _ hi => hx.get?_storeInt (fr_blk (hp.mem h.g)
    (Mem.Blocks.Inside.add_ofNat (by
      simp only [Mem.Blocks.Inside, topF_eq, or_false]; rw [h.sp]; simp only [offOps] at hoff; unfold topS offOps; bv_omega) hi)) v

-- The word `blocked` at `rsp + 8` of the entry.
theorem TQ.blk (h : TQ s ra st fs t) :
    BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 offBlk) 8).get! = blkArg s := by
  rw [h.sp, h.blkp]; rfl

theorem TQ.isSome_blkp (h : TQ s ra st fs t) (hp : TopPre s) :
    (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 offBlk) 8).isSome = true := by
  have hi : (rsp s + 8#64 - rsp s).toNat + 8 ≤ 16 := by bv_omega
  rw [h.sp, h.blkp]
  exact (hp.mem h.g).mapped.loadInt_isSome (Or.inr (Or.inr (Or.inr (Or.inl hi))))

-- A load in the struct, after stores.
theorem TQ.isSome_fr (h : TQ s ra st fs t) {m : Mem 64} (hm : Mem.Mapped [frame topF s] m)
    (off : Nat) (hoff : off + 8 ≤ offOps := by decide) :
    (m.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8).isSome = true :=
  hm.loadInt_isSome (by simp only [Mem.Blocks.Inside, topF_eq, or_false]; rw [h.sp]; simp only [offOps] at hoff; unfold topS offOps; bv_omega)

-- A load of `blocked`, after stores.
theorem TQ.isSome_b0 (h : TQ s ra st fs t) {m : Mem 64} (hm : Mem.Mapped [(blkArg s, 16)] m) :
    (m.loadInt (BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 offBlk) 8).get!) 8).isSome
      = true := by
  rw [h.blk]; exact hm.loadInt_isSome in_blk0

theorem TQ.isSome_b1 (h : TQ s ra st fs t) {m : Mem 64} (hm : Mem.Mapped [(blkArg s, 16)] m) :
    (m.loadInt (BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 offBlk) 8).get! + 8#64)
      8).isSome = true := by
  rw [h.blk]; exact hm.loadInt_isSome in_blk1

theorem TQ.rd_off (h : TQ s ra st fs t) :
    BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 16448#64) 8).get! = fs.blockedOffset := by
  rw [h.sp]; exact h.off.2

theorem TQ.rd_exc1 (h : TQ s ra st fs t) (hp : TopPre s) {a : Addr} (ha : a = blkArg s) {v : Int} :
    BitVec.ofInt 64 ((t.dmem.storeInt a 8 v).loadInt (t.regs.rsp.toBitVec + 16456#64) 8).get! =
      fs.blockedExcess := by
  subst ha; rw [h.ld hp 16456 in_blk0, h.sp]; exact h.exc.2

-- `.LB.build_bottom_up.13` and `.LB.build_bottom_up.12`: the two words of `blocked` are `x` and `y`, and `rdx` is `nops`.
theorem TQ.store (h : TQ s ra st fs t) (hp : TopPre s) {a x y w : Word} {fs' : Flat.St}
    (hu : u.dmem = (t.dmem.storeInt a 8 x.toInt).storeInt (a + 8#64) 8 y.toInt)
    (ha : a = blkArg s)
    (hr : topRes s (u0 s ra) = (BitVec.ofNat 64 fs.trace.length, some fs'))
    (hf : fs'.trace = fs.trace ∧ fs'.size = fs.size ∧ Flat.slotsOf fs' = Flat.slotsOf fs)
    (hx : x = fs'.blockedOffset) (hy : y = fs'.blockedExcess)
    (hw : w = BitVec.ofInt 64 (u.dmem.loadInt (t.regs.rsp.toBitVec + 48#64) 8).get!)
    (hsp : u.regs.rsp = t.regs.rsp) (e1 : u.regs.rbx = t.regs.rbx) (e2 : u.regs.rbp = t.regs.rbp)
    (e3 : u.regs.r12 = t.regs.r12) (e4 : u.regs.r13 = t.regs.r13) (e5 : u.regs.r14 = t.regs.r14)
    (e6 : u.regs.r15 = t.regs.r15) : TR s ra (topS s) w u := by
  subst ha
  have hm := hp.mem h.g
  have hd : ∀ b, ¬Mem.Blocks.Inside b 1 [(blkArg s, 16)] → u.dmem.get? b = t.dmem.get? b :=
    fun b hb => by rw [hu]; exact get?_st2 hb
  have hb0 : Mem.Mapped [(blkArg s, 8)] t.dmem :=
    mapped_sub h.blkm fun b hb => by simp only [In] at hb ⊢; bv_omega
  have hb1 : Mem.Mapped [(blkArg s + 8#64, 8)] (t.dmem.storeInt (blkArg s) 8 x.toInt) :=
    mapped_sub (h.blkm.storeInt _ _ _) fun b hb => by simp only [In] at hb ⊢; bv_omega
  refine ⟨by rw [hsp]; exact h.sp, ?_, e1.trans h.rbx, e2.trans h.rbp, e3.trans h.r12,
    e4.trans h.r13, e5.trans h.r14, e6.trans h.r15,
    by rw [hu]; exact (h.mapped.storeInt _ _ _).storeInt _ _ _, fun b hb => ?_, u0 s ra, ?_⟩
  · rw [← h.ra]
    exact Mem.loadInt_congr fun _ hi => hd _ (fr_blk hm (ra_in_frame.add_ofNat hi))
  · rw [hd b fun hb' => hb (Or.inr (Or.inr (Or.inr (Or.inl (hb'.resolve_right id)))))]
    exact h.out b hb
  rw [hr]
  refine ⟨?_, fun fs2 e7 _ => ?_⟩
  · rw [hw, hu, h.ld hp 48 in_blk1, h.ld hp 48 in_blk0, h.sp]; exact h.nops.2
  obtain rfl := Option.some.inj e7
  obtain ⟨ht, hz, hsl⟩ := hf
  have hn := h.g.n_le'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht]
    refine Eq.trans (List.map_congr_left fun i hi => ?_) h.ops
    have := List.mem_range.mp hi
    have := h.len
    exact topOp_congr hn (by omega) fun b hb => hd b fun hb' =>
      hm.disj_blk b hb' (inside_one.mpr (Or.inr (inside_one_nil.mpr hb)))
  · rw [hz, hsl]
    refine Eq.trans (List.map_congr_left fun i hi => ?_) h.data
    have := List.mem_range.mp hi
    have := h.size
    exact topData_congr hn (by omega) fun b hb => hd b fun hb' =>
      hm.disj_blk b hb' (inside_one.mpr (Or.inl hb))
  · rw [hu, rd_storeInt_of_disjoint ?_, rd_storeInt_self x hb0, hx]
    intro b hb hb'
    have := inside_one_nil.mp hb
    have := inside_one_nil.mp hb'
    simp only [In] at *
    bv_omega
  · show rd u.dmem (blkArg s + 8#64) = _
    rw [hu, rd_storeInt_self y hb1, hy]

end

end Top

end Bbu.Unit
