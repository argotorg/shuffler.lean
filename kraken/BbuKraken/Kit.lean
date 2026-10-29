import BbuKraken.Contracts

/-!
# Kit: lemmas for the proofs of the function bodies

See `Fn/SwapWith.lean` for a full use.

Goals of `kvcgen64`:
* `bbu_norm at *`: the normal form of the `kvcgen64` goals. Loads become `rd`,
  `(s.pushRa ra).dmem` becomes a store over `s.dmem`, the registers reduce,
  immediates become literals and shifts become `<<<`. Use it first, on all goals.
* `bbu_flags at h`: a flag hypothesis `CondCode.cc.interp (from_result ..) = b` of
  `cmp` or `test` (unsigned and equality codes) becomes a `Prop` for `bv_omega`.
* `bbu_rd`: `simp (disch := first | bv_omega | fail) only [rd_store_same, rd_store_other]`, the
  reads after stores. `bv_omega` must prove that the addresses are equal or do not
  overlap: put the facts it needs in the context first, in `bbu_norm` form.
* `isSome` goals of loads: `loadInt_isSome_store` removes a store (also the store of
  `pushRa`), then `Wf.isSome_struct` or `hw.mapped.loadInt_isSome`.

Facts for `bv_omega` (`Bbu`):
* `Wf.sep_data`, `Wf.sep_ops`: the working stack and the ops buffer do not overlap the struct.
* `FrameOk.sep_struct`: the frame does not overlap the struct.
* `sep_of_disjoint`: `Disjoint` of two blocks as `Nat` inequalities.
* `Wf.struct_lt`, `Wf.ops_lt`, `FrameOk.le`: the blocks do not wrap.

The model state (`Bbu`):
* `stOf_eq`: the model state is `st` if `len`, `pending`, `nops`, each slot and each
  op in memory agree with `st`.

Memory in a function body (`Bbu.Kit`, use `open Kit`). `Mid F s ra m`: `m` is the
memory of a body for the call `s` with frame size `F`.
* `Mid.init`: the memory after the call.
* `Mid.store`, `Mid.store_w`: a store to `mod F s`, a store to `writable`.
* `Mid.call`, `Mid.pre`: a call to a callee with frame size `G`.
* `Mid.call_isSome`: the return address slot of a callee is mapped.
* `Mid.keeps`, `Mid.wf`, `Mid.n`: the environment and the regions stay; the struct stays
  well formed if `len` and `nops` stay in bounds.
* `Mid.ret`: `ret` gives the postcondition of `Body`.

The saved registers (`Bbu.Kit`). A body that starts with `push r_0; ..; push r_k`
and has frame size `F` uses `abbrev Fm := Kit.Fm F [r_0, .., r_k]`.
* `pushes s ra rs`: the memory after the call and the pushes (the `kvcgen64` form).
* `Fm.init`: `Fm` holds for `pushes s ra rs`.
* `Fm.call`, `Fm.pre`: a call at `rsp s - k`, with `8 * rs.length + 8 ≤ k`.
* `Fm.write`: a change to `writable` only. `Fm.blk`: the two stores to `m_blocked`.
* `h.saved i _`: the word at `rsp s - (8 * i + 16)` is the register `rs[i]`.
* `Fm.ret`: `ret` gives the postcondition of `Body`, after the pops.
* `st_pushes`: the pushes do not change the model state.

Flags (`Bbu.Kit`): `cf_sub`, `cf_sub'`, `z_sub`, `nz_sub` (for `cmp`), `a_sub_imm`,
`be_sub_imm` (for `cmp $k`), `z_test`, `sf_test`, `ns_test` (for `test v, v`).

Words of the struct (`Bbu`): `Wf.word_isSome`, `n_envOf`, `target_get`.

Other normal forms (`Bbu`): `pushRa_<reg>`, `pushRa_rsp`, `disp<k>`, `shl4`. Results:
`Res.imp`, `Res.not_done`, `Res.err`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

/-! ## Normal forms -/

-- The form of a load in the `vcgen` goals.
@[simp] theorem rd_def {m : Mem 64} (a : Addr) : BitVec.ofInt 64 (m.loadInt a 8).get! = rd m a := rfl

-- The count of a shift by an immediate `k`.
theorem shiftLeft_imm (x k : BitVec 64) :
    x.shiftLeft ((k.take 8).toNat &&& 63) = x <<< (k.toNat % 64) := by
  have : (k.take 8).toNat &&& 63 = k.toNat % 64 := by
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    omega
  rw [this, BitVec.shiftLeft_eq]

theorem ushiftRight_imm (x k : BitVec 64) :
    x.ushiftRight ((k.take 8).toNat &&& 63) = x >>> (k.toNat % 64) := by
  have : (k.take 8).toNat &&& 63 = k.toNat % 64 := by
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    omega
  rw [this, BitVec.ushiftRight_eq]

theorem shl4 (x : BitVec 64) : x <<< 4 = x * 16#64 := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl

-- The registers after the push of the return address.
section
variable {s : MachineData} {ra : Int64}
theorem pushRa_rax : (s.pushRa ra).regs.rax = s.regs.rax := rfl
theorem pushRa_rbx : (s.pushRa ra).regs.rbx = s.regs.rbx := rfl
theorem pushRa_rcx : (s.pushRa ra).regs.rcx = s.regs.rcx := rfl
theorem pushRa_rdx : (s.pushRa ra).regs.rdx = s.regs.rdx := rfl
theorem pushRa_rsi : (s.pushRa ra).regs.rsi = s.regs.rsi := rfl
theorem pushRa_rdi : (s.pushRa ra).regs.rdi = s.regs.rdi := rfl
theorem pushRa_rbp : (s.pushRa ra).regs.rbp = s.regs.rbp := rfl
theorem pushRa_r8 : (s.pushRa ra).regs.r8 = s.regs.r8 := rfl
theorem pushRa_r9 : (s.pushRa ra).regs.r9 = s.regs.r9 := rfl
theorem pushRa_r10 : (s.pushRa ra).regs.r10 = s.regs.r10 := rfl
theorem pushRa_r11 : (s.pushRa ra).regs.r11 = s.regs.r11 := rfl
theorem pushRa_r12 : (s.pushRa ra).regs.r12 = s.regs.r12 := rfl
theorem pushRa_r13 : (s.pushRa ra).regs.r13 = s.regs.r13 := rfl
theorem pushRa_r14 : (s.pushRa ra).regs.r14 = s.regs.r14 := rfl
theorem pushRa_r15 : (s.pushRa ra).regs.r15 = s.regs.r15 := rfl
theorem pushRa_rsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
end

-- The displacement `8 * k` of a word in a struct.
theorem disp (a : Addr) (k : Nat) (i : Int64) (h : i.toInt = 8 * k := by decide) :
    a + BitVec.ofInt 64 i.toInt = wordAt a k := by
  rw [h, show (8 * (k : Int)) = ((8 * k : Nat) : Int) by omega, BitVec.ofInt_natCast]
theorem disp0 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 0) = wordAt a 0 := disp a 0 0
theorem disp1 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 8) = wordAt a 1 := disp a 1 8
theorem disp3 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 24) = wordAt a 3 := disp a 3 24
theorem disp4 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 32) = wordAt a 4 := disp a 4 32
theorem disp7 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 56) = wordAt a 7 := disp a 7 56

/-- The normal form of the `kvcgen64` goals. -/
macro "bbu_norm" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [rd_def,
  MachineData.regs_pushRa, MachineData.dmem_pushRa,
  Reg64s.set64_rax, Reg64s.set64_rbx, Reg64s.set64_rcx, Reg64s.set64_rdx, Reg64s.set64_rsi,
  Reg64s.set64_rdi, Reg64s.set64_rsp, Reg64s.set64_rbp, Reg64s.set64_r8, Reg64s.set64_r9,
  Reg64s.set64_r10, Reg64s.set64_r11, Reg64s.set64_r12, Reg64s.set64_r13, Reg64s.set64_r14,
  Reg64s.set64_r15,
  Reg64s.rax_mk, Reg64s.rbx_mk, Reg64s.rcx_mk, Reg64s.rdx_mk, Reg64s.rsi_mk, Reg64s.rdi_mk,
  Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk, Reg64s.r9_mk, Reg64s.r10_mk, Reg64s.r11_mk,
  Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk,
  Reg64s.get64_rax, Reg64s.get64_rbx, Reg64s.get64_rcx, Reg64s.get64_rdx, Reg64s.get64_rsi,
  Reg64s.get64_rdi, Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_r8, Reg64s.get64_r9,
  Reg64s.get64_r10, Reg64s.get64_r11, Reg64s.get64_r12, Reg64s.get64_r13, Reg64s.get64_r14,
  Reg64s.get64_r15,
  MachineData.regs_mk, MachineData.dmem_mk, MachineData.status_mk, MachineData.zmms_mk,
  wordAt, Nat.reduceMul, Nat.reduceAdd,
  Int64.reduceToInt, Int64.toBitVec_ofNat, BitVec.ofInt_ofNat, BitVec.ofInt_neg,
  BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.ofInt_toInt,
  shiftLeft_imm, ushiftRight_imm, BitVec.toNat_ofNat,
  Nat.reducePow, Nat.reduceMod] $(loc)?)

/-- A flag hypothesis of an unsigned or equality jump, as a `Prop` for `bv_omega`. -/
macro "bbu_flags" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [CondCode.interp_z,
  CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a,
  CondCode.interp_be, StatusFlags.cf_from_result, StatusFlags.zf_from_result, BitVec.zero_eq,
  Bool.not_eq_true', Bool.not_eq_false', Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_false_iff,
  Bool.or_eq_false_iff, bne_iff_ne, beq_iff_eq, bne_eq_false_iff_eq, beq_eq_false_iff_ne, ne_eq,
  BitVec.unsigned_eq] $(loc)?)

-- The carry flag of `cmp b, a` after `bbu_flags`: the borrow of `a - b`.
theorem borrow_iff (a b : BitVec 64) :
    ¬ (((a - b).toNat : Int) = (a.toNat : Int) - (b.toNat : Int)) ↔ a.toNat < b.toNat := by
  rw [BitVec.toNat_sub]
  have := a.isLt; have := b.isLt
  constructor <;> intro h <;> omega

theorem no_borrow_iff (a b : BitVec 64) :
    (((a - b).toNat : Int) = (a.toNat : Int) - (b.toNat : Int)) ↔ b.toNat ≤ a.toNat := by
  rw [BitVec.toNat_sub]
  have := a.isLt; have := b.isLt
  constructor <;> intro h <;> omega

/-! ## Words after a store -/

section
variable {m : Mem 64}

theorem rd_store_same {a b : Addr} (v : Int) (h : a = b) :
    rd (m.storeInt a 8 v) b = BitVec.ofInt 64 v := by
  subst h
  rw [rd, Mem.loadInt_storeInt _ _ _ _ (by decide), Option.get!_some, ofBytes_toBytes, Int.take]
  simp [BitVec.ofInt]

theorem rd_store_other {a b : Addr} (v : Int) (h : 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat) :
    rd (m.storeInt a 8 v) b = rd m b :=
  rd_storeInt_of_disjoint fun x hx hy => by
    simp only [Mem.Blocks.Inside, or_false] at hx hy; bv_omega

/-- The reads after stores. -/
macro "bbu_rd" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := first | bv_omega | fail) only [rd_store_same, rd_store_other, BitVec.ofInt_toInt,
    BitVec.ofInt_ofNat] $(loc)?)

theorem mapM_id_isSome {α} : ∀ {l : List (Option α)}, (l.mapM id).isSome → ∀ x ∈ l, x.isSome
  | [], _, _, hx => by cases hx
  | y :: l, h, x, hx => by
    cases y with
    | none => simp at h
    | some a =>
      cases hl : l.mapM id with
      | none => simp [List.mapM_cons, hl] at h
      | some r =>
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact mapM_id_isSome (by simp [hl]) x hx

-- A store keeps the loads that succeed.
theorem loadInt_isSome_store {a b : Addr} {n k : Nat} (v : Int) (h : (m.loadInt a k).isSome) :
    ((m.storeInt b n v).loadInt a k).isSome := by
  have hm : Mem.Mapped [(a, k)] m := fun x hx => by
    simp only [Mem.Blocks.Inside, or_false] at hx
    simp only [Mem.loadInt, Mem.loadBytes, List.allSome, Option.isSome_map] at h
    have := mapM_id_isSome h _ (List.mem_map.mpr ⟨(x - a).toNat, List.mem_range.mpr (by omega), rfl⟩)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show a + (x - a) = x by bv_omega] at this
  exact (hm.storeInt b n v).loadInt_isSome (Mem.Blocks.Inside.base (Nat.le_refl k))

end

/-! ## Facts for `bv_omega` -/

section
variable {m : Mem 64} {S : Addr}

-- Two blocks that do not wrap and do not overlap lie one after the other.
theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : Mem.Blocks.Disjoint [(a, n)] [(b, k)])
    (hn : 0 < n) (hk : 0 < k) :
    a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  refine Classical.byContradiction fun hc => ?_
  by_cases hab : a.toNat ≤ b.toNat
  · exact h b (by simp only [Mem.Blocks.Inside, or_false]; bv_omega)
      (by simp only [Mem.Blocks.Inside, or_false]; bv_omega)
  · exact h a (by simp only [Mem.Blocks.Inside, or_false]; bv_omega)
      (by simp only [Mem.Blocks.Inside, or_false]; bv_omega)

-- The struct is the union of four blocks of `writable` and `readable`.
theorem inside_struct {x : Addr} (h : Mem.Blocks.Inside x 1 [(S, 8 * WORDS)]) :
    Mem.Blocks.Inside x 1 (writable m S ++ readable m S) := by
  simp only [Mem.Blocks.Inside, or_false, WORDS, BLK, PEND, POS, DEST, MAX_N] at h
  rw [inside_append]
  by_cases h1 : (x - S).toNat < 32
  · exact Or.inr (Or.inl (by omega))
  by_cases h2 : (x - S).toNat < 40
  · exact Or.inl (Or.inl (by simp only [wordAt]; bv_omega))
  by_cases h3 : (x - S).toNat < 48
  · exact Or.inr (Or.inr (Or.inl (by simp only [wordAt]; bv_omega)))
  · exact Or.inl (Or.inr (Or.inl (by simp only [wordAt, WORDS, BLK, PEND, POS, DEST, MAX_N]; bv_omega)))

-- A change outside the struct words 0 to 3 and 5 keeps `writable`.
theorem writable_congr {m' : Mem 64} {l : List (Addr × Nat)} (h : Mem.UnchangedOutside l m m')
    (hd : Mem.Blocks.Disjoint (readable m S) l) : writable m' S = writable m S := by
  obtain ⟨hn, -, -, ho, hda⟩ := hdr_congr' h hd
  simp only [writable, hn, ho, hda]

-- The blocks of `writable`: `m_size`, the words from `m_traceSize` to `m_blocked`,
-- the working stack and the ops buffer.
theorem inside_writable {a : Addr} {n : Nat}
    (h : (32 ≤ (a - S).toNat ∧ (a - S).toNat + n ≤ 40)
      ∨ (48 ≤ (a - S).toNat ∧ (a - S).toNat + n ≤ 8 * WORDS)
      ∨ (a - dataOf m S).toNat + n ≤ 8 * nOf m S
      ∨ (a - opsOf m S).toNat + n ≤ 72 * nOf m S) :
    Mem.Blocks.Inside a n (writable m S) := by
  simp only [writable, Mem.Blocks.Inside, wordAt, BLK, PEND, POS, DEST, WORDS, MAX_N, or_false] at h ⊢
  bv_omega

-- A load from the struct succeeds.
theorem Wf.isSome_struct (hw : Wf m S) {a : Addr} {n : Nat} (h : (a - S).toNat + n ≤ 8 * WORDS) :
    (m.loadInt a n).isSome :=
  Mem.Mapped.loadInt_isSome (bs := [(S, 8 * WORDS)]) (fun x hx => hw.mapped x (inside_struct hx))
    (Or.inl h)

theorem disjoint_head {a b : Addr} {n k : Nat} {l : List (Addr × Nat)}
    (h : Mem.Blocks.Disjoint [(a, n)] ((b, k) :: l)) : Mem.Blocks.Disjoint [(a, n)] [(b, k)] :=
  fun x hx hy => h x hx (hy.elim Or.inl False.elim)

-- The working stack, the ops buffer and the struct do not overlap.
theorem Wf.sep_data (hw : Wf m S) (hn : 0 < nOf m S) :
    (dataOf m S).toNat + 8 * nOf m S ≤ S.toNat ∨ S.toNat + 8 * WORDS ≤ (dataOf m S).toNat :=
  (sep_of_disjoint (disjoint_head hw.disj_struct) (by decide) (by omega)).symm

theorem Wf.sep_ops (hw : Wf m S) (hn : 0 < nOf m S) :
    (opsOf m S).toNat + 72 * nOf m S ≤ S.toNat ∨ S.toNat + 8 * WORDS ≤ (opsOf m S).toNat :=
  (sep_of_disjoint (disjoint_head (fun x hx hy => hw.disj_struct x hx (Or.inr hy)))
    (by decide) (by omega)).symm

theorem Wf.sep_data_ops (hw : Wf m S) (hn : 0 < nOf m S) :
    (dataOf m S).toNat + 8 * nOf m S ≤ (opsOf m S).toNat
      ∨ (opsOf m S).toNat + 72 * nOf m S ≤ (dataOf m S).toNat :=
  sep_of_disjoint (disjoint_head hw.disj_data) (by omega) (by omega)

-- The frame of a call does not overlap the struct.
theorem FrameOk.sep_struct {F : Nat} {s : MachineData} (hf : FrameOk F s) (hF : 0 < F) :
    (rsp s).toNat ≤ (rdi s).toNat ∨ (rdi s).toNat + 8 * WORDS ≤ (rsp s).toNat - F := by
  have hle := hf.le
  have := sep_of_disjoint (a := rsp s - BitVec.ofNat 64 F) (n := F) (b := rdi s) (k := 8 * WORDS)
    (fun x hx hy => hf.disj x hx (inside_struct hy)) hF (by decide)
  bv_omega

-- The frame of a call does not overlap a block of `writable`.
theorem FrameOk.sep_writable {F : Nat} {s : MachineData} (hf : FrameOk F s) (hF : 0 < F)
    {a : Addr} {k : Nat} (hk : 0 < k) (ha : (a, k) ∈ writable s.dmem (rdi s)) :
    (rsp s).toNat ≤ a.toNat ∨ a.toNat + k ≤ (rsp s).toNat - F := by
  have hle := hf.le
  have := sep_of_disjoint (a := rsp s - BitVec.ofNat 64 F) (n := F) (b := a) (k := k)
    (fun x hx hy => hf.disj x hx (inside_append.mpr (Or.inl (inside_of_mem ha hy)))) hF hk
  bv_omega

-- The frame of a call does not overlap the working stack or the ops buffer.
theorem FrameOk.sep_data {F : Nat} {s : MachineData} (hf : FrameOk F s) (hF : 0 < F)
    (hn : 0 < nOf s.dmem (rdi s)) :
    (rsp s).toNat ≤ (dataOf s.dmem (rdi s)).toNat
      ∨ (dataOf s.dmem (rdi s)).toNat + 8 * nOf s.dmem (rdi s) ≤ (rsp s).toNat - F :=
  hf.sep_writable hF (by omega) (by simp [writable])

theorem FrameOk.sep_ops {F : Nat} {s : MachineData} (hf : FrameOk F s) (hF : 0 < F)
    (hn : 0 < nOf s.dmem (rdi s)) :
    (rsp s).toNat ≤ (opsOf s.dmem (rdi s)).toNat
      ∨ (opsOf s.dmem (rdi s)).toNat + 72 * nOf s.dmem (rdi s) ≤ (rsp s).toNat - F :=
  hf.sep_writable hF (by omega) (by simp [writable])

end

/-! ## The model state -/

section
variable {m : Mem 64} {S : Addr}

theorem len_stOf : (stOf m S).len = (rd m (wordAt S 4)).toNat := by
  simp [St.len, stOf]

theorem nops_stOf : (stOf m S).trace.length = (rd m (wordAt S 6)).toNat := by
  simp [stOf]

theorem val_stOf {i : Nat} (hi : i < (rd m (wordAt S 4)).toNat) :
    (stOf m S).val i = StackSlot.ofWord (rd m (wordAt (dataOf m S) i)) := by
  simp [St.val, stOf, hi, slotOf]

theorem dest_stOf {i : Nat} (hi : i < (rd m (wordAt S 4)).toNat) :
    (stOf m S).dest i = (rd m (wordAt S (DEST + i))).toNat := by
  simp [St.dest, stOf, hi, slotOf]

theorem positionOf_stOf {d : Nat} (hd : d < nOf m S) :
    positionOf (stOf m S) d = optOf (rd m (wordAt S (POS + d))) := by
  simp [positionOf, stOf, hd]

-- The model state is `st` if the words in memory agree with `st`.
theorem stOf_eq {st : St} (hlen : (rd m (wordAt S 4)).toNat = st.len)
    (hpend : (rd m (wordAt S PEND)).toNat = st.pendingGenerations)
    (hnops : (rd m (wordAt S 6)).toNat = st.trace.length)
    (hslot : ∀ i (hi : i < st.len), slotOf m S i = st.slots[i])
    (hplen : st.positionOf.length = nOf m S)
    (hpos : ∀ d (hd : d < st.positionOf.length), optOf (rd m (wordAt S (POS + d))) = st.positionOf[d])
    (hop : ∀ i (hi : i < st.trace.length), opOf m S i = st.trace[i]) : stOf m S = st := by
  obtain ⟨slots, pos, pending, ops⟩ := st
  simp only [St.len] at hlen hslot
  simp only at hplen hpos
  simp only [stOf, hlen, hpend, hnops, St.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · exact List.ext_getElem (by simp) fun i h1 h2 => by simpa using hslot i h2
  · exact List.ext_getElem (by simp [hplen]) fun d h1 h2 => by simpa using hpos d h2
  · exact List.ext_getElem (by simp) fun i h1 h2 => by simpa using hop i h2

theorem target_get {d : Nat} (hd : d < nOf m S) :
    (envOf m S).target[d]! = StackSlot.ofWord (rd m (wordAt (tgtOf m S) d)) := by
  simp [envOf, hd, tgtSlot]

theorem n_envOf : (envOf m S).n = nOf m S := by
  simp [Env.n, envOf]

end

/-! ## Slots -/

theorem ofWord_bits {a b : Word} :
    StackSlot.ofWord a = StackSlot.ofWord b ↔ ∀ j < 48, a.getLsbD j = b.getLsbD j := by
  simp only [StackSlot.ofWord, StackSlot.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩ j hj
    by_cases hj1 : j < 32
    · have := congrArg (·.getLsbD j) h1
      simpa [BitVec.getLsbD_extractLsb', hj1] using this
    by_cases hj2 : j < 40
    · have := congrArg (·.getLsbD (j - 32)) h2
      simp only [BitVec.getLsbD_extractLsb'] at this
      rwa [show 32 + (j - 32) = j by omega, decide_eq_true (by omega : j - 32 < 8), Bool.true_and,
        Bool.true_and] at this
    · have := congrArg (·.getLsbD (j - 40)) h3
      simp only [BitVec.getLsbD_extractLsb'] at this
      rwa [show 40 + (j - 40) = j by omega, decide_eq_true (by omega : j - 40 < 8), Bool.true_and,
        Bool.true_and] at this
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> ext k hk <;> simp only [BitVec.getElem_extractLsb'] <;> exact h _ (by omega)

-- `(a ^ b) << 16 == 0` in the C: the two slots are equal.
theorem ofWord_eq_iff (a b : Word) :
    StackSlot.ofWord a = StackSlot.ofWord b ↔ (a ^^^ b) <<< 16 = 0#64 := by
  rw [ofWord_bits]
  constructor
  · intro h
    ext i hi
    simp only [BitVec.getElem_shiftLeft, BitVec.getElem_zero]
    by_cases hi16 : i < 16
    · simp [hi16]
    · simp only [hi16, decide_false, Bool.not_false, Bool.true_and, ← BitVec.getLsbD_eq_getElem]
      rw [BitVec.getLsbD_xor, h (i - 16) (by omega), Bool.xor_self]
  · intro h j hj
    have := congrArg (·.getLsbD (j + 16)) h
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero, BitVec.getLsbD_xor] at this
    simp only [show j + 16 < 64 by omega, decide_true, show ¬ j + 16 < 16 by omega, decide_false,
      Bool.not_false, Bool.true_and, Nat.add_sub_cancel] at this
    simpa using this

/-! ## Words of the struct -/

section
variable {m m' : Mem 64} {S : Addr}

-- A load of a word of the struct succeeds in a memory `m'` that keeps the struct mapped.
theorem Wf.word_isSome (hw : Wf m S) (hm : Mem.Mapped (writable m S ++ readable m S) m') {k : Nat}
    (hk : k < WORDS) : (m'.loadInt (wordAt S k) 8).isSome = true := by
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs hk
  refine Mem.Mapped.loadInt_isSome (bs := [(S, 8 * WORDS)]) (fun x hx => hm x (inside_struct hx))
    (Or.inl ?_)
  simp only [wordAt, WORDS_eq]; bv_omega

end

/-! ## Results -/

section
variable {α : Type} {S : Addr} {Q : α → Prop} {t : MachineData}

theorem Res.imp {r : M α} {Q' : α → Prop} (h : Res S r Q t) (hq : ∀ a, Q a → Q' a) :
    Res S r Q' t := by
  cases r with
  | error e => cases e <;> exact h
  | ok a => exact hq a h

-- An error returns a `Status` that is not `Done`.
theorem Res.not_done {e : Err} (h : Res S (.error e : M α) Q t) : al t ≠ DONE := by
  cases e with
  | blocked p x => rw [h.1]; decide
  | assertion => rw [h]; decide

theorem Res.err {β : Type} {e : Err} {Q' : β → Prop} (h : Res S (.error e : M α) Q t) :
    Res S (.error e : M β) Q' t := by
  cases e <;> exact h

end

/-! ## Memory in a function body -/

namespace Kit

section
variable {F : Nat} {s : MachineData} {ra : Int64} {A : MachineData → Prop} {m : Mem 64}

/-- The memory `m` of a body for the call `s` with frame size `F`: the return address
stays, the blocks of `mod F s` stay mapped and the body changes no byte outside them. -/
structure Mid (F : Nat) (s : MachineData) (ra : Int64) (m : Mem 64) : Prop where
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  map : Mem.Mapped (mod F s).mem m
  un : Mem.UnchangedOutside (mod F s).mem s.dmem m

-- The return address lies in the frame.
theorem ra_in_frame (hF : 8 ≤ F) (hpre : Pre F A s) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - 8#64, 8)] → Mem.Blocks.Inside x 1 [frame F s] := by
  have hle := hpre.2.1.le
  intro x hx
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

-- The bytes of a block that lies in `l` lie in `l`.
theorem inside_bytes {a : Addr} {n : Nat} {l : List (Addr × Nat)} (ha : Mem.Blocks.Inside a n l) :
    ∀ x, Mem.Blocks.Inside x 1 [(a, n)] → Mem.Blocks.Inside x 1 l := by
  intro x hx
  simp only [Mem.Blocks.Inside, or_false] at hx
  have := Mem.Blocks.Inside.add_ofNat (n := n) (i := (x - a).toNat) ha (by omega)
  rwa [show a + BitVec.ofNat 64 (x - a).toNat = x by bv_omega] at this

theorem Mid.init (hF : 8 ≤ F) (hpre : Pre F A s) : Mid F s ra (s.pushRa ra).dmem := by
  have hu : Mem.UnchangedOutside [(rsp s - 8#64, 8)] s.dmem (s.pushRa ra).dmem :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  have hm : Mem.Mapped (mod F s).mem s.dmem := fun x hx =>
    hx.elim (fun h => hpre.2.1.mapped x (Or.inl h))
      (fun h => hpre.1.mapped x (inside_append.mpr (Or.inl h)))
  refine ⟨(rd_store_same _ rfl).trans BitVec.ofInt_toInt, hm.storeInt _ _ _, fun x hx => ?_⟩
  exact hu x fun h => hx (Or.inl ((ra_in_frame hF hpre x h).elim id False.elim))

-- A store to `mod F s` that does not overlap the return address.
theorem Mid.store (h : Mid F s ra m) {a : Addr} {n : Nat} (ha : Mem.Blocks.Inside a n (mod F s).mem)
    (hra : Mem.Blocks.Disjoint [(rsp s - 8#64, 8)] [(a, n)]) (v : Int) :
    Mid F s ra (m.storeInt a n v) := by
  have hu : Mem.UnchangedOutside [(a, n)] m (m.storeInt a n v) :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl n)) _
  refine ⟨(rd_congr hu hra).trans h.ra, h.map.storeInt _ _ _, fun x hx => ?_⟩
  rw [hu x fun hy => hx (inside_bytes ha x hy)]
  exact h.un x hx

-- A store to `writable`.
theorem Mid.store_w (hF : 8 ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) {a : Addr} {n : Nat}
    (ha : Mem.Blocks.Inside a n (writable s.dmem (rdi s))) (v : Int) :
    Mid F s ra (m.storeInt a n v) :=
  h.store ha.tail (fun x hx hy => hpre.2.1.disj x (ra_in_frame hF hpre x hx)
    (inside_append.mpr (Or.inl (inside_bytes ha x hy)))) v

-- The struct is well formed after the call.
theorem wf_pushRa (hF : 8 ≤ F) (hpre : Pre F A s) : Wf (s.pushRa ra).dmem (rdi s) :=
  Wf.congr_of_disjoint
    (Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _)
    hpre.1 (disjoint_symm (disjoint_mono (ra_in_frame hF hpre) hpre.2.1.disj))

-- The environment and the regions of the struct stay.
theorem Mid.keeps (hpre : Pre F A s) (h : Mid F s ra m) :
    envOf m (rdi s) = env s ∧ readable m (rdi s) = readable s.dmem (rdi s)
      ∧ writable m (rdi s) = writable s.dmem (rdi s) :=
  Post.env (t := { s with dmem := m }) hpre ⟨fun _ _ => rfl, h.un⟩

theorem Mid.n (hpre : Pre F A s) (h : Mid F s ra m) : nOf m (rdi s) = nOf s.dmem (rdi s) := by
  have := congrArg Env.n (h.keeps hpre).1
  rwa [n_envOf, n_envOf] at this

-- The struct stays well formed if `len` and `nops` stay in bounds.
theorem Mid.wf (hpre : Pre F A s) (h : Mid F s ra m)
    (hlen : (rd m (wordAt (rdi s) 4)).toNat ≤ nOf s.dmem (rdi s))
    (hnops : (rd m (wordAt (rdi s) 6)).toNat ≤ 6 * nOf s.dmem (rdi s)) : Wf m (rdi s) :=
  Wf.congr h.un hpre.1 hpre.disj (fun x hx => h.map x (Or.inr hx)) hlen hnops

-- The memory after a call to a callee with frame size `G` at `k` bytes below `rsp s`.
theorem Mid.call {G k : Nat} {c t : MachineData} {R : MachineData → MachineData → Prop}
    (hk : 8 ≤ k) (hG : k + G ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - BitVec.ofNat 64 k) (hrdi : rdi c = rdi s) (hp : Post G R c t)
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
  have hnw : ∀ x, Mem.Blocks.Inside x 1 [frame F s] →
      ¬ Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
    fun x hx hw => hfr.disj x hx (inside_append.mpr (Or.inl hw))
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [rd_congr hu fun x hx hl => ?_]
    · exact h.ra
    · rcases hl with hl | hl
      · simp only [Mem.Blocks.Inside, or_false, hrsp] at hx hl
        bv_omega
      · exact hnw x (ra_in_frame (by omega) hpre x hx) hl
  · by_cases hx8 : Mem.Blocks.Inside x 1 [frame G c]
    · exact hp.2.1 x hx8
    by_cases hxw : Mem.Blocks.Inside x 1 (writable s.dmem (rdi s))
    · -- the callee keeps the struct well formed
      have hd : Mem.Blocks.Disjoint (readable m (rdi s)) (frame G c :: writable s.dmem (rdi s)) :=
        (h.keeps hpre).2.1 ▸ disjoint_mono (bs' := readable s.dmem (rdi s))
          (fun _ hy => hy) fun y hy hl => hpre.disj y hy (hl.elim
            (fun hl => Or.inl ((hsub y (Or.inl hl)).elim id False.elim)) Or.inr)
      have := hp.1.mapped x (inside_append.mpr (Or.inl ?_))
      · exact this
      · rw [hrdi, writable_congr hu hd, hwr]; exact hxw
    · rw [hu x fun hl => hl.elim (fun hl => hx8 (Or.inl hl)) hxw]
      exact h.map x hx
  · rw [hu x fun hl => hl.elim (fun hl => hx (Or.inl ((hsub x (Or.inl hl)).elim id False.elim)))
      (fun hl => hx (Or.inr hl))]
    exact h.un x hx

-- The return address slot of a callee at `k` bytes below `rsp s` is mapped.
theorem Mid.call_isSome {k : Nat} (hk : k + 8 ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) :
    (m.loadInt (rsp s - BitVec.ofNat 64 k - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  refine Mem.Mapped.loadInt_isSome h.map (Or.inl ?_)
  bv_omega

-- The precondition of a callee with frame size `G` at `k` bytes below `rsp s`.
theorem Mid.pre {G k : Nat} {c : MachineData} {A' : MachineData → Prop}
    (hG : k + G ≤ F) (hpre : Pre F A s) (h : Mid F s ra m) (hw : Wf m (rdi s)) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - BitVec.ofNat 64 k) (hrdi : rdi c = rdi s) (hA : A' c) : Pre G A' c := by
  obtain ⟨-, hr, hwr⟩ := h.keeps hpre
  refine ⟨by rw [hc, hrdi]; exact hw, ?_, hA⟩
  exact FrameOk.sub hpre.2.1 hpre.1 hrdi hrsp hG
    (hc ▸ fun x hx => h.map x (hx.elim Or.inl False.elim)) (hc ▸ hr) (hc ▸ hwr)

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

-- The stack at the call is below the stack after `ret`.
theorem stackBelow_pushRa {u : MachineData} (h : rsp u = rsp s) : (s.pushRa ra).StackBelow u := by
  apply MachineData.stackBelow_of_add_eight
  simp only [MachineData.pushRa, Reg64s.get64_set64, reduceIte]
  rw [show u.regs.get64 .rsp = rsp s from h]
  exact BitVec.sub_add_cancel _ _

/-- `ret` from `t` to `u`, with the memory `Mid`, a well formed struct and the registers
of the call, gives the postcondition of `Body`. -/
theorem Mid.ret [Host] {R : MachineData → MachineData → Prop} {ls : List Label}
    {I' : CfgLabel → Nat → Unit → MachineData → Prop} {t u : MachineData} (hF : 8 ≤ F)
    (hpre : Pre F A s) (h : Mid F s ra t.dmem) (hsp : rsp t = rsp s - 8#64) (hu : u.dmem = t.dmem)
    (husp : rsp u = rsp s)
    (hr : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      u.regs.get64 q = s.regs.get64 q)
    (hw : Wf u.dmem (rdi s)) (hR : R s u) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post F R s t ∧ (mod F s).Agree s t) t.retAddr.get! u := by
  have hra := h.retAddr hF hpre hsp
  refine Or.inr ⟨⟨by simp [hra], ⟨hw, fun x hx => hu ▸ h.map x (hx.elim Or.inl False.elim), hR⟩,
    fun q hq => ?_, hu ▸ h.un⟩, fun _ _ _ => ?_⟩
  · by_cases hq' : q = .rsp
    · subst hq'; exact husp
    · exact hr q (by simp_all [mod])
  · exact stackBelow_pushRa husp

end

/-! ## The saved registers -/

-- The memory after pushes of the registers `rs` of `s` below `a`, as `kvcgen64` gives it.
def pushAt (s : MachineData) : Addr → List Reg64 → Mem 64 → Mem 64
  | _, [], m => m
  | a, r :: rs, m => pushAt s (a - 8#64) rs (m.storeInt (a - 8#64) 8 (s.regs.get64 r).toInt)

-- The memory after the call `s` with the return address `ra` and the pushes of `rs`.
def pushes (s : MachineData) (ra : Int64) (rs : List Reg64) : Mem 64 :=
  pushAt s (rsp s - 8#64) rs (s.pushRa ra).dmem

section
variable {s : MachineData} {l : List (Addr × Nat)} {m0 m : Mem 64} {a : Addr} {rs : List Reg64}

-- The pushes change only words in `l`.
theorem pushAt_un (h : Mem.UnchangedOutside l m0 m)
    (hl : ∀ i, i < rs.length → Mem.Blocks.Inside (a - BitVec.ofNat 64 (8 * i + 8)) 8 l) :
    Mem.UnchangedOutside l m0 (pushAt s a rs m) := by
  induction rs generalizing a m with
  | nil => exact h
  | cons r rs ih =>
    refine ih (h.storeInt (hl 0 (by simp)) _) fun i hi => ?_
    rw [show a - 8#64 - BitVec.ofNat 64 (8 * i + 8) = a - BitVec.ofNat 64 (8 * (i + 1) + 8) by
      bv_omega]
    exact hl (i + 1) (by simp; omega)

theorem pushAt_mapped (h : Mem.Mapped l m) : Mem.Mapped l (pushAt s a rs m) := by
  induction rs generalizing a m with
  | nil => exact h
  | cons r rs ih => exact ih (h.storeInt _ _ _)

-- The pushes do not change a word that they do not overlap.
theorem rd_pushAt_other {b : Addr}
    (h : ∀ i, i < rs.length → 8 ≤ (b - (a - BitVec.ofNat 64 (8 * i + 8))).toNat
      ∧ 8 ≤ (a - BitVec.ofNat 64 (8 * i + 8) - b).toNat) :
    rd (pushAt s a rs m) b = rd m b := by
  induction rs generalizing a m with
  | nil => rfl
  | cons r rs ih =>
    refine (ih fun i hi => ?_).trans (rd_store_other _ (h 0 (by simp)))
    rw [show a - 8#64 - BitVec.ofNat 64 (8 * i + 8) = a - BitVec.ofNat 64 (8 * (i + 1) + 8) by
      bv_omega]
    exact h (i + 1) (by simp; omega)

-- The word of the push `i`.
theorem rd_pushAt_self (hn : 8 * rs.length ≤ 2 ^ 64) (i : Nat) (hi : i < rs.length) :
    rd (pushAt s a rs m) (a - BitVec.ofNat 64 (8 * i + 8)) = s.regs.get64 rs[i] := by
  induction rs generalizing a m i with
  | nil => cases hi
  | cons r rs ih =>
    have hl : (r :: rs).length = rs.length + 1 := rfl
    show rd (pushAt s (a - 8#64) rs (m.storeInt (a - 8#64) 8 (s.regs.get64 r).toInt)) _ = _
    cases i with
    | zero =>
      refine (rd_pushAt_other fun j hj => ?_).trans ?_
      · constructor <;> bv_omega
      · exact (rd_store_same _ (by bv_omega)).trans BitVec.ofInt_toInt
    | succ i =>
      rw [show a - BitVec.ofNat 64 (8 * (i + 1) + 8) = a - 8#64 - BitVec.ofNat 64 (8 * i + 8) by
        bv_omega]
      exact ih (by omega) i (by omega)

end

section
variable {F : Nat} {rs : List Reg64} {s : MachineData} {ra : Int64} {A : MachineData → Prop}
  {m : Mem 64}

/-- The memory `m` of a body that pushes the registers `rs` after the call: `Mid`, the
struct is well formed, and the word `8 * i + 16` bytes below `rsp s` is the register `rs[i]`
of `s`. -/
structure Fm (F : Nat) (rs : List Reg64) (s : MachineData) (ra : Int64) (m : Mem 64) : Prop
    extends Mid F s ra m where
  wf : Wf m (rdi s)
  saved : ∀ i (hi : i < rs.length), rd m (rsp s - BitVec.ofNat 64 (8 * i + 16)) = s.regs.get64 rs[i]

-- The pushes change only the frame.
theorem unchanged_pushes (hF : 8 * rs.length + 8 ≤ F) (hpre : Pre F A s) :
    Mem.UnchangedOutside [frame F s] s.dmem (pushes s ra rs) := by
  have hle := hpre.2.1.le
  have hu : Mem.UnchangedOutside [frame F s] s.dmem (s.pushRa ra).dmem :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl)
      (show Mem.Blocks.Inside (rsp s - 8#64) 8 [frame F s] from Or.inl (by bv_omega)) _
  exact pushAt_un hu fun i hi => Or.inl (by simp only [rsp] at *; bv_omega)

theorem st_pushes (hF : 8 * rs.length + 8 ≤ F) (hpre : Pre F A s) :
    stOf (pushes s ra rs) (rdi s) = st s :=
  stOf_congr (unchanged_pushes hF hpre) hpre.1 (disjoint_symm hpre.2.1.disj)

-- The memory after the pushes.
theorem Fm.init (hF : 8 * rs.length + 8 ≤ F) (hpre : Pre F A s) : Fm F rs s ra (pushes s ra rs) := by
  have hle := hpre.2.1.le
  have hu := unchanged_pushes (ra := ra) hF hpre
  have hm : Mem.Mapped (mod F s).mem s.dmem := fun x hx =>
    hx.elim (fun h => hpre.2.1.mapped x (Or.inl h))
      (fun h => hpre.1.mapped x (inside_append.mpr (Or.inl h)))
  refine ⟨⟨?_, pushAt_mapped (hm.storeInt _ _ _), fun x hx => hu x fun h => hx (Or.inl
    (h.elim id False.elim))⟩, Wf.congr_of_disjoint hu hpre.1 (disjoint_symm hpre.2.1.disj),
    fun i hi => ?_⟩
  · refine (rd_pushAt_other fun j hj => ?_).trans ((rd_store_same _ rfl).trans BitVec.ofInt_toInt)
    constructor <;> bv_omega
  · rw [show rsp s - BitVec.ofNat 64 (8 * i + 16) = rsp s - 8#64 - BitVec.ofNat 64 (8 * i + 8) by
      bv_omega]
    exact rd_pushAt_self (by omega) i hi

-- The memory after a call to a callee with frame size `G` at `k` bytes below `rsp s`.
theorem Fm.call {G k : Nat} {c t : MachineData} {R : MachineData → MachineData → Prop}
    (hk : 8 * rs.length + 8 ≤ k) (hG : k + G ≤ F) (hpre : Pre F A s) (h : Fm F rs s ra m)
    (hc : c.dmem = m) (hrsp : rsp c = rsp s - BitVec.ofNat 64 k) (hrdi : rdi c = rdi s)
    (hp : Post G R c t) (hag : (mod G c).Agree c t) : Fm F rs s ra t.dmem := by
  have hle := hpre.2.1.le
  have hu : Mem.UnchangedOutside (frame G c :: writable s.dmem (rdi s)) m t.dmem := by
    have := hag.2
    simp only [mod, hc, hrdi, (h.keeps hpre).2.2] at this
    exact this
  refine ⟨h.toMid.call (by omega) hG hpre hc hrsp hrdi hp hag, hrdi ▸ hp.1, fun i hi => ?_⟩
  rw [rd_congr hu fun x hx hl => ?_]
  · exact h.saved i hi
  · rcases hl with hl | hl
    · simp only [Mem.Blocks.Inside, or_false, hrsp] at hx hl
      bv_omega
    · refine hpre.2.1.disj x ?_ (inside_append.mpr (Or.inl hl))
      simp only [Mem.Blocks.Inside, or_false] at hx ⊢
      bv_omega

-- The precondition of a callee with frame size `G` at `k` bytes below `rsp s`.
theorem Fm.pre {G k : Nat} {c : MachineData} {A' : MachineData → Prop} (hG : k + G ≤ F)
    (hpre : Pre F A s) (h : Fm F rs s ra m) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - BitVec.ofNat 64 k) (hrdi : rdi c = rdi s) (hA : A' c) : Pre G A' c :=
  h.toMid.pre hG hpre h.wf hc hrsp hrdi hA

-- Stores to `writable` that keep it mapped and keep `len` and `nops` in bounds.
theorem Fm.write (hF : 8 * rs.length + 8 ≤ F) (hpre : Pre F A s) (h : Fm F rs s ra m)
    {m' : Mem 64} (hu : Mem.UnchangedOutside (writable s.dmem (rdi s)) m m')
    (hm : Mem.Mapped (writable s.dmem (rdi s)) m')
    (hlen : (rd m' (wordAt (rdi s) 4)).toNat ≤ nOf s.dmem (rdi s))
    (hnops : (rd m' (wordAt (rdi s) 6)).toNat ≤ 6 * nOf s.dmem (rdi s)) : Fm F rs s ra m' := by
  have hle := hpre.2.1.le
  -- the words of the frame are not in `writable`
  have hfr : ∀ {j}, 8 ≤ j → j ≤ F →
      rd m' (rsp s - BitVec.ofNat 64 j) = rd m (rsp s - BitVec.ofNat 64 j) := fun hj hj' =>
    rd_congr hu fun x hx hw => hpre.2.1.disj x
      (by simp only [Mem.Blocks.Inside, or_false] at hx ⊢; bv_omega) (inside_append.mpr (Or.inl hw))
  have hmid : Mid F s ra m' := by
    refine ⟨(hfr (j := 8) (by omega) (by omega)).trans h.ra, fun x hx => ?_, fun x hx => ?_⟩
    · by_cases hw : Mem.Blocks.Inside x 1 (writable s.dmem (rdi s))
      · exact hm x hw
      · rw [hu x hw]; exact h.map x hx
    · rw [hu x fun hw => hx (Or.inr hw)]; exact h.un x hx
  exact ⟨hmid, hmid.wf hpre hlen hnops, fun i hi =>
    (hfr (by omega) (by omega)).trans (h.saved i hi)⟩

-- The two stores to `m_blocked` keep `Fm`.
theorem Fm.blk (hF : 8 * rs.length + 8 ≤ F) (hpre : Pre F A s) (h : Fm F rs s ra m) (p x : Word) :
    Fm F rs s ra ((m.storeInt (wordAt (rdi s) BLK) 8 p.toInt).storeInt
      (wordAt (rdi s) (BLK + 1)) 8 x.toInt) := by
  have hs := h.wf.struct_lt
  have hwr := (h.keeps hpre).2.2
  simp only [WORDS_eq] at hs
  -- `m_blocked` lies in `writable`
  have hw : ∀ y, Mem.Blocks.Inside y 1 [(wordAt (rdi s) BLK, 16)] →
      Mem.Blocks.Inside y 1 (writable s.dmem (rdi s)) := fun y hy => Or.inr (Or.inl (by
    simp only [Mem.Blocks.Inside, or_false, wordAt, BLK_eq, WORDS_eq] at hy ⊢; bv_omega))
  have hu : Mem.UnchangedOutside [(wordAt (rdi s) BLK, 16)] m
      ((m.storeInt (wordAt (rdi s) BLK) 8 p.toInt).storeInt (wordAt (rdi s) (BLK + 1)) 8 x.toInt) := by
    have hin : ∀ a : Addr, (a - wordAt (rdi s) BLK).toNat + 8 ≤ 16 →
        Mem.Blocks.Inside a 8 [(wordAt (rdi s) BLK, 16)] := fun a h => Or.inl h
    refine .storeInt (.storeInt (fun _ _ => rfl) (hin _ ?_) _) (hin _ ?_) _
    all_goals (simp only [wordAt, BLK_eq]; bv_omega)
  -- `m_size` and `m_traceSize` are not in `m_blocked`
  have hst : ∀ {k}, k ≤ 6 →
      rd ((m.storeInt (wordAt (rdi s) BLK) 8 p.toInt).storeInt (wordAt (rdi s) (BLK + 1)) 8 x.toInt)
        (wordAt (rdi s) k) = rd m (wordAt (rdi s) k) := fun hk => rd_congr hu fun y hy hb => by
    simp only [Mem.Blocks.Inside, or_false, wordAt, BLK_eq] at hy hb; bv_omega
  refine h.write hF hpre (fun y hy => hu y fun hb => hy (hw y hb)) ?_ ?_ ?_
  · exact fun y hy =>
      (h.wf.mapped.storeInt _ _ _ |>.storeInt _ _ _) y (inside_append.mpr (Or.inl (hwr ▸ hy)))
  · rw [hst (by decide), ← h.n hpre]; exact h.wf.len_le
  · rw [hst (by decide), ← h.n hpre]; exact h.wf.nops_le

/-- `ret` from `u` with the memory `Fm` and the registers of the call gives the
postcondition of `Body`. -/
theorem Fm.ret [Host] {R : MachineData → MachineData → Prop} {ls : List Label}
    {I' : CfgLabel → Nat → Unit → MachineData → Prop} {u : MachineData} (hF : 8 ≤ F)
    (hpre : Pre F A s) (h : Fm F rs s ra u.dmem) (hsp : rsp u = rsp s - 8#64)
    (hr : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      u.regs.get64 q = s.regs.get64 q)
    (hR : ∀ t, t.dmem = u.dmem → rax t = rax u → R s t) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post F R s t ∧ (mod F s).Agree s t) u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } :=
  h.toMid.ret hF hpre hsp rfl
    (by simp only [rsp, Reg64s.get64_set64, reduceIte, hsp, BitVec.sub_add_cancel])
    (fun q hq => by
      simp only [Reg64s.get64_set64]
      split
      · simp_all
      · exact hr q hq)
    h.wf (hR _ rfl (by simp [rax]))

end

/-! ## Flags -/

-- The carry flag of `cmp b, a`.
theorem cf_sub (a b : Word) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)) = true) ↔ a.toNat < b.toNat := by
  rw [bne_iff_ne, ne_eq, BitVec.toNat_sub]
  have := a.isLt; have := b.isLt
  constructor <;> intro h <;> omega

theorem cf_sub' (a b : Word) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)) = false) ↔ b.toNat ≤ a.toNat := by
  rw [← Bool.not_eq_true, cf_sub]; omega

-- The zero flag of `cmp b, a`.
theorem z_sub (a b : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a - b) r) = (a == b) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq,
    BitVec.zero_eq]
  constructor <;> intro h <;> bv_omega

theorem nz_sub (a b : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) r) = !(a == b) := by
  rw [CondCode.interp_nz, ← CondCode.interp_z, z_sub]

-- `cmp $k, x; ja` jumps iff `k < x`.
theorem a_sub_imm (x : Word) (k : Nat) (hk : k < 2 ^ 64) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (x - BitVec.ofNat 64 k)
      { cf := (((x - BitVec.ofNat 64 k).toNat : Int) != (x.toNat : Int) - (OfNat.ofNat k : Int)),
        af, of }) = decide (k < x.toNat) := by
  rw [CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_eq_false_iff_ne,
    decide_eq_true_eq, ne_eq, BitVec.zero_eq]
  rw [BitVec.toNat_sub, show (OfNat.ofNat k : Int) = (k : Int) from rfl]
  have := x.isLt
  constructor
  · intro ⟨h1, h2⟩; bv_omega
  · intro h; constructor <;> bv_omega

-- `cmp $k, x; jbe` jumps iff `x ≤ k`.
theorem be_sub_imm (x : Word) (k : Nat) (hk : k < 2 ^ 64) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result (x - BitVec.ofNat 64 k)
      { cf := (((x - BitVec.ofNat 64 k).toNat : Int) != (x.toNat : Int) - (OfNat.ofNat k : Int)),
        af, of }) = decide (x.toNat ≤ k) := by
  rw [CondCode.interp_be, StatusFlags.cf_from_result, StatusFlags.zf_from_result, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq, BitVec.zero_eq, decide_eq_true_eq]
  rw [BitVec.toNat_sub, show (OfNat.ofNat k : Int) = (k : Int) from rfl]
  have := x.isLt
  constructor
  · rintro (h | h) <;> bv_omega
  · intro h; by_cases h' : x.toNat < k
    · left; bv_omega
    · right; bv_omega

-- The flags of `test v, v`.
theorem z_test (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (v &&& v) r) = (v == 0) := by
  simp [CondCode.interp, StatusFlags.from_result]

theorem sf_test (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.s.interp (StatusFlags.from_result (v &&& v) r) = v.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

theorem ns_test (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.ns.interp (StatusFlags.from_result (v &&& v) r) = !v.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

end Kit

end Bbu
