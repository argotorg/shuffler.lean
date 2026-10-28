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
* `Wf.sep_ops`, `Wf.sep_blk`: the ops buffer and `blocked` do not overlap the struct.
* `FrameOk.sep_struct`: the frame does not overlap the struct.
* `sep_of_disjoint`: `Disjoint` of two blocks as `Nat` inequalities.
* `Wf.struct_lt`, `Wf.ops_lt`, `Wf.blk_lt`, `FrameOk.le`: the blocks do not wrap.

The model state (`Bbu`):
* `stOf_eq`: the model state is `st` if `len`, `pending`, `nops`, each slot and each
  op in memory agree with `st`.

Memory in a function body (`Bbu.Kit`, use `open Kit`). `Mid F s ra m`: `m` is the
memory of a body for the call `s` with frame size `F`.
* `Mid.init`: the memory after the call.
* `Mid.store`, `Mid.store_w`: a store to `mod F s`, a store to `writable`.
* `Mid.call`, `Mid.pre`: a call to a callee with frame size `G`.
* `Mid.keeps`, `Mid.wf`: the environment and the regions stay; the struct stays
  well formed if `len` and `nops` stay in bounds.
* `Mid.ret`: `ret` gives the postcondition of `Body`.
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

-- The struct is the union of three blocks of `writable` and `readable`.
theorem inside_struct {x : Addr} (h : Mem.Blocks.Inside x 1 [(S, 8 * WORDS)]) :
    Mem.Blocks.Inside x 1 (writable m S ++ readable m S) := by
  simp only [Mem.Blocks.Inside, or_false, WORDS] at h
  rw [inside_append]
  by_cases h1 : (x - S).toNat < 24
  · exact Or.inl (Or.inl (by omega))
  by_cases h2 : (x - S).toNat < 64
  · exact Or.inr (Or.inl (by simp only [wordAt]; bv_omega))
  · exact Or.inl (Or.inr (Or.inl (by simp only [wordAt, STACK]; bv_omega)))

-- A change outside the header words 3 to 7 keeps `writable`.
theorem writable_congr {m' : Mem 64} {l : List (Addr × Nat)} (h : Mem.UnchangedOutside l m m')
    (hd : Mem.Blocks.Disjoint (readable m S) l) : writable m' S = writable m S := by
  simp only [writable, nOf, opsOf, blkOf, hdr_congr h hd (k := 3) (by omega) (by omega),
    hdr_congr h hd (k := 6) (by omega) (by omega), hdr_congr h hd (k := 7) (by omega) (by omega)]

-- The blocks of `writable`: the words 0 to 2 of the header, the stack and dest arrays,
-- the ops buffer and `blocked`.
theorem inside_writable {a : Addr} {n : Nat}
    (h : (a - S).toNat + n ≤ 24 ∨ (8 * STACK ≤ (a - S).toNat ∧ (a - S).toNat + n ≤ 8 * WORDS)
      ∨ (a - opsOf m S).toNat + n ≤ 96 * nOf m S ∨ (a - blkOf m S).toNat + n ≤ 16) :
    Mem.Blocks.Inside a n (writable m S) := by
  simp only [writable, Mem.Blocks.Inside, wordAt, STACK, WORDS, or_false] at h ⊢
  bv_omega

-- A load from the struct succeeds.
theorem Wf.isSome_struct (hw : Wf m S) {a : Addr} {n : Nat} (h : (a - S).toNat + n ≤ 8 * WORDS) :
    (m.loadInt a n).isSome :=
  Mem.Mapped.loadInt_isSome (bs := [(S, 8 * WORDS)]) (fun x hx => hw.mapped x (inside_struct hx))
    (Or.inl h)

theorem disjoint_head {a b : Addr} {n k : Nat} {l : List (Addr × Nat)}
    (h : Mem.Blocks.Disjoint [(a, n)] ((b, k) :: l)) : Mem.Blocks.Disjoint [(a, n)] [(b, k)] :=
  fun x hx hy => h x hx (hy.elim Or.inl False.elim)

-- The ops buffer, `blocked` and the struct do not overlap.
theorem Wf.sep_ops (hw : Wf m S) (hn : 0 < nOf m S) :
    (opsOf m S).toNat + 96 * nOf m S ≤ S.toNat ∨ S.toNat + 8 * WORDS ≤ (opsOf m S).toNat :=
  (sep_of_disjoint (disjoint_head hw.disj_struct) (by decide) (by omega)).symm

theorem Wf.sep_blk (hw : Wf m S) :
    (blkOf m S).toNat + 16 ≤ S.toNat ∨ S.toNat + 8 * WORDS ≤ (blkOf m S).toNat :=
  (sep_of_disjoint (disjoint_head (fun x hx hy => hw.disj_struct x hx (Or.inr hy)))
    (by decide) (by decide)).symm

-- The frame of a call does not overlap the struct.
theorem FrameOk.sep_struct {F : Nat} {s : MachineData} (hf : FrameOk F s) (hF : 0 < F) :
    (rsp s).toNat ≤ (rdi s).toNat ∨ (rdi s).toNat + 8 * WORDS ≤ (rsp s).toNat - F := by
  have hle := hf.le
  have := sep_of_disjoint (a := rsp s - BitVec.ofNat 64 F) (n := F) (b := rdi s) (k := 8 * WORDS)
    (fun x hx hy => hf.disj x hx (inside_struct hy)) hF (by decide)
  bv_omega

-- The frame of a call does not overlap the ops buffer.
theorem FrameOk.sep_ops {F : Nat} {s : MachineData} (hf : FrameOk F s) (hF : 0 < F)
    (hn : 0 < nOf s.dmem (rdi s)) :
    (rsp s).toNat ≤ (opsOf s.dmem (rdi s)).toNat
      ∨ (opsOf s.dmem (rdi s)).toNat + 96 * nOf s.dmem (rdi s) ≤ (rsp s).toNat - F := by
  have hle := hf.le
  have := sep_of_disjoint (a := rsp s - BitVec.ofNat 64 F) (n := F) (b := opsOf s.dmem (rdi s))
    (k := 96 * nOf s.dmem (rdi s))
    (fun x hx hy => hf.disj x hx (by
      rw [inside_append]
      exact Or.inl (by simp only [writable, Mem.Blocks.Inside] at hy ⊢; exact Or.inr (Or.inr (Or.inl (hy.resolve_right id))))))
    hF (by omega)
  bv_omega

end

/-! ## The model state -/

section
variable {m : Mem 64} {S : Addr}

theorem len_stOf : (stOf m S).len = (rd m (wordAt S 0)).toNat := by
  simp [St.len, stOf]

theorem nops_stOf : (stOf m S).ops.length = (rd m (wordAt S 2)).toNat := by
  simp [stOf]

theorem val_stOf {i : Nat} (hi : i < (rd m (wordAt S 0)).toNat) :
    (stOf m S).val i = rd m (wordAt S (STACK + i)) := by
  simp [St.val, stOf, hi, slotOf]

theorem dest_stOf {i : Nat} (hi : i < (rd m (wordAt S 0)).toNat) :
    (stOf m S).dest i = (rd m (wordAt S (DEST + i))).toNat := by
  simp [St.dest, stOf, hi, slotOf]

-- The model state is `st` if the words in memory agree with `st`.
theorem stOf_eq {st : St} (hlen : (rd m (wordAt S 0)).toNat = st.len)
    (hpend : (rd m (wordAt S 1)).toNat = st.pending)
    (hnops : (rd m (wordAt S 2)).toNat = st.ops.length)
    (hslot : ∀ i (hi : i < st.len), slotOf m S i = st.slots[i])
    (hop : ∀ i (hi : i < st.ops.length), opOf m S i = st.ops[i]) : stOf m S = st := by
  obtain ⟨slots, pending, ops⟩ := st
  simp only [St.len] at hlen hslot
  simp only [stOf, hlen, hpend, hnops, St.mk.injEq, true_and]
  constructor
  · exact List.ext_getElem (by simp) fun i h1 h2 => by simpa using hslot i h2
  · exact List.ext_getElem (by simp) fun i h1 h2 => by simpa using hop i h2

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

-- The struct stays well formed if `len` and `nops` stay in bounds.
theorem Mid.wf (hpre : Pre F A s) (h : Mid F s ra m)
    (hlen : (rd m (wordAt (rdi s) 0)).toNat ≤ 256)
    (hnops : (rd m (wordAt (rdi s) 2)).toNat ≤ 6 * nOf s.dmem (rdi s)) : Wf m (rdi s) :=
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
  · apply MachineData.stackBelow_of_add_eight
    simp only [MachineData.pushRa, Reg64s.get64_set64, reduceIte]
    rw [show u.regs.get64 .rsp = rsp s from husp]
    exact BitVec.sub_add_cancel _ _

end

end Kit

end Bbu
