import BbuKraken.Contracts
import BbuKraken.ModelLemmas
import BbuKraken.Kit

/-!
The body triple of `produce` (`c/bbu/produce.S`). The saved registers `rbx`,
`rbp`, `r12` and `r13` hold the struct, the offset `d`, the target value `v` of
`d` and the encoded copy of `v`. Every call is at `rsp s - 40`.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true
-- `notq r`: Kraken has no spec for it. It does not change the flags.
@[spec] theorem not_reg_spec [Host] [FunDecls] (asz : Width) (r : Reg64)
    {Q : PUnit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (~~~(s.regs.get64 r)) } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hpre

namespace Bbu
namespace Produce

/-! ## Model lemmas -/

-- The part of `produce` after `emit`.
def tail (d : Nat) (st : St) : M St :=
  if positionOf st d ≠ some (st.len - 1) then .error .assertion
  else .ok { st with pendingGenerations := st.pendingGenerations - 1 }

theorem produce_eq (e : Env) (st : St) (d : Nat) : produce e st d = (emit e st d).bind (tail d) := rfl

-- No copy of `v` is in reach.
abbrev Far (st : St) (v : Word) : Prop :=
  ∀ c, shallowestCopyPosition st v = some c → 15 < st.len - 1 - c

section
variable {e : Env} {st : St} {d c : Nat}

theorem filter_none {v : Word} (hf : Far st v) :
    (shallowestCopyPosition st v).filter (fun c => st.len - 1 - c ≤ MAX_DUP_DEPTH) = none := by
  cases hc : shallowestCopyPosition st v with
  | none => rfl
  | some c => have := hf c hc; simp [MAX_DUP_DEPTH]; omega

theorem emit_zero (h : e.target[d]! = 0) : emit e st d = add st 0 d (.push 0) := by
  simp [emit, h]

theorem emit_dup (h0 : e.target[d]! ≠ 0) (hc : shallowestCopyPosition st e.target[d]! = some c)
    (hb : st.len - 1 - c ≤ 15) : emit e st d = add st e.target[d]! d (.dup (st.len - c)) := by
  have hf : (shallowestCopyPosition st e.target[d]!).filter
        (fun c => st.len - 1 - c ≤ MAX_DUP_DEPTH)
      = some c := by
    simp only [hc, Option.filter_some, MAX_DUP_DEPTH, hb, decide_true, ite_true]
  unfold emit
  simp only [h0, ite_false]
  rw [hf]

theorem emit_push (h0 : e.target[d]! ≠ 0) (hf : Far st e.target[d]!)
    (hp : (isFree e.target[d]! || isSpilled e e.target[d]!) = true) :
    emit e st d = add st e.target[d]! d (.push e.target[d]!) := by
  unfold emit
  simp only [h0, ite_false]
  rw [filter_none hf]
  simp only [hp, ite_true]

theorem emit_blocked (h0 : e.target[d]! ≠ 0) (hf : Far st e.target[d]!)
    (hp : (isFree e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopyPosition st e.target[d]! = some c) :
    emit e st d = .error (.blocked c (st.len - 1 - c - 15)) := by
  unfold emit
  simp only [h0, ite_false]
  rw [filter_none hf]
  simp only [hp, hc, MAX_DUP_DEPTH]
  rfl

theorem emit_none (h0 : e.target[d]! ≠ 0)
    (hp : (isFree e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopyPosition st e.target[d]! = none) : emit e st d = .error .assertion := by
  unfold emit
  simp only [h0, ite_false, hc, Option.filter_none, hp]
  rfl

theorem produce_err {e : Env} {st : St} {d : Nat} {x : Err} (h : emit e st d = .error x) :
    produce e st d = .error x := by
  rw [produce_eq, h]; rfl

theorem tail_bad {st : St} (h : positionOf st d ≠ some (st.len - 1)) :
    tail d st = .error .assertion := by
  simp [tail, h]

theorem tail_ok {st : St} (h : positionOf st d = some (st.len - 1)) :
    tail d st = .ok { st with pendingGenerations := st.pendingGenerations - 1 } := by
  simp [tail, h]

theorem pending_zero {st : St} (h : st.pendingGenerations = 0) :
    { st with pendingGenerations := st.pendingGenerations - 1 } = st := by
  cases st; simp_all

end

-- The registers that `produce` saves, in the order of the pushes.
abbrev regs : List Reg64 := [.r13, .r12, .rbp, .rbx]

-- The memory of `produce`: the frame of 80 bytes, the saved words and the struct.
abbrev Fm := Kit.Fm 80 regs

section
variable {s : MachineData} {ra : Int64}

-- A store to 8 bytes in `writable` that keeps the words 0 and 2 of the struct.
theorem Fm.store {m : Mem 64} {a : Addr} {v : Int} (hpre : Pre 80 produceA s) (h : Fm s ra m)
    (hin : ∀ x, Mem.Blocks.Inside x 1 [(a, 8)] → Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)))
    (h0 : rd (m.storeInt a 8 v) (wordAt (rdi s) 0) = rd m (wordAt (rdi s) 0))
    (h2 : rd (m.storeInt a 8 v) (wordAt (rdi s) 2) = rd m (wordAt (rdi s) 2)) :
    Fm s ra (m.storeInt a 8 v) := by
  have hwr := (h.keeps hpre).2.2
  have hu : Mem.UnchangedOutside [(a, 8)] m (m.storeInt a 8 v) :=
    .storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  refine Kit.Fm.write (by decide) hpre h (fun y hy => hu y fun hb => hy (hin y hb))
    (fun y hy => (h.wf.mapped.storeInt _ _ _) y (inside_append.mpr (Or.inl (hwr ▸ hy)))) ?_ ?_
  · rw [h0]; exact h.wf.len_le
  · rw [h2, ← h.n hpre]; exact h.wf.nops_le

end

/-! ## Normal forms of `kvcgen64` terms -/

section
variable {s : MachineData} {ra : Int64}

-- The memory after the pushes of the entry block, as `kvcgen64` gives it.
theorem pushes_eq : (((Mem.storeInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8
    (s.pushRa ra).regs.r13.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64) 8 (s.pushRa ra).regs.r12.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64) 8
      (s.pushRa ra).regs.rbp.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64) 8
      (s.pushRa ra).regs.rbx.toBitVec.toInt = Kit.pushes s ra regs := rfl
end

/-! ## The struct in memory -/

section
variable {m : Mem 64} {S : Addr}

theorem wordAt_mul (a x : Word) : wordAt a x.toNat = a + x * 8#64 := by
  simp only [wordAt]
  bv_omega

-- The load of the target value at the offset `x`.
theorem rd_target {x : Word} (hx : x.toNat < nOf m S) :
    rd m (wordAt (rd m (wordAt S 4) + x * 8#64) 0) = (envOf m S).target[x.toNat]! := by
  have := Nat.lt_of_lt_of_le hx (Nat.le_refl _)
  rw [target_get hx, tgtOf]
  congr 1
  simp only [wordAt, nOf] at *
  bv_omega

theorem tgt_isSome (hw : Wf m S) {d : Nat} (hd : d < nOf m S) :
    (m.loadInt (wordAt (tgtOf m S) d) 8).isSome = true := by
  have := hw.tgt_lt
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr (Or.inr (Or.inr (Or.inl ?_))))
  simp only [wordAt]; bv_omega

-- A store to the word `m_pendingGenerations` sets `pendingGenerations`.
theorem stOf_setPending (hw : Wf m S) (x : Word) :
    stOf (m.storeInt (wordAt S 1) 8 x.toInt) S
      = { stOf m S with pendingGenerations := x.toNat } := by
  have hs := hw.struct_lt
  have hn : _ ≤ 1024 := hw.n_le
  simp only [WORDS_eq] at hs
  have hk : ∀ k, k < 2056 → k ≠ 1 →
      rd (m.storeInt (wordAt S 1) 8 x.toInt) (wordAt S k) = rd m (wordAt S k) := fun k hk h1 =>
    rd_store_other _ (by simp only [wordAt]; bv_omega)
  have hop : ∀ j, j < 12 * nOf m S →
      rd (m.storeInt (wordAt S 1) 8 x.toInt) (wordAt (opsOf m S) j) = rd m (wordAt (opsOf m S) j) :=
    fun j hj => rd_storeInt_of_disjoint fun y hy ho => hw.disj_struct y
      (by simp only [Mem.Blocks.Inside, or_false, WORDS_eq] at hy ⊢; bv_omega)
      (Or.inl (by simp only [Mem.Blocks.Inside, or_false] at ho ⊢; bv_omega))
  have hlen : _ ≤ 1024 := hw.len_le
  have hnops := hw.nops_le
  have ho : opsOf (m.storeInt (wordAt S 1) 8 x.toInt) S = opsOf m S := hk 6 (by omega) (by omega)
  simp only [stOf, hk 0 (by omega) (by omega), hk 2 (by omega) (by omega),
    rd_store_same _ rfl, BitVec.ofInt_toInt]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [slotOf, STACK, DEST_eq, hk (8 + i) (by omega) (by omega),
      hk (1032 + i) (by omega) (by omega)]
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [opOf, ho, hop (2 * i) (by omega), hop (2 * i + 1) (by omega)]

end

/-! ## The `blocked` stores -/

section
variable {s : MachineData} {ra : Int64}

-- A store to `blocked` keeps the words of the struct.
theorem rd_blk_store {m M : Mem 64} {S : Addr} (hw : Wf m S) {k j : Nat} (hk : k < WORDS)
    (hj : j < 2) (v : Int) :
    rd (M.storeInt (wordAt (blkOf m S) j) 8 v) (wordAt S k) = rd M (wordAt S k) := by
  have hb := hw.blk_lt
  refine rd_storeInt_of_disjoint fun x hx hy => hw.blk_disj hk x hy ?_
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

end

/-! ## The return -/

section
variable {s : MachineData} {ra : Int64}

-- The pops of `.LB26` read the saved words.
theorem Fm.pops {m : Mem 64} (h : Fm s ra m) {a : Addr} (ha : a = rsp s - 40#64) :
    rd m a = s.regs.rbx.toBitVec ∧ rd m (a + 8#64) = s.regs.rbp.toBitVec
      ∧ rd m (a + 8#64 + 8#64) = s.regs.r12.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64) = s.regs.r13.toBitVec := by
  subst ha
  refine ⟨h.saved 3 (by decide), ?_, ?_, ?_⟩
  · rw [show rsp s - 40#64 + 8#64 = rsp s - 32#64 by bv_omega]; exact h.saved 2 (by decide)
  · rw [show rsp s - 40#64 + 8#64 + 8#64 = rsp s - 24#64 by bv_omega]; exact h.saved 1 (by decide)
  · rw [show rsp s - 40#64 + 8#64 + 8#64 + 8#64 = rsp s - 16#64 by bv_omega]
    exact h.saved 0 (by decide)

end

-- The result `r` of the model as the status `x` and the memory `m`: `Res` with `x` for `rax`.
def RW (S : Addr) (r : M St) (m : Mem 64) (x : Word) : Prop :=
  match r with
  | .ok st' => x = 0#64 ∧ stOf m S = st'
  | .error (.blocked pos excess) =>
    x = -1#64 ∧ rd m (blkOf m S) = BitVec.ofNat 64 pos
      ∧ rd m (wordAt (blkOf m S) 1) = BitVec.ofNat 64 excess
  | .error .assertion => x = -2#64

section
variable {S : Addr} {r : M St} {m : Mem 64} {x : Word}

theorem RW.res {t : MachineData} (h : RW S r m x) (hm : t.dmem = m) (hx : rax t = x) :
    Res S r (fun st' => rax t = 0#64 ∧ stOf t.dmem S = st') t := by
  subst hm hx
  rcases r with (⟨p, e⟩ | _) | a <;> exact h

theorem RW.of_res {t : MachineData} (h : Res S r (fun st' => rax t = 0#64 ∧ stOf t.dmem S = st') t) :
    RW S r t.dmem (rax t) := by
  rcases r with (⟨p, e⟩ | _) | a <;> exact h

-- A status that is not 0 is an error, which `bind` passes on.
theorem RW.bind_err {f : St → M St} (h : RW S r m x) (hx : x ≠ 0#64) : RW S (r.bind f) m x := by
  rcases r with (⟨p, e⟩ | _) | a
  · exact h
  · exact h
  · exact absurd h.1 hx

theorem RW.ok_of_zero (h : RW S r m 0#64) : ∃ st', r = .ok st' ∧ stOf m S = st' := by
  rcases r with (⟨p, e⟩ | _) | a
  · exact absurd h.1 (by decide)
  · exact absurd (show (0#64 : Word) = -2#64 from h) (by decide)
  · exact ⟨a, rfl, h.2⟩

end
section
variable (s : MachineData) (ra : Int64)

-- The offset `d`, its target value `v` and the copy of `v`.
abbrev dd : Nat := (rsi s).toNat
abbrev vv : Word := (env s).target[(rsi s).toNat]!
abbrev cp : Option Nat := shallowestCopyPosition (st s) (vv s)

-- The frame and the registers that `produce` does not change.
structure Base (t : MachineData) : Prop where
  fm : Fm s ra t.dmem
  rsp : t.regs.rsp.toBitVec = rsp s - 40#64
  r14 : t.regs.r14.toBitVec = s.regs.r14.toBitVec
  r15 : t.regs.r15.toBitVec = s.regs.r15.toBitVec

-- Before `emit`: the struct in `rbx`, `d` in `rbp`, `v` in `r12` and the copy in `r13`.
structure Lp (t : MachineData) : Prop extends Base s ra t where
  st : stOf t.dmem (rdi s) = st s
  rbx : t.regs.rbx.toBitVec = rdi s
  rbp : t.regs.rbp.toBitVec = rsi s
  r12 : t.regs.r12.toBitVec = vv s
  r13 : t.regs.r13.toBitVec = encOpt (cp s)
  v0 : vv s ≠ 0

-- `.LB31`: no copy is in reach.
def At31 (t : MachineData) : Prop := Lp s ra t ∧ Far (st s) (vv s)
-- `.LB39`: `v` is not free.
def At39 (t : MachineData) : Prop := At31 s ra t ∧ isFree (vv s) = false
-- `.LB32`: `emit` pushes `v`.
def At32 (t : MachineData) : Prop :=
  At31 s ra t ∧ (isFree (vv s) || isSpilled (env s) (vv s)) = true
-- `.LB34`: `emit` fails.
def At34 (t : MachineData) : Prop :=
  At31 s ra t ∧ (isFree (vv s) || isSpilled (env s) (vv s)) = false
-- `.LB42`: `emit` dups the copy `c`.
def At42 (t : MachineData) : Prop :=
  Lp s ra t ∧ ∃ c, cp s = some c ∧ (st s).len - 1 - c ≤ 15
-- `.LB41`: `v` is 0.
def At41 (t : MachineData) : Prop :=
  Base s ra t ∧ stOf t.dmem (rdi s) = st s ∧ t.regs.rbx.toBitVec = rdi s
    ∧ t.regs.rbp.toBitVec = rsi s ∧ t.regs.rdi.toBitVec = rdi s ∧ t.regs.rsi.toBitVec = rsi s
    ∧ vv s = 0
-- `.LB30`: `emit` is the `add` that returned the status in `r12`.
def At30 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.rbx.toBitVec = rdi s ∧ t.regs.rbp.toBitVec = rsi s
    ∧ ∃ v op, emit (env s) (st s) (dd s) = add (st s) v (dd s) op
      ∧ RW (rdi s) (add (st s) v (dd s) op) t.dmem t.regs.r12.toBitVec
-- `.LB43`: `emit` returned `st'`.
def At43 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.rbx.toBitVec = rdi s ∧ t.regs.rbp.toBitVec = rsi s
    ∧ t.regs.r12.toBitVec = 0#64
    ∧ ∃ st', emit (env s) (st s) (dd s) = .ok st' ∧ stOf t.dmem (rdi s) = st'
-- `.LB36` and `.LB38`: `produce` fails an assertion.
def Asrt (t : MachineData) : Prop :=
  Base s ra t ∧ produce (env s) (st s) (dd s) = .error .assertion
-- `.LB28`: the result is in `r12`.
def At28 (t : MachineData) : Prop :=
  Base s ra t ∧ RW (rdi s) (produce (env s) (st s) (dd s)) t.dmem t.regs.r12.toBitVec

def V : Label → MachineData → Nat
  | ".LB28", _ => 0
  | ".LB30", _ | ".LB43", _ | ".LB36", _ | ".LB38", _ => 1
  | _, _ => 2

end

-- The flags of `testb $1` and `cmpq $1` at `.LB29`.
theorem take_and1 (v : Word) : (v.take 8 &&& 1#8).toNat = v.toNat % 2 := by
  unfold BitVec.take
  rw [BitVec.toNat_and, BitVec.extractLsb'_toNat]
  simp

theorem isFree_even {v : Word} (h0 : v ≠ 0) (h : v.take 8 &&& 1#8 = 0#8) : isFree v = false := by
  have he : v.toNat % 2 = 0 := by rw [← take_and1, h]; rfl
  have h0' : ¬v = 0#64 := h0
  simp [isFree, he, h0']

theorem isFree_odd {v : Word} (h : ¬v.take 8 &&& 1#8 = 0#8) (h1 : ¬v - 1#64 = 0#64) :
    isFree v = true := by
  have ho : v.toNat % 2 = 1 := by
    have : (v.take 8 &&& 1#8).toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    rw [take_and1] at this
    omega
  have h1' : v ≠ 1#64 := by bv_omega
  simp [isFree, ho, h1']

theorem isFree_one {v : Word} (h1 : v - 1#64 = 0#64) : isFree v = false := by
  have : v = 1#64 := by bv_omega
  subst this; decide

/-! ## `.LB32` -/

section
variable {m : Mem 64} {S : Addr}

theorem wordAt_zero (a : Addr) : wordAt a 0 = a := by simp [wordAt]

theorem blk_ptr_store (hw : Wf m S) (v : Int) :
    rd (m.storeInt (rd m (S + 56#64)) 8 v) (S + 56#64) = blkOf m S := by
  have h := rd_blk_store (M := m) hw (k := 7) (j := 0) (by decide) (by decide) v
  rw [wordAt_zero] at h
  exact h

-- The two stores of `.LB32`.
def blkStores (m : Mem 64) (S : Addr) (p x : Word) : Mem 64 :=
  (m.storeInt (wordAt (blkOf m S) 0) 8 p.toInt).storeInt (wordAt (blkOf m S) 1) 8 x.toInt

theorem blkStores_eq (hw : Wf m S) (p x : Word) :
    (m.storeInt (rd m (S + 56#64)) 8 p.toInt).storeInt
      (rd (m.storeInt (rd m (S + 56#64)) 8 p.toInt) (S + 56#64) + 8#64) 8 x.toInt
      = blkStores m S p x := by
  rw [blk_ptr_store hw, blkStores, wordAt_zero]
  rfl

theorem blkStores_rd (hw : Wf m S) (p x : Word) :
    rd (blkStores m S p x) (blkOf (blkStores m S p x) S) = p
      ∧ rd (blkStores m S p x) (wordAt (blkOf (blkStores m S p x) S) 1) = x := by
  have hb := hw.blk_lt
  have hB : blkOf (blkStores m S p x) S = blkOf m S := by
    show rd (blkStores m S p x) (wordAt S 7) = _
    unfold blkStores
    rw [rd_blk_store hw (by decide) (by decide), rd_blk_store hw (by decide) (by decide)]
    rfl
  rw [hB]
  unfold blkStores
  constructor
  · rw [rd_store_other, rd_store_same _ (wordAt_zero _), BitVec.ofInt_toInt]
    simp only [wordAt]; bv_omega
  · rw [rd_store_same _ rfl, BitVec.ofInt_toInt]

theorem blk_isSome0 (hw : Wf m S) : (m.loadInt (rd m (S + 56#64)) 8).isSome = true := by
  have h := hw.blk_isSome hw.mapped (k := 0) (by decide)
  rw [wordAt_zero] at h
  exact h

theorem blk_isSome1 (hw : Wf m S) (v : Int) :
    ((m.storeInt (rd m (S + 56#64)) 8 v).loadInt
      (rd (m.storeInt (rd m (S + 56#64)) 8 v) (S + 56#64) + 8#64) 8).isSome = true := by
  rw [blk_ptr_store hw]
  exact hw.blk_isSome (hw.mapped.storeInt _ _ _) (k := 1) (by decide)

theorem hdr_isSome0 (hw : Wf m S) : (m.loadInt S 8).isSome = true := by
  have h := hw.word_isSome hw.mapped (k := 0) (by decide)
  rw [wordAt_zero] at h
  exact h

end

theorem encOpt_msb {c : Nat} (h : c < 1024) : (encOpt (some c)).msb = false := by
  rw [encOpt, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
  omega

-- The value at the position that `shallowestCopyPosition` returns.
theorem val_of_copy {st : St} {v : Word} {c : Nat} (h : shallowestCopyPosition st v = some c) :
    st.val c = v := by
  have := List.find?_some h
  simpa using this

/-! ## Calls -/

section
variable {s : MachineData} {ra : Int64}

-- A callee keeps a register that it may not change.
theorem keep {G : Nat} {c u : MachineData} (hag : (mod G c).Agree c u) (r : Reg64)
    (hr : r ∉ (mod G c).regs := by simp [mod]) : u.regs.get64 r = c.regs.get64 r :=
  hag.1 r hr

theorem Base.call_isSome {t : MachineData} (hpre : Pre 80 produceA s) (hb : Base s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true := by
  rw [hb.rsp]; exact hb.fm.call_isSome (by decide) hpre

-- The precondition of a call from `t` to a callee with frame size `G`.
theorem Base.pre {t c : MachineData} {G : Nat} {A : MachineData → Prop} (hpre : Pre 80 produceA s)
    (hb : Base s ra t) (hG : G ≤ 40) (hc : c.dmem = t.dmem) (hrsp : c.regs.rsp = t.regs.rsp)
    (hrdi : rdi c = rdi s) (hA : A c) : Pre G A c :=
  Kit.Fm.pre (k := 40) (by omega) hpre hb.fm hc (by simp only [Reg64s.get64_rsp, hrsp]; exact hb.rsp)
    hrdi hA

-- The state `u` after a call from `t`.
theorem Base.call {t c u : MachineData} {G : Nat} {R : MachineData → MachineData → Prop}
    (hpre : Pre 80 produceA s) (hb : Base s ra t) (hp : Post G R c u)
    (hag : (mod G c).Agree c u) (hG : G ≤ 40) (hc : c.dmem = t.dmem)
    (hrsp : c.regs.rsp = t.regs.rsp) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hrdi : rdi c = rdi s) : Base s ra u where
  fm := Kit.Fm.call (k := 40) (by decide) (by omega) hpre hb.fm hc
    (by simp only [Reg64s.get64_rsp, hrsp]; exact hb.rsp) hrdi hp hag
  rsp := by
    have := keep hag .rsp
    simp only [Reg64s.get64_rsp, hrsp] at this
    rw [this]; exact hb.rsp
  r14 := by
    have := keep hag .r14
    simp only [Reg64s.get64_r14, h14] at this
    rw [this]; exact hb.r14
  r15 := by
    have := keep hag .r15
    simp only [Reg64s.get64_r15, h15] at this
    rw [this]; exact hb.r15

-- The bounds of `push` and `dup` hold at the entry.
theorem Fm.pushA {m : Mem 64} {c : MachineData} (hpre : Pre 80 produceA s) (h : Fm s ra m)
    (hc : c.dmem = m) (hrdi : rdi c = rdi s) (hst : stOf m (rdi s) = st s) : pushA c := by
  have hn := h.n hpre
  obtain ⟨-, -, -, hl, ho⟩ := hpre
  show (stOf c.dmem (rdi c)).len < 1024
    ∧ (stOf c.dmem (rdi c)).trace.length < 6 * nOf c.dmem (rdi c)
  rw [hc, hrdi, hst, hn]
  exact ⟨hl, ho⟩

theorem Fm.dupA {m : Mem 64} {c : MachineData} (hpre : Pre 80 produceA s) (h : Fm s ra m)
    (hc : c.dmem = m) (hrdi : rdi c = rdi s) (hst : stOf m (rdi s) = st s)
    (hsi : (rsi c).toNat < (st s).len) : dupA c := by
  obtain ⟨hl, ho⟩ := h.pushA hpre hc hrdi hst
  refine ⟨?_, hl, ho⟩
  show _ < (stOf c.dmem (rdi c)).len
  rw [hc, hrdi, hst]
  exact hsi

-- A call that keeps the model state keeps `Lp`.
theorem Lp.call {t c u : MachineData} {G : Nat} {R : MachineData → MachineData → Prop}
    (hpre : Pre 80 produceA s) (hl : Lp s ra t) (hp : Post G R c u)
    (hag : (mod G c).Agree c u) (hG : G ≤ 40) (hc : c.dmem = t.dmem)
    (hrsp : c.regs.rsp = t.regs.rsp) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hrbx : c.regs.rbx = t.regs.rbx)
    (hrbp : c.regs.rbp = t.regs.rbp) (h12 : c.regs.r12 = t.regs.r12)
    (h13 : c.regs.r13 = t.regs.r13) (hrdi : rdi c = rdi s)
    (hst : stOf u.dmem (rdi s) = Bbu.st s) : Lp s ra u where
  toBase := hl.toBase.call hpre hp hag hG hc hrsp h14 h15 hrdi
  st := hst
  rbx := by
    have := keep hag .rbx
    simp only [Reg64s.get64_rbx, hrbx] at this
    rw [this]; exact hl.rbx
  rbp := by
    have := keep hag .rbp
    simp only [Reg64s.get64_rbp, hrbp] at this
    rw [this]; exact hl.rbp
  r12 := by
    have := keep hag .r12
    simp only [Reg64s.get64_r12, h12] at this
    rw [this]; exact hl.r12
  r13 := by
    have := keep hag .r13
    simp only [Reg64s.get64_r13, h13] at this
    rw [this]; exact hl.r13
  v0 := hl.v0

-- `Base` and `Lp` only read the registers and the memory.
theorem Base.congr {t t' : MachineData} (h : Base s ra t) (hm : t'.dmem = t.dmem)
    (hr : t'.regs = t.regs) : Base s ra t' :=
  ⟨hm ▸ h.fm, hr ▸ h.rsp, hr ▸ h.r14, hr ▸ h.r15⟩

theorem Lp.congr {t t' : MachineData} (h : Lp s ra t) (hm : t'.dmem = t.dmem)
    (hr : t'.regs = t.regs) : Lp s ra t' :=
  { toBase := h.toBase.congr hm hr, st := hm ▸ h.st, rbx := hr ▸ h.rbx, rbp := hr ▸ h.rbp,
    r12 := hr ▸ h.r12, r13 := hr ▸ h.r13, v0 := h.v0 }

theorem Base.set12 {u : MachineData} (h : Base s ra u) (x : UInt64) :
    Base s ra { u with regs := { u.regs with r12 := x } } :=
  ⟨h.fm, h.rsp, h.r14, h.r15⟩

theorem entry_stack40 (x : Word) : (x - 8#64 - (x - 40#64)).toNat < 2 ^ 63 := by
  bv_omega

-- Each state of the cfg is at or below the entry.
theorem Base.stack {t : MachineData} (h : Base s ra t) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    simp only [Reg64s.get64_rsp, pushRa_rsp, h.rsp]
    exact entry_stack40 _)

-- The result of `push` and `dup` as the result of `add` in the terms of `s`.
theorem push_res {c u : MachineData} {v : Word} (h : pushR c u) (hrdi : rdi c = rdi s)
    (hst : stOf c.dmem (rdi s) = st s) (hv : rsi c = v) (hd : (rdx c).toNat = dd s) :
    Res (rdi s) (add (st s) v (dd s) (.push v))
      (fun st' => rax u = 0#64 ∧ stOf u.dmem (rdi s) = st') u := by
  simp only [pushR, Bbu.st, rdi] at h hrdi hst ⊢
  rw [hrdi, hst, hv, hd] at h
  exact Res.imp h fun _ ha => ⟨ha.1, hrdi ▸ ha.2⟩

theorem dup_res {c u : MachineData} {i : Nat} (h : dupR c u) (hrdi : rdi c = rdi s)
    (hst : stOf c.dmem (rdi s) = st s) (hi : (rsi c).toNat = i) (hd : (rdx c).toNat = dd s) :
    Res (rdi s) (add (st s) ((st s).val i) (dd s) (.dup ((st s).len - i)))
      (fun st' => rax u = 0#64 ∧ stOf u.dmem (rdi s) = st') u := by
  simp only [dupR, Bbu.st, rdi] at h hrdi hst ⊢
  rw [hrdi, hst, hi, hd] at h
  exact Res.imp h fun _ ha => ⟨ha.1, hrdi ▸ ha.2⟩

-- `push` or `dup` returns to `.LB30` after `movq %rax, %r12`.
theorem at30_of_add {t c u : MachineData} {G : Nat} {R : MachineData → MachineData → Prop}
    {v : Word} {op : Op} (hpre : Pre 80 produceA s) (hb : Base s ra t)
    (hp : Post G R c u) (hag : (mod G c).Agree c u) (hG : G ≤ 40)
    (hc : c.dmem = t.dmem) (hrsp : c.regs.rsp = t.regs.rsp) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hrdi : rdi c = rdi s) (hrbx : c.regs.rbx.toBitVec = rdi s)
    (hrbp : c.regs.rbp.toBitVec = rsi s)
    (hr : Res (rdi s) (add (st s) v (dd s) op) (fun st' => rax u = 0#64 ∧ stOf u.dmem (rdi s) = st') u)
    (he : emit (env s) (st s) (dd s) = add (st s) v (dd s) op) :
    At30 s ra { u with regs := { u.regs with r12 := ⟨u.regs.rax.toBitVec⟩ } } := by
  refine ⟨(hb.call hpre hp hag hG hc hrsp h14 h15 hrdi).set12 _, ?_, ?_, v, op, he, RW.of_res hr⟩
  · have := keep hag .rbx
    simp only [Reg64s.get64_rbx] at this
    exact this.trans hrbx
  · have := keep hag .rbp
    simp only [Reg64s.get64_rbp] at this
    exact this.trans hrbp

-- `positionOf` returns in `.LB43`.
theorem Base.pos {s t c u : MachineData} {ra : Int64} {st' : St} (hpre : Pre 80 produceA s)
    (hb : Base s ra t) (hp : Post positionOfF positionOfR c u)
    (hag : (mod positionOfF c).Agree c u)
    (hc : c.dmem = t.dmem) (hrsp : c.regs.rsp = t.regs.rsp) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hrbx : c.regs.rbx.toBitVec = rdi s) (hrdi : rdi c = rdi s)
    (hrsi : rsi c = rsi s) (hst : stOf t.dmem (rdi s) = st') :
    Base s ra u ∧ u.regs.rbx.toBitVec = rdi s ∧ u.regs.r12 = c.regs.r12
      ∧ u.regs.rax.toBitVec = encOpt (positionOf st' (dd s)) ∧ stOf u.dmem (rdi s) = st' := by
  refine ⟨hb.call hpre hp hag (by decide) hc hrsp h14 h15 hrdi, ?_, ?_, ?_, ?_⟩
  · have := keep hag .rbx
    simp only [Reg64s.get64_rbx] at this
    rw [this]; exact hrbx
  · have := keep hag .r12
    simp only [Reg64s.get64_r12] at this
    exact UInt64.toBitVec_inj.mp this
  · have hr : rax u = encOpt (positionOf (stOf c.dmem (rdi c)) (rsi c).toNat) := hp.2.2.1
    rw [hc, hrdi, hst, hrsi] at hr
    exact hr
  · have hr : stOf u.dmem (rdi c) = stOf c.dmem (rdi c) := hp.2.2.2
    rw [hc, hrdi, hst] at hr
    exact hr

-- The test `positionOf(s, d) == s->len - 1` in `.LB43`.
theorem pos_test {o : Option Nat} {L : Nat} {r : Word} (hr : r.toNat = L) (hL : 1 ≤ L)
    (hL' : L ≤ 1025) (ho : ∀ p, o = some p → p < L) :
    encOpt o - (r - 1#64) = 0#64 ↔ o = some (L - 1) := by
  cases o with
  | none =>
    simp only [encOpt, reduceCtorEq, iff_false]
    bv_omega
  | some p =>
    have hp := ho p rfl
    simp only [encOpt, Option.some.injEq]
    constructor
    · intro h; bv_omega
    · intro h; subst h; bv_omega

-- The store of `pending - 1` keeps the frame.
theorem Fm.setPending {s : MachineData} {ra : Int64} {m : Mem 64} (hpre : Pre 80 produceA s)
    (h : Fm s ra m) (x : Word) : Fm s ra (m.storeInt (wordAt (rdi s) 1) 8 x.toInt) := by
  have hs := h.wf.struct_lt
  simp only [WORDS_eq] at hs
  refine h.store hpre (fun y hy => ?_) (rd_store_other _ ?_) (rd_store_other _ ?_)
  · refine Or.inl ?_
    simp only [Mem.Blocks.Inside, or_false, wordAt] at hy ⊢
    bv_omega
  all_goals (simp only [wordAt]; bv_omega)

theorem At28.ok {s t : MachineData} {ra : Int64} {st' : St} (hb : Base s ra t)
    (h : produce (env s) (st s) (dd s) = .ok st') (h0 : t.regs.r12.toBitVec = 0#64)
    (hs : stOf t.dmem (rdi s) = st') : At28 s ra t := by
  refine ⟨hb, ?_⟩
  rw [h]
  exact ⟨h0, hs⟩


end

theorem entry_stack (x : Word) :
    (x - 8#64 - (x - 8#64 - 8#64 - 8#64 - 8#64 - 8#64)).toNat < 2 ^ 63 := by
  bv_omega

-- `cmpq $-1` on the result of `shallowestCopyPosition`.
theorem encOpt_none {o : Option Nat} (hlt : ∀ c, o = some c → c < 1024) :
    encOpt o - 18446744073709551615#64 = 0#64 ↔ o = none := by
  cases o with
  | none => simp [encOpt]
  | some c =>
    have := hlt c rfl
    simp only [encOpt, reduceCtorEq, iff_false]
    bv_omega

-- `notq` and `addq (%rbx)`: the depth `len - 1 - c` of the copy `c`.
theorem depth_bv {r : Word} {L c : Nat} (hr : r.toNat = L) (hc : c < L) (hL : L < 1024) :
    (r + ~~~(BitVec.ofNat 64 c)).toNat = L - 1 - c := by
  subst hr
  bv_omega

-- After `shallowestCopyPosition` returns a copy `c`.
theorem entry_depth {s u : MachineData} (hpre : Pre 80 produceA s)
    (hst : stOf u.dmem (rdi s) = st s) (hux : u.regs.rbx.toBitVec = rdi s)
    (hax : u.regs.rax.toBitVec = encOpt (cp s)) (hs : cp s ≠ none) :
    ∃ c, cp s = some c
      ∧ (rd u.dmem u.regs.rbx.toBitVec + ~~~u.regs.rax.toBitVec).toNat = (st s).len - 1 - c := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hs
  have hlt := shallowestCopy_lt hc
  have hlen : (st s).len < 1024 := hpre.2.2.2.1
  have hr : (rd u.dmem u.regs.rbx.toBitVec).toNat = (st s).len := by
    rw [hux, ← hst, len_stOf, wordAt_zero]
  rw [hax, hc]
  exact ⟨c, rfl, depth_bv hr hlt hlen⟩

-- `shallowestCopyPosition` returns in the entry block.
theorem entry_call {s : MachineData} {ra : Int64} {M : Mem 64} {c u : MachineData}
    (hpre : Pre 80 produceA s) (hfm : Fm s ra M) (hp : Post shallowestCopyF shallowestCopyR c u)
    (hag : (mod shallowestCopyF c).Agree c u) (hc : c.dmem = M) (hrsp : rsp c = rsp s - 40#64)
    (h14 : c.regs.r14 = s.regs.r14) (h15 : c.regs.r15 = s.regs.r15) (hrdi : rdi c = rdi s)
    (hrbx : c.regs.rbx.toBitVec = rdi s) (hrbp : c.regs.rbp.toBitVec = rsi s)
    (h12 : c.regs.r12.toBitVec = vv s) (hrsi : rsi c = vv s) (hst : stOf M (rdi s) = st s) :
    Base s ra u ∧ stOf u.dmem (rdi s) = st s ∧ u.regs.rbx.toBitVec = rdi s
      ∧ u.regs.rbp.toBitVec = rsi s ∧ u.regs.r12.toBitVec = vv s
      ∧ u.regs.rax.toBitVec = encOpt (cp s) := by
  refine ⟨⟨Kit.Fm.call (k := 40) (by decide) (by decide) hpre hfm hc hrsp hrdi hp hag, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · have := keep hag .rsp
    simp only [Reg64s.get64_rsp] at this
    rw [this]; exact hrsp
  · have := keep hag .r14
    simp only [Reg64s.get64_r14] at this
    rw [this, h14]
  · have := keep hag .r15
    simp only [Reg64s.get64_r15] at this
    rw [this, h15]
  · have hr : stOf u.dmem (rdi c) = stOf c.dmem (rdi c) := hp.2.2.2
    rw [hc, hrdi, hst] at hr
    exact hr
  · have := keep hag .rbx
    simp only [Reg64s.get64_rbx] at this
    rw [this]; exact hrbx
  · have := keep hag .rbp
    simp only [Reg64s.get64_rbp] at this
    rw [this]; exact hrbp
  · have := keep hag .r12
    simp only [Reg64s.get64_r12] at this
    rw [this]; exact h12
  · have hr : rax u = encOpt (shallowestCopyPosition (stOf c.dmem (rdi c)) (rsi c)) := hp.2.2.1
    rw [hc, hrdi, hst, hrsi] at hr
    exact hr

-- The states after the call, as literals with variable fields. A direct proof in the
-- body makes the kernel compare the state literal with `u`; this uses too much memory.
-- With this lemma the kernel only checks `rfl` on equal terms.
section
variable {s u : MachineData} {ra : Int64} {z : RegZmms} {f : StatusFlags} {d : Mem 64}
  {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64}

theorem lp_mk (hB : Base s ra u) (hst : stOf u.dmem (rdi s) = st s)
    (hux : u.regs.rbx.toBitVec = rdi s) (hbp : u.regs.rbp.toBitVec = rsi s)
    (h12 : u.regs.r12.toBitVec = vv s) (hax : u.regs.rax.toBitVec = encOpt (cp s))
    (hz : vv s ≠ 0) (hd : d = u.dmem) (e1 : a1 = u.regs.rbx) (e6 : a6 = u.regs.rsp)
    (e7 : a7 = u.regs.rbp) (e12 : a12 = u.regs.r12) (e13 : a13 = ⟨u.regs.rax.toBitVec⟩)
    (e14 : a14 = u.regs.r14) (e15 : a15 = u.regs.r15) :
    Lp s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  subst hd e1 e6 e7 e12 e13 e14 e15
  exact ⟨⟨hB.fm, hB.rsp, hB.r14, hB.r15⟩, hst, hux, hbp, h12, hax, hz⟩

end

end Produce

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

open Produce in
theorem produce_body [Host] [FunDecls]
    (hcopy : Spec "shallowestCopyPosition" shallowestCopyF shallowestCopyA shallowestCopyR)
    (hspill : Spec "isSpilled" isSpilledF isSpilledA isSpilledR)
    (hpush : Spec "push" pushF pushA pushR)
    (hdup : Spec "dup" dupF dupA dupR)
    (hpos : Spec "positionOf" positionOfF positionOfA positionOfR) :
    Body produceAsm produceF produceA produceR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 80 produceA s := hpre
  have hle : 80 ≤ s.regs.rsp.toBitVec.toNat := hpre.2.1.le
  refine Program.WP.cfg (fun
      | .entry, t | .label "produce", t => t = s.pushRa ra
      | .label ".LB31", t => At31 s ra t
      | .label ".LB39", t => At39 s ra t
      | .label ".LB32", t => At32 s ra t
      | .label ".LB30", t => At30 s ra t
      | .label ".LB28", t => At28 s ra t
      | .label ".LB41", t => At41 s ra t
      | .label ".LB42", t => At42 s ra t
      | .label ".LB34", t => At34 s ra t
      | .label ".LB43", t => At43 s ra t
      | .label ".LB36", t | .label ".LB38", t => Asrt s ra t
      | _, _ => False)
    V ?_ rfl
  cfg_cases
  case right.right.right.right.right.right.right.left t ht =>
    obtain ⟨hb, hst, hrbx, hrbp, hrdi, hrsi, hv⟩ := ht
    clear hcopy hspill hpos hdup
    kvcgen64 [hpush]
    all_goals bbu_norm at *
    case vc1 => exact hb.call_isSome hpre
    case vc2 => exact hb.pre hpre (by decide) rfl rfl hrdi (hb.fm.pushA hpre rfl hrdi hst)
    case vc3 =>
      rename_i u hp hag _
      have h30 := at30_of_add hpre hb hp hag (by decide) rfl rfl rfl rfl hrdi hrbx hrbp
        (push_res hp.2.2 hrdi hst rfl (congrArg BitVec.toNat hrsi)) (emit_zero (st := st s) hv)
      cfg_goto
      · exact h30.1.stack
      · exact h30
      · simp [V]
  case right.right.right.right.right.right.right.right.left t ht =>
    obtain ⟨hl, c, hc, hd⟩ := ht
    have hlen : (st s).len < 1024 := hpre.2.2.2.1
    have hcl := shallowestCopy_lt hc
    have hi : (t.regs.r13.toBitVec).toNat = c := by
      rw [hl.r13, hc]; simp only [encOpt, BitVec.toNat_ofNat]; omega
    clear hcopy hspill hpos hpush
    kvcgen64 [hdup]
    all_goals bbu_norm at *
    case vc1 => exact hl.call_isSome hpre
    case vc2 =>
      exact hl.pre hpre (by decide) rfl rfl hl.rbx
        (hl.fm.dupA hpre rfl hl.rbx hl.st (by rw [← hi] at hcl; exact hcl))
    case vc3 =>
      rename_i u hp hag _
      have he : emit (env s) (st s) (dd s) = add (st s) ((st s).val c) (dd s) (.dup ((st s).len - c)) :=
        (emit_dup hl.v0 hc hd).trans (congrArg (fun x => add (st s) x (dd s) _) (val_of_copy hc).symm)
      have h30 := at30_of_add hpre hl.toBase hp hag (by decide) rfl rfl rfl rfl hl.rbx hl.rbx hl.rbp
        (dup_res hp.2.2 hl.rbx hl.st hi (congrArg BitVec.toNat hl.rbp)) he
      cfg_goto
      · exact h30.1.stack
      · exact h30
      · simp [V]
  case right.right.right.right.left t ht =>
    obtain ⟨⟨hl, hf⟩, hp0⟩ := ht
    clear hcopy hspill hpos hdup
    kvcgen64 [hpush]
    all_goals bbu_norm at *
    case vc1 => exact hl.call_isSome hpre
    case vc2 => exact hl.pre hpre (by decide) rfl rfl hl.rbx (hl.fm.pushA hpre rfl hl.rbx hl.st)
    case vc3 =>
      rename_i u hp hag _
      exact at30_of_add hpre hl.toBase hp hag (by decide) rfl rfl rfl rfl hl.rbx hl.rbx hl.rbp
        (push_res hp.2.2 hl.rbx hl.st hl.r12 (congrArg BitVec.toNat hl.rbp)) (emit_push hl.v0 hf hp0)
    case vc4 => simp [V]
  case right.right.right.right.right.right.right.right.right.right.right.left t ht
      | right.right.right.right.right.right.right.right.right.right.right.right t ht =>
    obtain ⟨hb, hpr⟩ := ht
    clear hcopy hspill hpush hdup hpos
    kvcgen64
    cfg_goto
    · exact hb.stack
    · refine ⟨⟨hb.fm, hb.rsp, hb.r14, hb.r15⟩, ?_⟩
      rw [hpr]
      rfl
    · simp [V]
  case right.right.right.right.right.right.left t ht =>
    obtain ⟨hb, hR⟩ := ht
    obtain ⟨h1, h2, h3, h4⟩ := hb.fm.pops hb.rsp
    clear hcopy hspill hpush hdup hpos
    kvcgen64
    all_goals simp only [rd_def] at *
    case vc1 | vc2 | vc3 | vc4 =>
      refine Mem.Mapped.loadInt_isSome hb.fm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, hb.rsp]
      bv_omega
    case vc5 =>
      simp only [MachineData.retAddr, Option.isSome_map]
      refine Mem.Mapped.loadInt_isSome hb.fm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, hb.rsp]
      bv_omega
    case vc6 =>
      refine Kit.Fm.ret (by decide) hpre hb.fm (by simp only [Reg64s.get64_rsp, hb.rsp]; bv_omega)
        ?_ fun _ hm hax => RW.res hR hm hax
      · intro q hq
        have := hb.r14
        have := hb.r15
        cases q <;> simp_all
  case right.right.right.left t ht =>
    obtain ⟨⟨hl, hf⟩, hfree⟩ := ht
    clear hcopy hpush hdup hpos
    kvcgen64 [hspill]
    all_goals bbu_norm at *
    case vc1 => exact hl.call_isSome hpre
    case vc2 =>
      refine hl.pre hpre (by decide) rfl rfl hl.rbx ⟨dd s, ?_⟩
      show _ < (envOf t.dmem t.regs.rbx.toBitVec).n
        ∧ (envOf t.dmem t.regs.rbx.toBitVec).target[dd s]! = t.regs.r12.toBitVec
      rw [hl.rbx, (hl.fm.keeps hpre).1, hl.r12]
      exact ⟨hpre.2.2.1, rfl⟩
    all_goals
      rename_i u hp hag _ hz _
      have hst : stOf u.dmem (rdi s) = st s := by
        have h : stOf u.dmem t.regs.rbx.toBitVec = stOf t.dmem t.regs.rbx.toBitVec := hp.2.2.2
        rw [hl.rbx, hl.st] at h; exact h
      have hrax : u.regs.rax.toBitVec = BitVec.ofNat 64 (isSpilled (env s) (vv s)).toNat := by
        have h : u.regs.rax.toBitVec
            = BitVec.ofNat 64 (isSpilled (envOf t.dmem t.regs.rbx.toBitVec) t.regs.r12.toBitVec).toNat :=
          hp.2.2.1
        rw [hl.rbx, (hl.fm.keeps hpre).1, hl.r12] at h; exact h
      have hL := hl.call hpre hp hag (by decide) rfl rfl rfl rfl rfl rfl rfl rfl hl.rbx hst
      bbu_flags at hz
      rw [hrax] at hz
    case vc3 =>
      have hsp : isSpilled (env s) (vv s) = false := by
        cases hs : isSpilled (env s) (vv s)
        · rfl
        · rw [hs] at hz; revert hz; decide
      cfg_goto
      · exact hL.stack
      · exact ⟨⟨hL.congr rfl rfl, hf⟩, Bool.or_eq_false_iff.mpr ⟨hfree, hsp⟩⟩
      · simp [V]
    case vc4 =>
      have hsp : isSpilled (env s) (vv s) = true := by
        cases hs : isSpilled (env s) (vv s)
        · rw [hs] at hz; revert hz; decide
        · rfl
      exact ⟨⟨hL.congr rfl rfl, hf⟩, by simp only [Bool.or_eq_true]; exact Or.inr hsp⟩
    case vc5 => simp [V]
  case right.right.left t ht =>
    obtain ⟨hl, hf⟩ := ht
    clear hcopy hpush hdup hpos hspill
    kvcgen64
    all_goals bbu_norm at *
    all_goals bbu_flags at *
    case vc1 =>
      rename_i hz
      rw [hl.r12] at hz
      cfg_goto
      · exact hl.stack
      · exact ⟨⟨hl.congr rfl rfl, hf⟩, isFree_even hl.v0 hz⟩
      · simp [V]
    case vc2 =>
      rename_i hz h1
      rw [hl.r12] at hz h1
      cfg_goto
      · exact hl.stack
      · exact ⟨⟨hl.congr rfl rfl, hf⟩, by rw [isFree_odd hz h1]; rfl⟩
      · simp [V]
    case vc3 =>
      rename_i hz h1
      rw [hl.r12] at h1
      exact ⟨⟨hl.congr rfl rfl, hf⟩, isFree_one h1⟩
    case vc4 => simp [V]
  case right.right.right.right.right.right.right.right.right.left t ht =>
    obtain ⟨⟨hl, hf⟩, hp0⟩ := ht
    clear hcopy hpush hdup hpos hspill
    have hw := hl.fm.wf
    kvcgen64
    all_goals bbu_norm at *
    case vc1 =>
      rename_i hz _
      bbu_flags at hz
      rw [hl.r13] at hz
      have hn : cp s = none := by
        cases hc : cp s with
        | none => rfl
        | some c =>
          have := shallowestCopy_lt hc
          have hlen : (st s).len < 1024 := hpre.2.2.2.1
          rw [hc] at hz
          simp only [encOpt] at hz
          bv_omega
      cfg_goto
      · exact hl.stack
      · exact ⟨hl.toBase.congr rfl rfl, produce_err (emit_none hl.v0 hp0 hn)⟩
      · simp [V]
    case vc2 => rw [hl.rbx]; exact hdr_isSome0 hw
    all_goals
      rename_i hz _ _
      bbu_flags at hz
      rw [hl.r13] at hz
      obtain ⟨c, hc⟩ : ∃ c, cp s = some c := by
        cases hc : cp s with
        | none => rw [hc] at hz; exact absurd hz (by decide)
        | some c => exact ⟨c, rfl⟩
      have hcl := shallowestCopy_lt hc
      have hfar : 15 < (st s).len - 1 - c := hf c hc
      have h0 : (rd t.dmem s.regs.rdi.toBitVec).toNat = (st s).len := by
        rw [← hl.st, len_stOf, wordAt_zero]; rfl
      have hb' : t.regs.rbx.toBitVec = s.regs.rdi.toBitVec := hl.rbx
      have hlen : (st s).len < 1024 := hpre.2.2.2.1
    case vc3 =>
      rename_i hz2
      bbu_flags at hz2
      rw [hb', hl.r13, hc] at hz2
      simp only [encOpt] at hz2
      bv_omega
    case vc4 => rw [hb']; exact hw.word_isSome hw.mapped (k := 7) (by decide)
    case vc5 => rw [hb']; exact blk_isSome0 hw
    case vc6 => rw [hb']; exact loadInt_isSome_store _ (hw.word_isSome hw.mapped (k := 7) (by decide))
    case vc7 => rw [hb']; exact blk_isSome1 hw _
    case vc8 =>
      have hP : produce (env s) (st s) (dd s) = .error (.blocked c ((st s).len - 1 - c - 15)) :=
        produce_err (emit_blocked hl.v0 hf hp0 hc)
      rw [hb', blkStores_eq hw]
      cfg_goto
      · exact hl.stack
      · refine ⟨⟨hl.fm.blk (by decide) hpre _ _, hl.rsp, hl.r14, hl.r15⟩, ?_⟩
        obtain ⟨h1, h2⟩ := blkStores_rd hw t.regs.r13.toBitVec
          (rd t.dmem s.regs.rdi.toBitVec - 16#64 - t.regs.r13.toBitVec)
        rw [hP]
        refine ⟨rfl, h1.trans ?_, h2.trans ?_⟩
        · rw [hl.r13, hc]; rfl
        · rw [hl.r13, hc]
          simp only [encOpt]
          bv_omega
      · simp [V]
  case left t ht =>
    subst ht
    kvcgen64
  case right.right.right.right.right.left t ht =>
    obtain ⟨hb, hrbx, hrbp, v, op, he, hr⟩ := ht
    have hP : produce (env s) (st s) (dd s) = (add (st s) v (dd s) op).bind (tail (dd s)) := by
      rw [produce_eq, he]
    clear hcopy hspill hpush hdup hpos
    kvcgen64
    all_goals bbu_norm at *
    all_goals bbu_flags at *
    case vc1 =>
      rename_i hz
      rw [BitVec.and_self] at hz
      rw [hz] at hr
      obtain ⟨st', hA, hst'⟩ := RW.ok_of_zero hr
      cfg_goto
      · exact hb.stack
      · exact ⟨hb.congr rfl rfl, hrbx, hrbp, hz, st', he.trans hA, hst'⟩
      · simp [V]
    case vc2 =>
      rename_i hz
      rw [BitVec.and_self] at hz
      exact ⟨hb.congr rfl rfl, hP ▸ RW.bind_err hr hz⟩
    case vc3 => simp [V]
  case right.right.right.right.right.right.right.right.right.right.left t ht =>
    obtain ⟨hb, hrbx, hrbp, hr12, st', he, hst'⟩ := ht
    have hP : produce (env s) (st s) (dd s) = tail (dd s) st' := by
      rw [produce_eq, he]; rfl
    clear hcopy hspill hpush hdup
    obtain ⟨hlen', -, -⟩ := emit_shape he
    have hlen : (st s).len < 1024 := hpre.2.2.2.1
    have hL : 1 ≤ st'.len ∧ st'.len ≤ 1025 := by rw [hlen']; omega
    have hpt : ∀ {u : MachineData}, stOf u.dmem (rdi s) = st' →
        (encOpt (positionOf st' (dd s)) - (rd u.dmem (rdi s) - 1#64) = 0#64
          ↔ positionOf st' (dd s) = some (st'.len - 1)) := fun hsu =>
      pos_test (by rw [← hsu, len_stOf, wordAt_zero]) hL.1 hL.2 fun _ => positionOf_some
    kvcgen64 [hpos]
    all_goals bbu_norm at *
    case vc1 => exact hb.call_isSome hpre
    case vc2 => exact hb.pre hpre (by decide) rfl rfl hrbx trivial
    case vc3 =>
      rename_i u hp hag _
      obtain ⟨hB, hux, -, -, -⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
      rw [hux]; exact hdr_isSome0 hB.fm.wf
    case vc5 =>
      rename_i u hp hag _ _
      obtain ⟨hB, hux, -, -, -⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
      rw [hux]; exact hB.fm.wf.word_isSome hB.fm.wf.mapped (k := 1) (by decide)
    case vc7 =>
      rename_i u hp hag _ _ _ _
      obtain ⟨hB, hux, -, -, -⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
      rw [hux]; exact hB.fm.wf.word_isSome hB.fm.wf.mapped (k := 1) (by decide)
    case vc4 =>
      rename_i u hp hag _ hnz
      obtain ⟨hB, hux, -, hax, hsu⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
      bbu_flags at hnz
      rw [hux, hax] at hnz
      replace hnz : positionOf st' (dd s) ≠ some (st'.len - 1) := fun h => hnz ((hpt hsu).mpr h)
      cfg_goto
      · exact hB.stack
      · exact ⟨⟨hB.fm, hB.rsp, hB.r14, hB.r15⟩, hP.trans (tail_bad hnz)⟩
      · simp [V]
    all_goals
      rename_i u hp hag _ hz _ hnz
      obtain ⟨hB, hux, hu12, hax, hsu⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
      have h0 : u.regs.r12.toBitVec = 0#64 := (congrArg UInt64.toBitVec hu12).trans hr12
      bbu_flags at hz hnz
      rw [BitVec.and_self] at hz
      rw [hux, hax] at hnz
      have hpo := (hpt hsu).mp hnz
      have hpw : st'.pendingGenerations = (rd u.dmem (rdi s + 8#64)).toNat := by rw [← hsu]; rfl
      rw [hux] at hz ⊢
    case vc6 =>
      have hp0 : st'.pendingGenerations = 0 := by rw [hpw, hz]; rfl
      cfg_goto
      · exact hB.stack
      · exact At28.ok ⟨hB.fm, hB.rsp, hB.r14, hB.r15⟩
          (hP.trans ((tail_ok hpo).trans (congrArg _ (pending_zero hp0)))) h0 hsu
      · simp [V]
    case vc8 =>
      have hx : (rd u.dmem (rdi s + 8#64) - 1#64).toNat = st'.pendingGenerations - 1 := by
        rw [hpw]; bv_omega
      cfg_goto
      · exact (Base.stack (t := u) hB)
      · refine At28.ok ⟨hB.fm.setPending hpre (rd u.dmem (rdi s + 8#64) - 1#64), hB.rsp, hB.r14,
          hB.r15⟩ (hP.trans (tail_ok hpo)) h0 ?_
        refine (stOf_setPending hB.fm.wf (rd u.dmem (rdi s + 8#64) - 1#64)).trans ?_
        rw [hsu, hx]
      · simp [V]
  case right.left t ht =>
    subst ht
    have hfm : Fm s ra (Kit.pushes s ra regs) := Kit.Fm.init (by decide) hpre
    have hsp := Kit.st_pushes (rs := regs) (ra := ra) (by decide) hpre
    have hen := (hfm.keeps hpre).1
    have hn := hfm.n hpre
    have hd : (rsi s).toNat < nOf (Kit.pushes s ra regs) (rdi s) := by
      rw [hn, ← n_envOf]; exact hpre.2.2.1
    have hv : rd (Kit.pushes s ra regs) (rd (Kit.pushes s ra regs) (rdi s + 32#64) + rsi s * 8#64)
        = vv s := by
      have := rd_target hd
      rw [wordAt_zero, hen] at this
      exact this
    have htg := tgt_isSome hfm.wf hd
    rw [wordAt_mul] at htg
    have hr40 : s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 = rsp s - 40#64 := by
      simp only [Reg64s.get64_rsp]; bv_omega
    have hfr := hpre.2.1.mapped
    clear hspill hpush hdup hpos
    kvcgen64 [hcopy]
    all_goals simp only [pushes_eq, rd_def] at *
    all_goals generalize hM : Kit.pushes s ra regs = M at *
    all_goals bbu_norm at *
    case vc1 | vc2 | vc3 | vc4 =>
      repeat apply loadInt_isSome_store
      refine Mem.Mapped.loadInt_isSome hfr (Or.inl ?_)
      clear hv htg hd hfm hsp hen hn hM hpre hr40 hfr
      rename_i _ _ h
      clear h
      bv_omega
    case vc5 => exact hfm.wf.word_isSome hfm.wf.mapped (k := 4) (by decide)
    case vc6 => exact htg
    case vc8 => exact hr40 ▸ hfm.call_isSome (by decide) hpre
    case vc9 => exact Kit.Fm.pre (k := 40) (by decide) hpre hfm rfl hr40 rfl trivial
    case vc7 =>
      rename_i hz
      bbu_flags at hz
      rw [BitVec.and_self] at hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp]
        exact entry_stack _
      · exact ⟨⟨hfm, hr40, rfl, rfl⟩, hsp, rfl, rfl, rfl, rfl, hv.symm.trans hz⟩
      · simp [V]
    case vc11 =>
      rename_i u _ _ _ _ hp hag
      obtain ⟨hB, -, hux, -⟩ := entry_call hpre hfm hp hag rfl hr40 rfl rfl rfl rfl rfl hv hv hsp
      rw [hux]; exact hdr_isSome0 hB.fm.wf
    case vc14 => simp [V]
    all_goals
      have hlt : ∀ c, cp s = some c → c < 1024 := fun c hc => by
        have := shallowestCopy_lt hc; have : (st s).len < 1024 := hpre.2.2.2.1; omega
    case vc10 =>
      rename_i _ u hs _ hz hp hag
      obtain ⟨hB, hst, hux, hbp, h12, hax⟩ :=
        entry_call hpre hfm hp hag rfl hr40 rfl rfl rfl rfl rfl hv hv hsp
      bbu_flags at hz hs
      rw [BitVec.and_self, hv] at hz
      rw [hax] at hs
      have hcp : cp s = none := (encOpt_none hlt).mp hs
      cfg_goto
      · exact hB.stack
      · exact ⟨lp_mk hB hst hux hbp h12 hax hz rfl rfl rfl rfl rfl rfl rfl rfl,
          fun c hc => absurd (hc.symm.trans hcp) (Option.some_ne_none c)⟩
      · simp [V]
    all_goals
      rename_i _ u hs _ hbe hz hp hag
      obtain ⟨hB, hst, hux, hbp, h12, hax⟩ :=
        entry_call hpre hfm hp hag rfl hr40 rfl rfl rfl rfl rfl hv hv hsp
      bbu_flags at hz hs
      rw [BitVec.and_self, hv] at hz
      rw [hax] at hs
      replace hs : cp s ≠ none := fun h => hs ((encOpt_none hlt).mpr h)
      rw [Kit.be_sub_imm _ _ (by decide)] at hbe
      obtain ⟨c, hcp, hy⟩ := entry_depth hpre hst hux hax hs
      rw [hy] at hbe
    case vc12 =>
      cfg_goto
      · exact hB.stack
      · exact ⟨lp_mk hB hst hux hbp h12 hax hz rfl rfl rfl rfl rfl rfl rfl rfl, c, hcp,
          of_decide_eq_true hbe⟩
      · simp [V]
    case vc13 =>
      refine ⟨lp_mk hB hst hux hbp h12 hax hz rfl rfl rfl rfl rfl rfl rfl rfl, fun c' hc' => ?_⟩
      obtain rfl := Option.some.inj (hcp.symm.trans hc')
      exact Nat.lt_of_not_le (of_decide_eq_false hbe)

end Bbu
