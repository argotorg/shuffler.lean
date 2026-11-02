module

public import FlatShuffler.Kit
import all FlatShuffler.Kit
public import FlatShuffler.ModelLemmas
import all FlatShuffler.ModelLemmas

@[expose] public section

/-!
The body triple of `generate` (`Names.generate` in `build/kraken/c/build_bottom_up.S`). The body pushes `rbp` and
`rbx` and calls `produce`. It exits with `-2` (`.LB.Emission.generate.2`) when the target is out of
range. When the two slot values are equal, it swaps the two dests inline; else it
calls `swapWith` (`.LB.Emission.generate.1`) when the depth is at most 16. The other paths end at `.LB.Emission.generate.0`.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace FlatShuffler

namespace Generate

-- The registers that `generate` saves, in the order of the pushes.
abbrev regs : List Reg64 := [.rbp, .rbx]

-- The memory of `generate`: the frame of 96 bytes, the saved words and the struct.
abbrev Fm := Kit.Fm 96 regs

section
variable {s : MachineData}

-- The callee-saved registers.
theorem saved_regs {t : MachineData} (hbx : t.regs.rbx.toBitVec = s.regs.rbx.toBitVec)
    (hbp : t.regs.rbp.toBitVec = s.regs.rbp.toBitVec)
    (h12 : t.regs.r12.toBitVec = s.regs.r12.toBitVec) (h13 : t.regs.r13.toBitVec = s.regs.r13.toBitVec)
    (h14 : t.regs.r14.toBitVec = s.regs.r14.toBitVec) (h15 : t.regs.r15.toBitVec = s.regs.r15.toBitVec) :
    ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q := by
  intro q hq
  cases q <;> simp_all

end

/-! ## The model state in memory -/

section
variable {m : Mem 64} {S : Addr} {k : Nat}

-- A store to the word `k` of the struct keeps the other words.
theorem map_rd (hw : Wf m S) (hk : k < WORDS) {j : Nat} (hj : j < WORDS) (hjk : j ≠ k) (v : Int) :
    rd (m.storeInt (wordAt S k) 8 v) (wordAt S j) = rd m (wordAt S j) := by
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs hk hj
  exact rd_store_other _ (by simp only [wordAt]; bv_omega)

theorem map_n (hw : Wf m S) (hk1 : DEST ≤ k) (hk : k < WORDS) (v : Int) :
    nOf (m.storeInt (wordAt S k) 8 v) S = nOf m S := by
  unfold nOf; rw [map_rd hw hk (by decide) (by simp only [DEST_eq] at hk1; omega)]

-- A store to the word `k ≥ DEST` of the struct keeps the working stack.
theorem map_data (hw : Wf m S) (hk : k < WORDS) {j : Nat} (hj : j < nOf m S) (v : Int) :
    rd (m.storeInt (wordAt S k) 8 v) (wordAt (dataOf m S) j) = rd m (wordAt (dataOf m S) j) := by
  have hs := hw.struct_lt
  have hd := hw.data_lt
  simp only [WORDS_eq] at hs hk
  refine rd_storeInt_of_disjoint fun x hx hy => hw.disj_struct x ?_ (Or.inl ?_)
  · simp only [Mem.Blocks.Inside, or_false, WORDS_eq] at hx ⊢; bv_omega
  · simp only [Mem.Blocks.Inside, or_false] at hy ⊢; bv_omega

end

section
variable {m : Mem 64} {S : Addr}

end

/-! ## The swap of the equal branch -/

theorem addr_dest (S y : Word) : S + y * 8#64 + 56#64 = wordAt S (DEST + y.toNat) := by
  simp only [wordAt, DEST_eq]; bv_omega

theorem addr_pos (S y : Word) : S + y * 8#64 + 8248#64 = wordAt S (POS + y.toNat) := by
  simp only [wordAt, POS_eq]; bv_omega

theorem addr_data (D y : Word) : D + y * 8#64 = wordAt D y.toNat := by
  simp only [wordAt]; bv_omega

-- The four stores of the equal branch: the dest words of slot `x` and of the top
-- slot swap, and the position words of the two dests point to the slots.
def swap4 (m : Mem 64) (S x : Word) : Mem 64 :=
  let A := S + x * 8#64 + 56#64
  let B := S + (rd m S + -1#64) * 8#64 + 56#64
  let m2 := (m.storeInt A 8 (rd m B).toInt).storeInt B 8 (rd m A).toInt
  (m2.storeInt (S + rd m2 A * 8#64 + 8248#64) 8 x.toInt).storeInt (S + rd m A * 8#64 + 8248#64) 8
    (rd m S + -1#64).toInt

-- The struct at `S` holds `st1`, and slot `x` is below the top slot.
structure Sw (m : Mem 64) (S x : Word) (st1 : St) : Prop where
  wf : Wf m S
  st : stOf m S = st1
  pos : Pos (nOf m S) st1
  lt : x.toNat + 1 < st1.len

section
variable {m : Mem 64} {S x : Word} {st1 : St}

-- The dest of slot `i` and its bound.
theorem Sw.dest (h : Sw m S x st1) {i : Nat} (hi : i < st1.len) :
    (rd m (wordAt S (DEST + i))).toNat = st1.dest i ∧ st1.dest i < nOf m S := by
  refine ⟨?_, ?_⟩
  · rw [← h.st, dest_stOf (by rw [← h.st, len_stOf] at hi; exact hi)]
  · have hd := h.pos.dests.1 i (by rw [St.length_dests]; exact hi)
    rwa [St.dest_eq, getElem!_pos st1.dests i (by rw [St.length_dests]; exact hi)]

theorem optOf_lt {w : Word} (h : w.toNat < 1024) : optOf w = some w.toNat := by
  unfold optOf; rw [ite_eq_right_iff.mpr (fun he => by subst he; simp at h)]

-- The dest words of slot `x` and of the top slot.
theorem Sw.dest_a (h : Sw m S x st1) : (rd m (S + x * 8#64 + 56#64)).toNat < nOf m S := by
  rw [addr_dest]; have := h.dest (i := x.toNat) (by have := h.lt; omega); omega

theorem Sw.ld_pos (h : Sw m S x st1) {y : Word} (hy : y.toNat < nOf m S) :
    (m.loadInt (S + y * 8#64 + 8248#64) 8).isSome = true := by
  have := h.wf.n_le; simp only [maxStackSize] at this
  rw [addr_pos]; exact h.wf.word_isSome h.wf.mapped (by simp only [POS_eq, WORDS_eq]; omega)

-- The words of the working stack.
theorem Sw.ld_val (h : Sw m S x st1) : (m.loadInt (rd m (S + 24#64) + x * 8#64) 8).isSome = true := by
  have hd := h.wf.data_lt
  have hl := h.wf.len_le
  have hn := h.wf.n_le
  have := h.lt
  rw [len_stOf.symm.trans (congrArg St.len h.st)] at hl
  simp only [maxStackSize] at hn
  refine Mem.Mapped.loadInt_isSome (fun y hy => h.wf.mapped y (inside_append.mpr (Or.inl hy)))
    (inside_writable (Or.inr (Or.inr (Or.inl ?_))))
  rw [show rd m (S + 24#64) = dataOf m S from rfl]; bv_omega

end
/-! ## The frame of `generate` -/

section
variable {s : MachineData} {ra : Int64}

theorem fm_isSome {m : Mem 64} (h : Fm s ra m) {a : Addr}
    (ha : (a - (s.regs.rsp.toBitVec - 96#64)).toNat + 8 ≤ 96) : (m.loadInt a 8).isSome = true :=
  h.map.loadInt_isSome (Or.inl ha)

end
/-! ## The calls -/

-- The registers of `generate` after the pushes.
structure Rg (s t : MachineData) : Prop where
  sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 24#64
  bp : t.regs.rbp.toBitVec = s.regs.rdi.toBitVec
  bx : t.regs.rbx.toBitVec = s.regs.rsi.toBitVec
  r12 : t.regs.r12.toBitVec = s.regs.r12.toBitVec
  r13 : t.regs.r13.toBitVec = s.regs.r13.toBitVec
  r14 : t.regs.r14.toBitVec = s.regs.r14.toBitVec
  r15 : t.regs.r15.toBitVec = s.regs.r15.toBitVec

section
variable {s : MachineData} {ra : Int64} {A : MachineData → Prop}

-- A callee keeps the registers of `Rg`.
theorem Rg.call {c t : MachineData} {G : Nat} (h : Rg s c) (hag : (mod G c).Agree c t) : Rg s t := by
  have hr : ∀ q, q ∉ (mod G c).regs → (t.regs.get64 q) = c.regs.get64 q := hag.1
  have h1 := hr .rsp (by simp [mod])
  have h2 := hr .rbp (by simp [mod])
  have h3 := hr .rbx (by simp [mod])
  have h4 := hr .r12 (by simp [mod])
  have h5 := hr .r13 (by simp [mod])
  have h6 := hr .r14 (by simp [mod])
  have h7 := hr .r15 (by simp [mod])
  simp only [Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_rbx, Reg64s.get64_r12,
    Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15] at h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1 ▸ h.sp, h2 ▸ h.bp, h3 ▸ h.bx, h4 ▸ h.r12, h5 ▸ h.r13, h6 ▸ h.r14, h7 ▸ h.r15⟩

theorem Rg.rsp {t : MachineData} (h : Rg s t) : rsp t = rsp s - 24#64 := by
  simp only [Reg64s.get64_rsp, h.sp]

theorem Rg.rdi {c : MachineData} (h : Rg s c) (hrdi : c.regs.rdi = c.regs.rbp) : rdi c = rdi s := by
  simp only [Reg64s.get64_rdi, hrdi, h.bp]

-- The precondition of `produce` at the call of the entry block.
theorem produce_pre {c : MachineData} (hpre : Pre 96 generateA s)
    (hc : c.dmem = Kit.pushes s ra regs) (hrg : Rg s c) (hrdi : c.regs.rdi = c.regs.rbp)
    (hrsi : c.regs.rsi = c.regs.rbx) (hd : (rsi s).toNat < (env s).n) : Pre produceF produceA c := by
  have hfm : Fm s ra _ := Kit.Fm.init (by decide) hpre
  have hst := Kit.st_pushes (rs := regs) (ra := ra) (by decide) hpre
  have henv := (hfm.keeps hpre).1
  have hrd := hrg.rdi hrdi
  have hA := hpre.2.2
  refine Kit.Fm.pre (k := 24) (by decide) hpre hfm hc hrg.rsp hrd ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [st, env, cap, rsi, Reg64s.get64_rsi, hrsi, hrg.bx, hrd, hc, hst, henv]
  · exact hd
  · exact hA.2.1
  · rw [← n_envOf, henv, n_envOf]; simp only [generateA, st, cap] at hA; omega
  · exact hA.2.2.2

end

/-! ## The model of `generate` -/

section
variable {e : Env} {st st1 : St} {d : Nat}

theorem gen_err {x : Err} (hd : d < e.n) (h : produce e st d = .error x) :
    generate e st d = .error x := by
  unfold generate; simp only [show ¬ e.n ≤ d from by omega, ↓reduceIte, h]; rfl

theorem gen_ok (hd : d < e.n) (h : produce e st d = .ok st1) :
    generate e st d =
      if d + 1 < st1.len ∧ st1.dest d ≠ d then
        if st1.val d = st1.val (st1.len - 1) then .ok (swapDestinations st1 d (st1.len - 1))
        else if st1.len - 1 - d ≤ MAX_SWAP_DEPTH then swapWith st1 d else .ok st1
      else .ok st1 := by
  unfold generate; simp only [show ¬ e.n ≤ d from by omega, ↓reduceIte, h]; rfl

end

/-! ## Results and loads -/

-- The words of the struct are mapped.
theorem word_isSome {m : Mem 64} {S a : Addr} (hw : Wf m S) {k : Nat} (hk : k < WORDS)
    (ha : a = wordAt S k) : (m.loadInt a 8).isSome = true :=
  ha ▸ hw.word_isSome hw.mapped hk

/-! ## The entry block -/

section
variable {s : MachineData} {ra : Int64} {A : MachineData → Prop}

theorem e_ld3 (hpre : Pre 96 A s) :
    ((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).loadInt
      (s.regs.rdi.toBitVec + 24#64) 8).isSome = true :=
  loadInt_isSome_store _ (word_isSome hpre.1 (k := 3) (by decide) rfl)

theorem e_ld16 (hpre : Pre 96 A s) :
    ((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).loadInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  exact (Kit.Mid.init (F := 96) (ra := ra) (by decide) hpre).map.loadInt_isSome
    (Or.inl (by simp only [rsp, Reg64s.get64_rsp]; bv_omega))

theorem e_ld24 (hpre : Pre 96 A s) :
    (((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).storeInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).loadInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  exact ((Kit.Mid.init (F := 96) (ra := ra) (by decide) hpre).map.storeInt _ _ _).loadInt_isSome
    (Or.inl (by simp only [rsp, Reg64s.get64_rsp]; bv_omega))

theorem e_ld32 (hpre : Pre 96 A s) :
    ((Kit.pushes s ra regs).loadInt (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome
      = true := by
  have hle := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  exact (Kit.Fm.init (rs := regs) (ra := ra) (by decide) hpre).map.loadInt_isSome
    (Or.inl (by simp only [rsp, Reg64s.get64_rsp]; bv_omega))

-- The registers at the call of `produce`.
theorem e_rg {c : MachineData} (h1 : c.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64)
    (h2 : c.regs.rbp.toBitVec = s.regs.rdi.toBitVec) (h3 : c.regs.rbx.toBitVec = s.regs.rsi.toBitVec)
    (h4 : c.regs.r12 = s.regs.r12) (h5 : c.regs.r13 = s.regs.r13) (h6 : c.regs.r14 = s.regs.r14)
    (h7 : c.regs.r15 = s.regs.r15) : Rg s c :=
  ⟨by rw [h1]; bv_omega, h2, h3, by rw [h4], by rw [h5], by rw [h6], by rw [h7]⟩

end

/-! ## The invariants -/

section
variable (s : MachineData) (ra : Int64)

-- `.LB.Emission.generate.2`: `d` is out of range.
def At45 (t : MachineData) : Prop :=
  t.regs = (s.pushRa ra).regs ∧ t.dmem = (s.pushRa ra).dmem ∧ (env s).n ≤ (rsi s).toNat

-- `.LB.Emission.generate.0`: the result is in `rax` and memory.
def At42 (t : MachineData) : Prop := Fm s ra t.dmem ∧ Rg s t ∧ generateR s t

-- The variant: the back edges from `.LB.Emission.generate.1` go to `.LB.Emission.generate.0`.
def V : Label → MachineData → Nat
  | "generate", _ => 2
  | ".LB.Emission.generate.1", _ => 1
  | _, _ => 0

end

/-! ## After `produce` -/

theorem toNat_add_one (x : Word) (h : x.toNat < 1024) : (x + 1#64).toNat = x.toNat + 1 := by
  bv_omega

section
variable {s : MachineData} {ra : Int64} {t u : MachineData} {st1 : St} {A : MachineData → Prop}

theorem Rg.same (h : Rg s t) (h1 : u.regs.rsp = t.regs.rsp) (h2 : u.regs.rbp = t.regs.rbp)
    (h3 : u.regs.rbx = t.regs.rbx) (h4 : u.regs.r12 = t.regs.r12) (h5 : u.regs.r13 = t.regs.r13)
    (h6 : u.regs.r14 = t.regs.r14) (h7 : u.regs.r15 = t.regs.r15) : Rg s u :=
  ⟨h1 ▸ h.sp, h2 ▸ h.bp, h3 ▸ h.bx, h4 ▸ h.r12, h5 ▸ h.r13, h6 ▸ h.r14, h7 ▸ h.r15⟩

-- The stack of a jump target with the registers `Rg`.
theorem Rg.stk (h : Rg s u) :
    ((s.pushRa ra).regs.get64 .rsp - u.regs.get64 .rsp).toNat < 2 ^ 63 := by
  simp only [Reg64s.get64_rsp, pushRa_rsp, h.sp]; bv_omega

-- The state after `produce` returns `ok st1`.
structure Ap (s : MachineData) (ra : Int64) (t : MachineData) (st1 : St) : Prop where
  fm : Fm s ra t.dmem
  rg : Rg s t
  hd : (rsi s).toNat < (env s).n
  hp : produce (env s) (st s) (rsi s).toNat = .ok st1
  hst : st' s t = st1
  ax : t.regs.rax.toBitVec = 0#64

-- `.LB.Emission.generate.1`: `produce` returns `ok st1`, slot `d` lies below the top slot, its dest is not
-- `d`, and the values of slot `d` and of the top slot differ. `rdx` holds `len`.
def At44 (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ st1, Ap s ra t st1 ∧ (rsi s).toNat + 1 < st1.len ∧ st1.dest (rsi s).toNat ≠ (rsi s).toNat
    ∧ st1.val (rsi s).toNat ≠ st1.val (st1.len - 1)
    ∧ t.regs.rdx.toBitVec = rd t.dmem t.regs.rbp.toBitVec

theorem Ap.bp (h : Ap s ra t st1) : t.regs.rbp.toBitVec = rdi s := by
  simp only [rdi, Reg64s.get64_rdi, h.rg.bp]

theorem Ap.bx (h : Ap s ra t st1) : t.regs.rbx.toBitVec = rsi s := by
  simp only [rsi, Reg64s.get64_rsi, h.rg.bx]

theorem Ap.len_le (h : Ap s ra t st1) : st1.len ≤ 1024 := by
  have h1 := h.fm.wf.len_le
  have h2 := h.fm.wf.n_le
  simp only [maxStackSize] at h2
  rw [← h.hst, st', len_stOf]; omega

theorem Ap.d_lt (hpre : Pre 96 A s) (h : Ap s ra t st1) : (rsi s).toNat < 1024 := by
  have h1 : (env s).n = nOf s.dmem (rdi s) := n_envOf
  have : _ ≤ 1024 := hpre.1.n_le
  have := h.hd
  omega

theorem Ap.ld0 (h : Ap s ra t st1) : (t.dmem.loadInt t.regs.rbp.toBitVec 8).isSome = true :=
  word_isSome h.fm.wf (k := 0) (by decide) (by rw [h.bp]; simp [wordAt])

theorem Ap.ld_dest (hpre : Pre 96 A s) (h : Ap s ra t st1) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 56#64) 8).isSome = true := by
  have hd := h.d_lt hpre
  exact word_isSome h.fm.wf (k := DEST + (rsi s).toNat) (by simp only [DEST_eq, WORDS_eq]; omega)
    (by rw [h.bp, h.bx]; exact addr_dest _ _)

theorem Ap.dest (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len) :
    (rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 56#64)).toNat =
      st1.dest (rsi s).toNat := by
  rw [← h.hst] at hi ⊢
  rw [st', len_stOf] at hi
  rw [h.bp, h.bx, addr_dest, st', dest_stOf hi]

theorem Ap.dest_ne (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len)
    (hne : rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 56#64) ≠
      t.regs.rbx.toBitVec) :
    st1.dest (rsi s).toNat ≠ (rsi s).toNat := by
  intro he
  apply hne
  apply BitVec.eq_of_toNat_eq
  rw [h.dest hi, he, h.bx]

-- `je` jumps: slot `d` has its own dest.
theorem Ap.self (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len)
    (hz : rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 56#64) =
      t.regs.rbx.toBitVec) :
    generate (env s) (st s) (rsi s).toNat = .ok st1 := by
  have he := h.dest hi
  rw [hz, h.bx] at he
  rw [gen_ok h.hd h.hp]
  simp only [← he, ne_eq, not_true_eq_false, and_false, ↓reduceIte]

-- The struct holds `st1` and slot `d` lies below the top slot.
theorem Ap.sw (hpre : Pre 96 generateA s) (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len) :
    Sw t.dmem t.regs.rbp.toBitVec t.regs.rbx.toBitVec st1 := by
  have hn : (env s).n = nOf t.dmem (rdi s) := by
    show (envOf s.dmem (rdi s)).n = _
    rw [n_envOf, h.fm.n hpre]
  refine ⟨h.bp ▸ h.fm.wf, ?_, ?_, ?_⟩
  · rw [h.bp]; exact h.hst
  · rw [h.bp, ← hn]; exact Pos.produce hpre.2.2.1 h.hd h.hp
  · rw [h.bx]; exact hlt

theorem Ap.ld (h : Ap s ra t st1) : (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true :=
  fm_isSome h.fm (by rw [h.rg.sp]; bv_omega)

-- The precondition of `swapWith`.
theorem Ap.pre (hpre : Pre 96 generateA s) (h : Ap s ra t st1) {c : MachineData} (hc : c.dmem = t.dmem)
    (hrg : Rg s c) (hdi : c.regs.rdi = c.regs.rbp) : Pre swapWithF swapWithA c := by
  have hrd := hrg.rdi hdi
  have henv := (h.fm.keeps hpre).1
  have hA := hpre.2.2
  obtain ⟨-, hops, -⟩ := produce_shape h.hp
  have hst := h.hst
  simp only [st'] at hst
  refine Kit.Fm.pre (k := 24) (by decide) hpre h.fm hc hrg.rsp hrd ⟨?_, ?_⟩
  all_goals simp only [st, env, cap, hrd, hc, henv, hst]
  · exact Pos.produce hA.1 h.hd h.hp
  · rw [← n_envOf, henv, n_envOf]; simp only [generateA, st, cap] at hA hops; omega

end

/-! ## The blocks `.LB.Emission.generate.0` and `.LB.Emission.generate.2` -/

section
variable {s : MachineData} {ra : Int64} {t u : MachineData} {A : MachineData → Prop}

theorem At42.ld0 (ht : At42 s ra t) : (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true :=
  fm_isSome ht.1 (by rw [ht.2.1.sp]; bv_omega)

theorem At42.ld8 (ht : At42 s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true :=
  fm_isSome ht.1 (by rw [ht.2.1.sp]; bv_omega)

theorem At42.sp (ht : At42 s ra t) (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64) :
    rsp u = rsp s - 8#64 := by
  simp only [rsp, Reg64s.get64_rsp, hsp, ht.2.1.sp]; bv_omega

theorem At42.isSome (hpre : Pre 96 A s) (ht : At42 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64) : u.retAddr.isSome = true := by
  rw [Kit.Mid.retAddr (by decide) hpre (hu ▸ ht.1.toMid) (ht.sp hsp)]; rfl

theorem At45.fm (hpre : Pre 96 A s) (ht : At45 s ra t) (hu : u.dmem = t.dmem) :
    Kit.Fm 96 [] s ra u.dmem := by
  rw [hu, ht.2.1]; exact Kit.Fm.init (by decide) hpre

theorem At45.sp (ht : At45 s ra t) (hsp : u.regs.rsp = t.regs.rsp) : rsp u = rsp s - 8#64 := by
  simp only [rsp, Reg64s.get64_rsp, hsp, ht.1]; rfl

theorem At45.isSome (hpre : Pre 96 A s) (ht : At45 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) : u.retAddr.isSome = true := by
  rw [Kit.Mid.retAddr (by decide) hpre (ht.fm hpre hu).toMid (ht.sp hsp)]; rfl

end

-- The flag of `jne` after `sal`.
theorem nz_res (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result v r) = !(v == 0#64) := by
  simp [CondCode.interp, StatusFlags.from_result]

end Generate

end FlatShuffler
