import BbuKraken.Kit
import BbuKraken.ModelLemmas

/-!
The body triple of `generate` (`c/bbu/generate.S`). The body pushes `rbp` and
`rbx`, calls `produce`, and then swaps two dest words (`.LB52`) or calls
`swapWith` (`.LB53`).
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

namespace Generate

-- The registers that `generate` saves, in the order of the pushes.
abbrev regs : List Reg64 := [.rbp, .rbx]

-- The memory of `generate`: the frame of 104 bytes, the saved words and the struct.
abbrev Fm := Kit.Fm 104 regs

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
variable {m : Mem 64} {S : Addr}

-- A store to the dest word `i` sets the dest of slot `i`.
theorem stOf_store_dest (hw : Wf m S) {i : Nat} (hi : i < (stOf m S).len) (x : Word) :
    stOf (m.storeInt (wordAt S (DEST + i)) 8 x.toInt) S =
      { stOf m S with slots := (stOf m S).slots.set i ⟨(stOf m S).val i, x.toNat⟩ } := by
  have hs := hw.struct_lt
  have hl : _ ≤ 1024 := hw.len_le
  rw [len_stOf] at hi
  rw [val_stOf hi]
  simp only [WORDS_eq] at hs
  have hk : ∀ k, k < WORDS → k ≠ DEST + i →
      rd (m.storeInt (wordAt S (DEST + i)) 8 x.toInt) (wordAt S k) = rd m (wordAt S k) := by
    intro k hk hne
    exact rd_store_other _ (by simp only [WORDS_eq, DEST_eq] at *; bv_omega)
  have hops : ∀ k, k < 12 * nOf m S →
      rd (m.storeInt (wordAt S (DEST + i)) 8 x.toInt) (wordAt (opsOf m S) k) =
        rd m (wordAt (opsOf m S) k) := by
    intro k hk
    have : _ ≤ 1024 := hw.n_le
    have := hw.ops_lt
    refine rd_storeInt_of_disjoint fun y hy ho => hw.disj_struct y ?_ (Or.inl ?_)
    · simp only [Mem.Blocks.Inside, or_false, WORDS_eq, DEST_eq] at hy ⊢; bv_omega
    · simp only [Mem.Blocks.Inside, or_false] at ho ⊢; bv_omega
  have hopsOf : opsOf (m.storeInt (wordAt S (DEST + i)) 8 x.toInt) S = opsOf m S :=
    hk 6 (by decide) (by simp only [DEST_eq]; omega)
  have hnops := hw.nops_le
  unfold stOf
  simp only [hk 0 (by decide) (by simp only [DEST_eq]; omega), hk 1 (by decide) (by simp only [DEST_eq]; omega),
    hk 2 (by decide) (by simp only [DEST_eq]; omega)]
  congr 1
  · apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_set]
    simp only [List.length_map, List.length_range] at h1
    simp only [slotOf]
    split
    · subst_vars
      rw [hk (STACK + j) (by simp only [STACK, WORDS_eq]; omega) (by simp only [STACK, DEST_eq]; omega),
        rd_store_same _ rfl, BitVec.ofInt_toInt]
    · rw [hk (STACK + j) (by simp only [STACK, WORDS_eq]; omega) (by simp only [STACK, DEST_eq]; omega),
        hk (DEST + j) (by simp only [DEST_eq, WORDS_eq]; omega) (by omega)]
  · refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    simp only [opOf, hopsOf, hops (2 * j) (by omega), hops (2 * j + 1) (by omega)]

-- A store to a dest word keeps the struct well formed.
theorem wf_store_dest (hw : Wf m S) {i : Nat} (hi : i < 1024) (v : Int) :
    Wf (m.storeInt (wordAt S (DEST + i)) 8 v) S := by
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs
  have hu : Mem.UnchangedOutside [(wordAt S (DEST + i), 8)] m
      (m.storeInt (wordAt S (DEST + i)) 8 v) :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  refine Wf.congr hu hw ?_ (fun x hx => (hw.mapped.storeInt _ _ _) x (inside_append.mpr (Or.inl hx)))
    ?_ ?_
  · intro x hr hx
    simp only [Mem.Blocks.Inside, or_false] at hx
    rcases hr with hr | hr
    · simp only [wordAt, DEST_eq] at hr hx; bv_omega
    · exact hw.disj_struct x (Or.inl (by simp only [wordAt, DEST_eq, WORDS_eq] at hx ⊢; bv_omega))
        (Or.inr (Or.inr hr))
  · rw [rd_store_other _ (by simp only [DEST_eq]; bv_omega)]; exact hw.len_le
  · rw [rd_store_other _ (by simp only [DEST_eq]; bv_omega)]; exact hw.nops_le

end
/-! ## The frame of `generate` -/

section
variable {s : MachineData} {ra : Int64}

theorem fm_isSome {m : Mem 64} (h : Fm s ra m) {a : Addr}
    (ha : (a - (s.regs.rsp.toBitVec - 104#64)).toNat + 8 ≤ 104) : (m.loadInt a 8).isSome = true :=
  h.map.loadInt_isSome (Or.inl ha)

end
/-! ## The calls -/

theorem ok_congr {α : Type} {c s t : MachineData} {enc : α → Word} {f : α → St}
    (h : rdi c = rdi s) : Ok c t enc f = Ok s t enc f := by
  unfold Ok st'; rw [h]

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
theorem produce_pre {c : MachineData} (hpre : Pre 104 generateA s)
    (hc : c.dmem = Kit.pushes s ra regs) (hrg : Rg s c) (hrdi : c.regs.rdi = c.regs.rbp)
    (hrsi : c.regs.rsi = c.regs.rbx) (hd : (rsi s).toNat < (env s).n) : Pre produceF produceA c := by
  have hfm : Fm s ra _ := Kit.Fm.init (by decide) hpre
  have hst := Kit.st_pushes (rs := regs) (ra := ra) (by decide) hpre
  have henv := (hfm.keeps hpre).1
  have hrd := hrg.rdi hrdi
  have hA := hpre.2.2
  refine Kit.Fm.pre (k := 24) (by decide) hpre hfm hc hrg.rsp hrd ⟨?_, ?_, ?_⟩
  all_goals simp only [st, env, cap, rsi, Reg64s.get64_rsi, hrsi, hrg.bx, hrd, hc, hst, henv]
  · exact hd
  · exact hA.1
  · rw [← n_envOf, henv, n_envOf]; simp only [generateA, st, cap] at hA; omega

-- The state after the call of `produce`.
theorem after_produce {c t : MachineData} (hp : Post produceF produceR c t)
    (hag : (mod produceF c).Agree c t) (hpre : Pre 104 generateA s)
    (hc : c.dmem = Kit.pushes s ra regs) (hrg : Rg s c) (hrdi : c.regs.rdi = c.regs.rbp)
    (hrsi : c.regs.rsi = c.regs.rbx) :
    Fm s ra t.dmem ∧ Rg s t
      ∧ Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t := by
  have hfm : Fm s ra _ := Kit.Fm.init (by decide) hpre
  have hrd := hrg.rdi hrdi
  refine ⟨Kit.Fm.call (k := 24) (by decide) (by decide) hpre hfm hc hrg.rsp hrd hp hag,
    hrg.call hag, ?_⟩
  have h := hp.2.2
  unfold produceR at h
  rw [ok_congr hrd] at h
  simp only [st, env, rsi, Reg64s.get64_rsi, hrsi, hrg.bx, hrd, hc,
    Kit.st_pushes (rs := regs) (ra := ra) (by decide) hpre, (hfm.keeps hpre).1] at h
  exact h

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

-- `Res` only reads `rax` and the memory.
theorem res_ok {α : Type} {S : Addr} {r : M α} {enc : α → Word} {f : α → St} {s t u : MachineData}
    (h : Res S r (Ok s t enc f) t) (hm : u.dmem = t.dmem) (hax : rax u = rax t) :
    Res S r (Ok s u enc f) u := by
  rcases r with (⟨p, x⟩ | _) | a
  · exact ⟨hax.trans h.1, hm ▸ h.2.1, hm ▸ h.2.2⟩
  · exact hax.trans h
  · exact ⟨hax.trans h.1, by rw [st', hm]; exact h.2⟩

-- The words of the struct are mapped.
theorem word_isSome {m : Mem 64} {S a : Addr} (hw : Wf m S) {k : Nat} (hk : k < WORDS)
    (ha : a = wordAt S k) : (m.loadInt a 8).isSome = true :=
  ha ▸ hw.word_isSome hw.mapped hk

/-! ## The entry block -/

section
variable {s : MachineData} {ra : Int64} {A : MachineData → Prop}

-- The word `n` after the push of the return address.
theorem e_n (hpre : Pre 104 A s) :
    (rd (s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt)
      (s.regs.rdi.toBitVec + 24#64)).toNat = (env s).n := by
  have h := hdr_congr (Kit.Mid.init (F := 104) (ra := ra) (by decide) hpre).un hpre.disj (k := 3)
    (by omega) (by omega)
  simp only [MachineData.dmem_pushRa, wordAt, rdi, Reg64s.get64_rdi, Reg64s.get64_rsp] at h
  rw [show s.regs.rdi.toBitVec + 24#64 = s.regs.rdi.toBitVec + BitVec.ofNat 64 (8 * 3) from rfl, h,
    n_envOf]
  rfl

theorem e_ld3 (hpre : Pre 104 A s) :
    ((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).loadInt
      (s.regs.rdi.toBitVec + 24#64) 8).isSome = true :=
  loadInt_isSome_store _ (word_isSome hpre.1 (k := 3) (by decide) rfl)

theorem e_ld16 (hpre : Pre 104 A s) :
    ((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).loadInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  exact (Kit.Mid.init (F := 104) (ra := ra) (by decide) hpre).map.loadInt_isSome
    (Or.inl (by simp only [rsp, Reg64s.get64_rsp]; bv_omega))

theorem e_ld24 (hpre : Pre 104 A s) :
    (((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).storeInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).loadInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  exact ((Kit.Mid.init (F := 104) (ra := ra) (by decide) hpre).map.storeInt _ _ _).loadInt_isSome
    (Or.inl (by simp only [rsp, Reg64s.get64_rsp]; bv_omega))

theorem e_ld32 (hpre : Pre 104 A s) :
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

-- `.LB47`: `d` is out of range.
def At47 (t : MachineData) : Prop :=
  t.regs = (s.pushRa ra).regs ∧ t.dmem = (s.pushRa ra).dmem ∧ (env s).n ≤ (rsi s).toNat

-- `.LB44`: the result is in `rax` and memory.
def At44 (t : MachineData) : Prop := Fm s ra t.dmem ∧ Rg s t ∧ generateR s t

-- `.LB52`: the values of slot `d` and of the top slot are equal. `rdi` and `rcx` point
-- to the dest words of the top slot and of slot `d`, `rsi` holds the dest of slot `d`,
-- and `rax` holds 0, the result of `produce`.
def At52 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ (rsi s).toNat + 1 < (st' s t).len
    ∧ t.regs.rdi.toBitVec + 8248#64 = wordAt (rdi s) (DEST + ((st' s t).len - 1))
    ∧ t.regs.rcx.toBitVec + 8256#64 = wordAt (rdi s) (DEST + (rsi s).toNat)
    ∧ t.regs.rsi.toBitVec.toNat = (st' s t).dest (rsi s).toNat
    ∧ generate (env s) (st s) (rsi s).toNat =
      .ok (swapDestinations (st' s t) (rsi s).toNat ((st' s t).len - 1))
    ∧ t.regs.rax.toBitVec = 0#64

-- `.LB53`: `generate` calls `swapWith`.
def At53 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ (st' s t).trace.length < cap s
    ∧ generate (env s) (st s) (rsi s).toNat = swapWith (st' s t) (rsi s).toNat

-- The variant: the back edges from `.LB52` and `.LB53` go to `.LB44`.
def V : Label → MachineData → Nat
  | "generate", _ => 2
  | ".LB52", _ | ".LB53", _ => 1
  | _, _ => 0

end


/-! ## After `produce` -/

-- The word `c + x` of the struct at `S`.
theorem addr (S x : Word) (c : Nat) :
    S + x * 8#64 + BitVec.ofNat 64 (8 * c) = wordAt S (c + x.toNat) := by
  simp only [wordAt]; bv_omega

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

-- `jne` jumps: `produce` fails.
theorem jne_taken (hd : (rsi s).toNat < (env s).n)
    (h : Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t)
    (hz : t.regs.rax.toBitVec ≠ 0#64) : generateR s t := by
  unfold generateR
  rcases hp : produce (env s) (st s) (rsi s).toNat with (⟨p, x⟩ | _) | st1
  · rw [gen_err hd hp]; rw [hp] at h; exact h
  · rw [gen_err hd hp]; rw [hp] at h; exact h
  · rw [hp] at h
    exact absurd h.1 hz

-- `jne` does not jump: `produce` returns `ok`.
theorem jne_not (hfm : Fm s ra t.dmem) (hrg : Rg s t) (hd : (rsi s).toNat < (env s).n)
    (h : Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t)
    (hz : t.regs.rax.toBitVec = 0#64) : ∃ st1, Ap s ra t st1 := by
  rcases hp : produce (env s) (st s) (rsi s).toNat with (⟨p, x⟩ | _) | st1
  · rw [hp] at h
    have := h.1
    simp only [rax, Reg64s.get64_rax] at this
    rw [this] at hz
    exact absurd hz (by decide)
  · rw [hp] at h
    simp only [Res, rax, Reg64s.get64_rax] at h
    rw [h] at hz
    exact absurd hz (by decide)
  · rw [hp] at h
    exact ⟨st1, hfm, hrg, hd, hp, h.2, hz⟩

theorem Ap.bp (h : Ap s ra t st1) : t.regs.rbp.toBitVec = rdi s := by
  simp only [rdi, Reg64s.get64_rdi, h.rg.bp]

theorem Ap.bx (h : Ap s ra t st1) : t.regs.rbx.toBitVec = rsi s := by
  simp only [rsi, Reg64s.get64_rsi, h.rg.bx]

theorem Ap.len (h : Ap s ra t st1) : (rd t.dmem t.regs.rbp.toBitVec).toNat = st1.len := by
  rw [← h.hst, st', len_stOf, h.bp]; simp [wordAt]

theorem Ap.len_le (h : Ap s ra t st1) : st1.len ≤ 1024 := by
  have : _ ≤ 1024 := h.fm.wf.len_le
  rw [← h.hst, st', len_stOf]; exact this

theorem Ap.d_lt (hpre : Pre 104 A s) (h : Ap s ra t st1) : (rsi s).toNat < 1024 := by
  have h1 : (env s).n = nOf s.dmem (rdi s) := n_envOf
  have : _ ≤ 1024 := hpre.1.n_le
  have := h.hd
  omega

theorem Ap.lt (hpre : Pre 104 A s) (h : Ap s ra t st1)
    (hc : (t.regs.rbx.toBitVec + 1#64).toNat < (rd t.dmem t.regs.rbp.toBitVec).toNat) :
    (rsi s).toNat + 1 < st1.len := by
  have hd := h.d_lt hpre
  rw [h.len, h.bx, toNat_add_one _ hd] at hc
  omega

theorem Ap.ld0 (h : Ap s ra t st1) : (t.dmem.loadInt t.regs.rbp.toBitVec 8).isSome = true :=
  word_isSome h.fm.wf (k := 0) (by decide) (by rw [h.bp]; simp [wordAt])

theorem Ap.ld_dest (hpre : Pre 104 A s) (h : Ap s ra t st1) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 8256#64) 8).isSome = true := by
  have hd := h.d_lt hpre
  exact word_isSome h.fm.wf (k := 1032 + (rsi s).toNat) (by simp only [WORDS_eq]; omega)
    (by rw [h.bp, h.bx]; exact addr _ _ 1032)

theorem Ap.ld_val (hpre : Pre 104 A s) (h : Ap s ra t st1) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 64#64) 8).isSome = true := by
  have hd := h.d_lt hpre
  exact word_isSome h.fm.wf (k := 8 + (rsi s).toNat) (by simp only [WORDS_eq]; omega)
    (by rw [h.bp, h.bx]; exact addr _ _ 8)

theorem Ap.ld_top (h : Ap s ra t st1) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + rd t.dmem t.regs.rbp.toBitVec * 8#64 + 56#64)
      8).isSome = true := by
  have hl : _ ≤ 1024 := h.len_le
  have hL := h.len
  exact word_isSome h.fm.wf (k := 7 + st1.len) (by simp only [WORDS_eq]; omega)
    (by rw [← hL]; rw [h.bp] at hL ⊢; exact addr _ _ 7)

theorem Ap.dest (hpre : Pre 104 A s) (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len) :
    (rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 8256#64)).toNat =
      st1.dest (rsi s).toNat := by
  have hd := h.d_lt hpre
  rw [← h.hst] at hi ⊢
  rw [st', len_stOf] at hi
  rw [h.bp, h.bx, addr _ _ 1032, st', dest_stOf hi]
  rfl

theorem Ap.val (hpre : Pre 104 A s) (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len) :
    rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 64#64) =
      st1.val (rsi s).toNat := by
  have hd := h.d_lt hpre
  rw [← h.hst] at hi ⊢
  rw [st', len_stOf] at hi
  rw [h.bp, h.bx, addr _ _ 8, st', val_stOf hi]
  rfl

theorem Ap.top (h : Ap s ra t st1) (h1 : 1 ≤ st1.len) :
    rd t.dmem (t.regs.rbp.toBitVec + rd t.dmem t.regs.rbp.toBitVec * 8#64 + 56#64) =
      st1.val (st1.len - 1) := by
  have hl : _ ≤ 1024 := h.len_le
  have hL := h.len
  rw [h.bp] at hL ⊢
  have hL' : (rd t.dmem (rdi s)).toNat = (stOf t.dmem (rdi s)).len := by rw [hL, ← h.hst]
  rw [addr (rdi s) (rd t.dmem (rdi s)) 7, ← h.hst, st',
    val_stOf (i := (stOf t.dmem (rdi s)).len - 1) (by rw [← len_stOf]; omega), hL']
  congr 2; simp only [STACK]; omega

-- `jnb` jumps: slot `d` is the top slot.
theorem Ap.short (hpre : Pre 104 A s) (h : Ap s ra t st1)
    (hc : (rd t.dmem t.regs.rbp.toBitVec).toNat ≤ (t.regs.rbx.toBitVec + 1#64).toNat) :
    generate (env s) (st s) (rsi s).toNat = .ok st1 := by
  have hd := h.d_lt hpre
  rw [h.len, h.bx, toNat_add_one _ hd] at hc
  have : ¬ ((rsi s).toNat + 1 < st1.len) := by omega
  rw [gen_ok h.hd h.hp]
  simp only [this, false_and, ↓reduceIte]

theorem Ap.dest_ne (hpre : Pre 104 A s) (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len)
    (hne : t.regs.rbx.toBitVec ≠
      rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 8256#64)) :
    st1.dest (rsi s).toNat ≠ (rsi s).toNat := by
  intro he
  apply hne
  apply BitVec.eq_of_toNat_eq
  rw [h.dest hpre hi, he, h.bx]

-- `je` jumps: slot `d` has its own dest.
theorem Ap.self (hpre : Pre 104 A s) (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len)
    (hz : t.regs.rbx.toBitVec =
      rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 8256#64)) :
    generate (env s) (st s) (rsi s).toNat = .ok st1 := by
  have he := h.dest hpre hi
  rw [← hz, h.bx] at he
  rw [gen_ok h.hd h.hp]
  simp only [← he, ne_eq, not_true_eq_false, and_false, ↓reduceIte]

-- The last `jbe` does not jump: the top slot is too far.
theorem Ap.far (hpre : Pre 104 A s) (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len)
    (hne : st1.dest (rsi s).toNat ≠ (rsi s).toNat)
    (hv : rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 64#64) ≠
      rd t.dmem (t.regs.rbp.toBitVec + rd t.dmem t.regs.rbp.toBitVec * 8#64 + 56#64))
    (hb : ¬ (rd t.dmem t.regs.rbp.toBitVec - t.regs.rbx.toBitVec - 1#64).toNat ≤ 16) :
    generate (env s) (st s) (rsi s).toNat = .ok st1 := by
  have hl : _ ≤ 1024 := h.len_le
  have hL := h.len
  rw [h.val hpre (by omega), h.top (by omega)] at hv
  rw [h.bx] at hb
  have : ¬ st1.len - 1 - (rsi s).toNat ≤ MAX_SWAP_DEPTH := by
    simp only [MAX_SWAP_DEPTH]; intro hc; apply hb; rw [← hL] at hlt hc; bv_omega
  rw [gen_ok h.hd h.hp]
  simp only [hlt, ne_eq, hne, not_false_eq_true, and_self, hv, this, ↓reduceIte]

-- `jnb`, `je` or the last `jbe` jumps to `.LB44` with `ok st1`.
theorem Ap.fin (h : Ap s ra t st1) (hg : generate (env s) (st s) (rsi s).toNat = .ok st1)
    (hu : u.dmem = t.dmem) (hax : u.regs.rax = t.regs.rax) (hrg : Rg s u) : At44 s ra u := by
  refine ⟨hu ▸ h.fm, hrg, ?_⟩
  unfold generateR
  rw [hg]
  refine ⟨by simp only [rax, Reg64s.get64_rax, hax, h.ax], ?_⟩
  rw [st', hu]; exact h.hst

-- The `je` to `.LB52` jumps.
theorem Ap.at52 (hpre : Pre 104 A s) (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len)
    (hne : st1.dest (rsi s).toNat ≠ (rsi s).toNat)
    (hv : rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 64#64) =
      rd t.dmem (t.regs.rbp.toBitVec + rd t.dmem t.regs.rbp.toBitVec * 8#64 + 56#64))
    (hu : u.dmem = t.dmem) (hrg : Rg s u)
    (hdi : u.regs.rdi.toBitVec = t.regs.rbp.toBitVec + rd t.dmem t.regs.rbp.toBitVec * 8#64)
    (hax : u.regs.rax = t.regs.rax)
    (hcx : u.regs.rcx.toBitVec = t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64)
    (hsi : u.regs.rsi.toBitVec =
      rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 8256#64)) :
    At52 s ra u := by
  have hl : _ ≤ 1024 := h.len_le
  have hL := h.len
  have hd := h.d_lt hpre
  have hst : st' s u = st1 := by rw [st', hu]; exact h.hst
  rw [h.val hpre (by omega), h.top (by omega)] at hv
  refine ⟨hu ▸ h.fm, hrg, hst ▸ hlt, ?_, ?_, ?_, ?_, by rw [hax]; exact h.ax⟩
  · have hL' : (rd t.dmem (rdi s)).toNat = st1.len := by rw [← h.bp]; exact hL
    rw [hdi, hst, h.bp, show (8248#64 : Word) = BitVec.ofNat 64 (8 * 1031) from rfl,
      addr (rdi s) (rd t.dmem (rdi s)) 1031, hL']
    simp only [DEST_eq]; congr 1; omega
  · rw [hcx, h.bp, h.bx, show (8256#64 : Word) = BitVec.ofNat 64 (8 * 1032) from rfl,
      addr (rdi s) (rsi s) 1032]
    rfl
  · rw [hsi, h.dest hpre (by omega), hst]
  · rw [hst, gen_ok h.hd h.hp]
    simp only [hlt, ne_eq, hne, not_false_eq_true, and_self, hv, ↓reduceIte]

-- The `jbe` to `.LB53` jumps.
theorem Ap.at53 (hpre : Pre 104 generateA s) (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len)
    (hne : st1.dest (rsi s).toNat ≠ (rsi s).toNat)
    (hv : rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 64#64) ≠
      rd t.dmem (t.regs.rbp.toBitVec + rd t.dmem t.regs.rbp.toBitVec * 8#64 + 56#64))
    (hb : (rd t.dmem t.regs.rbp.toBitVec - t.regs.rbx.toBitVec - 1#64).toNat ≤ 16)
    (hu : u.dmem = t.dmem) (hrg : Rg s u) : At53 s ra u := by
  have hl : _ ≤ 1024 := h.len_le
  have hL := h.len
  have hst : st' s u = st1 := by rw [st', hu]; exact h.hst
  rw [h.val hpre (by omega), h.top (by omega)] at hv
  rw [h.bx] at hb
  have hfar : st1.len - 1 - (rsi s).toNat ≤ MAX_SWAP_DEPTH := by
    simp only [MAX_SWAP_DEPTH]; rw [← hL] at hlt ⊢; bv_omega
  have hA := hpre.2.2
  simp only [generateA] at hA
  obtain ⟨-, hops, -⟩ := produce_shape h.hp
  refine ⟨hu ▸ h.fm, hrg, by rw [hst, hops]; omega, ?_⟩
  rw [hst, gen_ok h.hd h.hp]
  simp only [hlt, ne_eq, hne, not_false_eq_true, and_self, hv, hfar, ↓reduceIte]

end

/-! ## The blocks `.LB44`, `.LB52`, `.LB53` and `.LB47` -/

-- The two stores of `.LB52` swap the dest words of slots `a` and `b`.
theorem stOf_swap {m : Mem 64} {S : Addr} (hw : Wf m S) {a b : Nat} (ha : a < (stOf m S).len)
    (hb : b < (stOf m S).len) (hab : a ≠ b) (x : Word) (hx : x.toNat = (stOf m S).dest a) :
    stOf ((m.storeInt (wordAt S (DEST + a)) 8 (rd m (wordAt S (DEST + b))).toInt).storeInt
      (wordAt S (DEST + b)) 8 x.toInt) S = swapDestinations (stOf m S) a b := by
  have hl : _ ≤ 1024 := hw.len_le
  rw [← len_stOf] at hl
  have hw1 := wf_store_dest hw (i := a) (by omega) (rd m (wordAt S (DEST + b))).toInt
  have hb1 : b < (stOf (m.storeInt (wordAt S (DEST + a)) 8 (rd m (wordAt S (DEST + b))).toInt) S).len := by
    rw [stOf_store_dest hw ha]; simpa [St.len] using hb
  rw [stOf_store_dest hw1 hb1, stOf_store_dest hw ha, ← dest_stOf (len_stOf ▸ hb), hx]
  simp [swapDestinations, St.val, hab]

section
variable {s : MachineData} {ra : Int64} {t u : MachineData} {A : MachineData → Prop}

-- A store to a dest word keeps the frame.
theorem Fm.store_dest {m : Mem 64} (hpre : Pre 104 A s) (h : Fm s ra m) {i : Nat} (hi : i < 1024)
    (v : Int) : Fm s ra (m.storeInt (wordAt (rdi s) (DEST + i)) 8 v) := by
  have hs := h.wf.struct_lt
  simp only [WORDS_eq] at hs
  have hwr := (h.keeps hpre).2.2
  have hn : nOf m (rdi s) = nOf s.dmem (rdi s) :=
    congrArg BitVec.toNat (hdr_congr h.un hpre.disj (k := 3) (by omega) (by omega))
  have hw : Mem.Blocks.Inside (wordAt (rdi s) (DEST + i)) 8 (writable s.dmem (rdi s)) :=
    inside_writable (Or.inr (Or.inl (by simp only [wordAt, STACK, DEST_eq, WORDS_eq]; bv_omega)))
  refine Kit.Fm.write (by decide) hpre h (.storeInt (fun _ _ => rfl) hw _) ?_ ?_ ?_
  · rw [← hwr]
    exact Mem.Mapped.storeInt (fun x hx => h.wf.mapped x (inside_append.mpr (Or.inl hx))) _ _ _
  · rw [rd_store_other _ (by simp only [DEST_eq]; bv_omega)]; exact h.wf.len_le
  · rw [rd_store_other _ (by simp only [DEST_eq]; bv_omega), ← hn]; exact h.wf.nops_le

theorem At44.ld0 (ht : At44 s ra t) : (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true :=
  fm_isSome ht.1 (by rw [ht.2.1.sp]; bv_omega)

theorem At44.ld8 (ht : At44 s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true :=
  fm_isSome ht.1 (by rw [ht.2.1.sp]; bv_omega)

theorem At44.sp (ht : At44 s ra t) (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64) :
    rsp u = rsp s - 8#64 := by
  simp only [rsp, Reg64s.get64_rsp, hsp, ht.2.1.sp]; bv_omega

theorem At44.isSome (hpre : Pre 104 A s) (ht : At44 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64) : u.retAddr.isSome = true := by
  rw [Kit.Mid.retAddr (by decide) hpre (hu ▸ ht.1.toMid) (ht.sp hsp)]; rfl

-- `pop rbx; pop rbp; ret` of `.LB44`.
theorem At44.ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    (hpre : Pre 104 A s) (ht : At44 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem t.regs.rsp.toBitVec)
    (hbp : u.regs.rbp.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64))
    (hax : u.regs.rax = t.regs.rax) (h12 : u.regs.r12 = t.regs.r12) (h13 : u.regs.r13 = t.regs.r13)
    (h14 : u.regs.r14 = t.regs.r14) (h15 : u.regs.r15 = t.regs.r15) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post generateF generateR s t ∧ (mod generateF s).Agree s t)
      u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  have hsp' := ht.sp hsp
  obtain ⟨hfm, hrg, hR⟩ := ht
  have hm : rd t.dmem (s.regs.rsp.toBitVec - 24#64) = s.regs.rbx.toBitVec := hfm.saved 1 (by decide)
  have hp : rd t.dmem (s.regs.rsp.toBitVec - 16#64) = s.regs.rbp.toBitVec := hfm.saved 0 (by decide)
  refine Kit.Fm.ret (by decide) hpre (hu ▸ hfm) hsp' (saved_regs ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [hbx, hrg.sp, hm]
  · rw [hbp, hrg.sp, show s.regs.rsp.toBitVec - 24#64 + 8#64 = s.regs.rsp.toBitVec - 16#64 by
      bv_omega, hp]
  · rw [h12, hrg.r12]
  · rw [h13, hrg.r13]
  · rw [h14, hrg.r14]
  · rw [h15, hrg.r15]
  · intro t' hm' hax'
    exact res_ok hR (hm'.trans hu) (hax'.trans (by simp only [rax, Reg64s.get64_rax, hax]))

theorem At47.fm (hpre : Pre 104 A s) (ht : At47 s ra t) (hu : u.dmem = t.dmem) :
    Kit.Fm 104 [] s ra u.dmem := by
  rw [hu, ht.2.1]; exact Kit.Fm.init (by decide) hpre

theorem At47.sp (ht : At47 s ra t) (hsp : u.regs.rsp = t.regs.rsp) : rsp u = rsp s - 8#64 := by
  simp only [rsp, Reg64s.get64_rsp, hsp, ht.1]; rfl

theorem At47.isSome (hpre : Pre 104 A s) (ht : At47 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) : u.retAddr.isSome = true := by
  rw [Kit.Mid.retAddr (by decide) hpre (ht.fm hpre hu).toMid (ht.sp hsp)]; rfl

-- `mov rax, -2; ret` of `.LB47`.
theorem At47.ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    (hpre : Pre 104 A s) (ht : At47 s ra t) (hu : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hax : u.regs.rax.toBitVec = -2#64) (hbx : u.regs.rbx = t.regs.rbx)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12) (h13 : u.regs.r13 = t.regs.r13)
    (h14 : u.regs.r14 = t.regs.r14) (h15 : u.regs.r15 = t.regs.r15) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post generateF generateR s t ∧ (mod generateF s).Agree s t)
      u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  refine Kit.Fm.ret (by decide) hpre (ht.fm hpre hu) (ht.sp hsp) (saved_regs ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [hbx, ht.1]; rfl
  · rw [hbp, ht.1]; rfl
  · rw [h12, ht.1]; rfl
  · rw [h13, ht.1]; rfl
  · rw [h14, ht.1]; rfl
  · rw [h15, ht.1]; rfl
  · intro t' _ hax'
    unfold generateR
    rw [show generate (env s) (st s) (rsi s).toNat = .error .assertion by
      unfold generate; simp only [ht.2.2, ↓reduceIte]]
    exact hax'.trans (by simp only [rax, Reg64s.get64_rax, hax])

theorem At52.len_le (ht : At52 s ra t) : (st' s t).len ≤ 1024 := by
  have := ht.1.wf.len_le; rw [st', len_stOf]; exact this

theorem At52.ld_top (ht : At52 s ra t) :
    (t.dmem.loadInt (t.regs.rdi.toBitVec + 8248#64) 8).isSome = true := by
  have : _ ≤ 1024 := ht.len_le
  have := ht.2.2.1
  exact word_isSome ht.1.wf (by simp only [DEST_eq, WORDS_eq]; omega) ht.2.2.2.1

theorem At52.ld_d (ht : At52 s ra t) :
    (t.dmem.loadInt (t.regs.rcx.toBitVec + 8256#64) 8).isSome = true := by
  have : _ ≤ 1024 := ht.len_le
  have := ht.2.2.1
  exact word_isSome ht.1.wf (by simp only [DEST_eq, WORDS_eq]; omega) ht.2.2.2.2.1

-- The stores of `.LB52`.
theorem At52.fin (hpre : Pre 104 A s) (ht : At52 s ra t)
    (hu : u.dmem = (t.dmem.storeInt (t.regs.rcx.toBitVec + 8256#64) 8
      (rd t.dmem (t.regs.rdi.toBitVec + 8248#64)).toInt).storeInt (t.regs.rdi.toBitVec + 8248#64) 8
        t.regs.rsi.toBitVec.toInt)
    (hax : u.regs.rax = t.regs.rax) (hrg : Rg s u) : At44 s ra u := by
  have hl : _ ≤ 1024 := ht.len_le
  obtain ⟨hfm, -, hlt, hra, hrc, hsi, hg, h0⟩ := ht
  rw [hra, hrc] at hu
  refine ⟨hu ▸ (hfm.store_dest hpre (by omega) _).store_dest hpre (by omega) _, hrg, ?_⟩
  unfold generateR
  rw [hg]
  refine ⟨by simp only [rax, Reg64s.get64_rax, hax, h0], ?_⟩
  simp only [st', hu] at hlt hsi ⊢
  exact stOf_swap hfm.wf (by omega) (by omega) (by omega) _ hsi

theorem At53.ld (ht : At53 s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true :=
  fm_isSome ht.1 (by rw [ht.2.1.sp]; bv_omega)

-- The precondition of `swapWith`.
theorem At53.pre (hpre : Pre 104 A s) (ht : At53 s ra t) {c : MachineData} (hc : c.dmem = t.dmem)
    (hrg : Rg s c) (hdi : c.regs.rdi = c.regs.rbp) : Pre swapWithF swapWithA c := by
  have hrd := hrg.rdi hdi
  have henv := (ht.1.keeps hpre).1
  have hA := ht.2.2.1
  refine Kit.Fm.pre (k := 24) (by decide) hpre ht.1 hc hrg.rsp hrd ?_
  simp only [swapWithA, st, cap, hrd, hc]
  rw [← n_envOf, henv, n_envOf]; exact hA

-- The state after the call of `swapWith`.
theorem At53.after {c : MachineData} (hp : Post swapWithF swapWithR c u)
    (hag : (mod swapWithF c).Agree c u) (hpre : Pre 104 A s) (ht : At53 s ra t)
    (hc : c.dmem = t.dmem) (hrg : Rg s c) (hdi : c.regs.rdi = c.regs.rbp)
    (hsi : c.regs.rsi = c.regs.rbx) : At44 s ra u := by
  have hrd := hrg.rdi hdi
  refine ⟨Kit.Fm.call (k := 24) (by decide) (by decide) hpre ht.1 hc hrg.rsp hrd hp hag,
    hrg.call hag, ?_⟩
  have h := hp.2.2
  unfold swapWithR at h
  rw [ok_congr hrd] at h
  simp only [st, rsi, Reg64s.get64_rsi, hsi, hrg.bx, hrd, hc] at h
  unfold generateR
  rw [ht.2.2.2]
  exact h

end
end Generate

-- A hypothesis of type `t`, found with reducible unification only.
local macro "hyp% " t:term : term => `((by with_reducible assumption : $t))

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

open Generate

theorem generate_body [Host] [FunDecls]
    (hprod : Spec "produce" produceF produceA produceR)
    (hswap : Spec "swapWith" swapWithF swapWithA swapWithR) :
    Body generateAsm generateF generateA generateR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 104 generateA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "generate", t => t = s.pushRa ra
      | .label ".LB44", t => At44 s ra t
      | .label ".LB52", t => At52 s ra t
      | .label ".LB53", t => At53 s ra t
      | .label ".LB47", t => At47 s ra t
      | _, _ => False)
    V ?_ rfl
  cfg_cases
  case left t ht => subst ht; kvcgen64
  case right.left t ht =>
    subst ht
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 => exact e_ld3 hpre
    case vc2 =>
      have hc := (hyp% CondCode.nc.interp _ = true)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', Kit.cf_sub'] at hc
      rw [e_n hpre] at hc
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; simp [pushRa_rsp]
      · exact ⟨rfl, rfl, hc⟩
      · simp [V]
    case vc3 => exact e_ld16 hpre
    case vc4 => exact e_ld24 hpre
    case vc5 => exact e_ld32 hpre
    case vc6 =>
      have hc := (hyp% CondCode.nc.interp _ = false)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hc
      rw [e_n hpre] at hc
      exact produce_pre hpre rfl (e_rg rfl rfl rfl rfl rfl rfl rfl) rfl rfl hc
    all_goals
      have hc0 := (hyp% CondCode.nc.interp (StatusFlags.from_result (s.regs.rsi.toBitVec - _) _) = false)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hc0
      rw [e_n hpre] at hc0
      have hp := (hyp% Post produceF produceR _ _)
      have hag := (hyp% (mod produceF _).Agree _ _)
      obtain ⟨hfm, hrg, hres⟩ := after_produce hp hag hpre rfl (e_rg rfl rfl rfl rfl rfl rfl rfl) rfl rfl
      have hs := (hyp% CondCode.nz.interp _ = _)
      rw [CondCode.interp_nz, ← CondCode.interp_z, Kit.z_test] at hs
    case vc7 =>
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hrg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact ⟨hfm, hrg.same rfl rfl rfl rfl rfl rfl rfl, res_ok (jne_taken hc0 hres (by simpa using hs)) rfl rfl⟩
      · simp [V]
    all_goals obtain ⟨st1, hap⟩ := jne_not hfm hrg hc0 hres (by simpa using hs)
    case vc8 => exact hap.ld0
    case vc9 =>
      have hc := (hyp% CondCode.nc.interp (StatusFlags.from_result (_ + 1#64 - _) _) = true)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', Kit.cf_sub'] at hc
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hap.rg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact hap.fin (hap.short hpre hc) rfl rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl)
      · simp [V]
    all_goals
      have hc := (hyp% CondCode.nc.interp (StatusFlags.from_result (_ + 1#64 - _) _) = false)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hc
      have hlt := hap.lt hpre hc
    case vc10 => exact hap.ld_dest hpre
    case vc11 =>
      have hz := (hyp% CondCode.z.interp (StatusFlags.from_result (_ - rd _ (_ + 8256#64)) _) = true)
      rw [Kit.z_sub, beq_iff_eq] at hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hap.rg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact hap.fin (hap.self hpre (by omega) hz) rfl rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl)
      · simp [V]
    all_goals
      have hz1 := (hyp% CondCode.z.interp (StatusFlags.from_result (_ - rd _ (_ + 8256#64)) _) = false)
      rw [Kit.z_sub, beq_eq_false_iff_ne] at hz1
      have hne := hap.dest_ne hpre (by omega) hz1
    case vc12 => exact hap.ld_top
    case vc13 => exact hap.ld_val hpre
    case vc14 =>
      have hz2 := (hyp% CondCode.z.interp (StatusFlags.from_result (rd _ (_ + 64#64) - _) _) = true)
      rw [Kit.z_sub, beq_iff_eq] at hz2
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hap.rg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact hap.at52 hpre hlt hne hz2 rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl
      · simp [V]
    all_goals
      have hz2 := (hyp% CondCode.z.interp (StatusFlags.from_result (rd _ (_ + 64#64) - _) _) = false)
      rw [Kit.z_sub, beq_eq_false_iff_ne] at hz2
      have hb := (hyp% CondCode.be.interp _ = _)
      rw [Kit.be_sub_imm _ _ (by decide)] at hb
    case vc15 =>
      rw [decide_eq_true_iff] at hb
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hap.rg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact hap.at53 hpre hlt hne hz2 hb rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl)
      · simp [V]
    case vc16 =>
      rw [decide_eq_false_iff_not] at hb
      exact hap.fin (hap.far hpre hlt hne hz2 hb) rfl rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl)
    case vc17 => simp [V]
  case right.right.left t ht =>
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 => exact ht.ld0
    case vc2 => exact ht.ld8
    case vc3 => exact ht.isSome hpre rfl rfl
    case vc4 => exact ht.ret hpre rfl rfl rfl rfl rfl rfl rfl rfl rfl
  case right.right.right.left t ht =>
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 => exact ht.ld_top
    case vc2 => exact ht.ld_d
    case vc3 => exact loadInt_isSome_store _ ht.ld_top
    case vc4 =>
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        exact (ht.2.1.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact ht.fin hpre rfl rfl (ht.2.1.same rfl rfl rfl rfl rfl rfl rfl)
      · simp [V]
  case right.right.right.right.left t ht =>
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 => exact ht.ld
    case vc2 => exact ht.pre hpre rfl (ht.2.1.same rfl rfl rfl rfl rfl rfl rfl) rfl
    case vc3 =>
      have hp := (hyp% Post swapWithF swapWithR _ _)
      have hag := (hyp% (mod swapWithF _).Agree _ _)
      have h41 := At53.after hp hag hpre ht rfl (ht.2.1.same rfl rfl rfl rfl rfl rfl rfl) rfl rfl
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        exact h41.2.1.stk
      · exact h41
      · simp [V]
  case right.right.right.right.right t ht =>
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 => exact ht.isSome hpre rfl rfl
    case vc2 => exact ht.ret hpre rfl rfl rfl rfl rfl rfl rfl rfl rfl

end Bbu
