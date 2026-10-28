import BbuKraken.Contracts

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

/-! ## Leaf functions

A leaf function writes only its return address: the memory at `ret` is the
memory after the call.
-/

section Leaf
variable {s t : MachineData} {ra : Int64} {A : MachineData → Prop}

-- The call writes only the return address, in the frame.
theorem unchanged_pushRa : Mem.UnchangedOutside [frame 8 s] s.dmem (s.pushRa ra).dmem :=
  Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _

-- The memory after the call keeps the struct.
theorem pushRa_keeps (hpre : Pre 8 A s) :
    Wf (s.pushRa ra).dmem (rdi s) ∧ Mem.Mapped [frame 8 s] (s.pushRa ra).dmem
      ∧ stOf (s.pushRa ra).dmem (rdi s) = st s ∧ envOf (s.pushRa ra).dmem (rdi s) = env s := by
  obtain ⟨hw, hf, -⟩ := hpre
  have hu := unchanged_pushRa (s := s) (ra := ra)
  have hd := disjoint_symm hf.disj
  exact ⟨Wf.congr_of_disjoint hu hw hd, hf.mapped.storeInt _ _ _, stOf_congr hu hw hd,
    (envOf_congr hu hw (disjoint_mono (fun x hx => inside_append.mpr (Or.inr hx)) hd)).1⟩

@[simp] theorem pushRa_rax : (s.pushRa ra).regs.rax = s.regs.rax := rfl
@[simp] theorem pushRa_rbx : (s.pushRa ra).regs.rbx = s.regs.rbx := rfl
@[simp] theorem pushRa_rcx : (s.pushRa ra).regs.rcx = s.regs.rcx := rfl
@[simp] theorem pushRa_rdx : (s.pushRa ra).regs.rdx = s.regs.rdx := rfl
@[simp] theorem pushRa_rsi : (s.pushRa ra).regs.rsi = s.regs.rsi := rfl
@[simp] theorem pushRa_rdi : (s.pushRa ra).regs.rdi = s.regs.rdi := rfl
@[simp] theorem pushRa_rbp : (s.pushRa ra).regs.rbp = s.regs.rbp := rfl
@[simp] theorem pushRa_r8 : (s.pushRa ra).regs.r8 = s.regs.r8 := rfl
@[simp] theorem pushRa_r9 : (s.pushRa ra).regs.r9 = s.regs.r9 := rfl
@[simp] theorem pushRa_r10 : (s.pushRa ra).regs.r10 = s.regs.r10 := rfl
@[simp] theorem pushRa_r11 : (s.pushRa ra).regs.r11 = s.regs.r11 := rfl
@[simp] theorem pushRa_r12 : (s.pushRa ra).regs.r12 = s.regs.r12 := rfl
@[simp] theorem pushRa_r13 : (s.pushRa ra).regs.r13 = s.regs.r13 := rfl
@[simp] theorem pushRa_r14 : (s.pushRa ra).regs.r14 = s.regs.r14 := rfl
@[simp] theorem pushRa_r15 : (s.pushRa ra).regs.r15 = s.regs.r15 := rfl

-- The state at `ret` of a leaf function that returns `r`.
def Done (s : MachineData) (ra : Int64) (r : Word) (t : MachineData) : Prop :=
  t.dmem = (s.pushRa ra).dmem ∧ rsp t = rsp s - 8#64 ∧ rax t = r
    ∧ ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q

theorem Done.intro {r : Word} (hm : t.dmem = (s.pushRa ra).dmem)
    (hsp : t.regs.rsp = (s.pushRa ra).regs.rsp) (hax : rax t = r) (hbx : t.regs.rbx = s.regs.rbx)
    (hbp : t.regs.rbp = s.regs.rbp) (h12 : t.regs.r12 = s.regs.r12)
    (h13 : t.regs.r13 = s.regs.r13) (h14 : t.regs.r14 = s.regs.r14)
    (h15 : t.regs.r15 = s.regs.r15) : Done s ra r t := by
  refine ⟨hm, ?_, hax, fun q hq => ?_⟩
  · simp [hsp, MachineData.pushRa]
  · cases q <;> simp_all

-- A state inside a leaf function: the memory, `rsp` and the callee-saved
-- registers are those after the call.
structure Keep (s : MachineData) (ra : Int64) (t : MachineData) : Prop where
  mem : t.dmem = (s.pushRa ra).dmem
  sp : t.regs.rsp = (s.pushRa ra).regs.rsp
  bx : t.regs.rbx = s.regs.rbx
  bp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

theorem Keep.init : Keep s ra (s.pushRa ra) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.next {t' : MachineData} (h : Keep s ra t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbx : t'.regs.rbx = t.regs.rbx)
    (hbp : t'.regs.rbp = t.regs.rbp) (h12 : t'.regs.r12 = t.regs.r12)
    (h13 : t'.regs.r13 = t.regs.r13) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) : Keep s ra t' :=
  ⟨hm.trans h.mem, hsp.trans h.sp, hbx.trans h.bx, hbp.trans h.bp, h12.trans h.r12,
    h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩


theorem Keep.retAddr (h : Keep s ra t) : t.retAddr = some ra := by
  have hsp : t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 := by
    rw [Reg64s.get64_rsp, h.sp]; rfl
  rw [MachineData.retAddr, h.mem, hsp]
  exact MachineData.retAddr_pushRa s ra

theorem Keep.done {r : Word} (h : Keep s ra t) (hax : rax t = r) : Done s ra r t :=
  Done.intro h.mem h.sp hax h.bx h.bp h.r12 h.r13 h.r14 h.r15


-- A state with the stack pointer of the call is at or below it.
theorem stack_pushRa (h : t.regs.rsp = (s.pushRa ra).regs.rsp) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by simp [h])

theorem Done.retAddr {r : Word} (h : Done s ra r t) : t.retAddr = some ra := by
  have hsp : t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 := h.2.1
  rw [MachineData.retAddr, h.1, hsp]
  exact MachineData.retAddr_pushRa s ra

-- `ret` from a `Done` state gives the postcondition.
theorem Done.ret [Host] {r : Word} {R : MachineData → MachineData → Prop} {ls : List Label}
    {I' : CfgLabel → Nat → Unit → MachineData → Prop} (hpre : Pre 8 A s) (h : Done s ra r t)
    (hR : ∀ t', t'.dmem = (s.pushRa ra).dmem → rax t' = r → R s t') :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post 8 R s t ∧ (mod 8 s).Agree s t) t.retAddr.get!
      { regs := t.regs.set64 Reg64.rsp (t.regs.get64 Reg64.rsp + 8#64), zmms := t.zmms,
        status := t.status, dmem := t.dmem } := by
  have hra := h.retAddr
  obtain ⟨hm, hsp, hax, hr⟩ := h
  replace hsp : t.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 := hsp
  obtain ⟨hw, hmap, -⟩ := pushRa_keeps (ra := ra) hpre
  refine Or.inr ⟨⟨by simp [hra], ⟨hm ▸ hw, hm ▸ hmap, hR _ hm (by simpa using hax)⟩,
    fun q hq => ?_, ?_⟩, fun _ _ _ => ?_⟩
  · simp only [Reg64s.get64_set64]
    split
    · subst_vars; rw [hsp]; bv_omega
    · exact hr q (by simp_all [mod])
  · simp only [hm]
    exact fun b hb => unchanged_pushRa b fun h => hb (h.imp id fun h => h.elim)
  · apply MachineData.stackBelow_of_add_eight
    simp [MachineData.pushRa, hsp]
    bv_omega

end Leaf

/-! ## Flags and addresses -/

-- `cmpq $1, v; jbe` jumps iff `v < 2`.
theorem be_sub_one (v : BitVec 64) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result (v - 1#64)
      { cf := (((v - 1#64).toNat : Int) != (v.toNat : Int) - 1), af, of })
      = decide (v.toNat < 2) := by
  simp only [CondCode.interp_be, StatusFlags.cf_from_result, StatusFlags.zf_from_result]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, ← BitVec.toNat_inj, BitVec.toNat_sub,
    BitVec.zero_eq, BitVec.toNat_ofNat, decide_eq_true_eq, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub]
  have := v.isLt
  omega

-- `testb $1, v; jne` jumps iff `v` is odd.
theorem nz_and_one (v : BitVec 64) (af : Bool) :
    CondCode.nz.interp (StatusFlags.from_result (v.take 8 &&& 1#8) { cf := false, af, of := false })
      = decide (v.toNat % 2 = 1) := by
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result]
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_and,
    BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.and_one_is_mod, decide_eq_true_eq, BitVec.zero_eq]
  omega

-- `cmpb $0, b; setne %al; movzbl %al, %eax` gives `b != 0`.
theorem setne_zero (b : BitVec 8) (cf af of : Bool) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8
      (CondCode.nz.interp (StatusFlags.from_result (b - 0#8) { cf, af, of })).toNat))
      = BitVec.ofNat 64 (b != 0#8).toNat := by
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.sub_zero, BitVec.zero_eq, bne]
  cases (b == 0#8) <;> rfl

-- `subq $2, v; shrq v` for an even `v ≥ 2`.
theorem sub_two_shr {v : BitVec 64} (h2 : 2 ≤ v.toNat) :
    (v - 2#64).ushiftRight (((1#64).take 8).toNat &&& 63) = BitVec.ofNat 64 ((v.toNat - 2) / 2) := by
  have h1 : ((1#64).take 8).toNat &&& 63 = 1 := by decide
  rw [h1]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have := v.isLt
  omega

-- The header words 3 to 7 are readable.
theorem inside_hdr {m : Mem 64} {S : Addr} {k : Nat} (h3 : 3 ≤ k) (h8 : k < 8) :
    Mem.Blocks.Inside (wordAt S k) 8 (readable m S) := by
  have : wordAt S k = wordAt S 3 + BitVec.ofNat 64 (8 * (k - 3)) := by bv_omega
  rw [this]
  exact Mem.Blocks.Inside.base_add (by simp only [BitVec.toNat_ofNat]; omega)

-- `testq w, w; je` jumps iff `w = 0`.
theorem z_and_self (w : BitVec 64) (af : Bool) :
    CondCode.z.interp (StatusFlags.from_result (w &&& w) { cf := false, af, of := false })
      = (w == 0#64) := by
  simp [CondCode.interp_z, StatusFlags.zf_from_result]

-- `cmpq b, a; je` jumps iff `a = b`.
theorem z_sub (a b : BitVec 64) (cf af of : Bool) :
    CondCode.z.interp (StatusFlags.from_result (a - b) { cf, af, of }) = (a == b) := by
  simp only [CondCode.interp_z, StatusFlags.zf_from_result]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, BitVec.zero_eq]
  constructor
  · intro h; rw [← BitVec.sub_add_cancel a b, h, BitVec.zero_add]
  · rintro rfl; exact BitVec.sub_self a

-- `cmpq b, a; jne` jumps iff `a ≠ b`.
theorem nz_sub (a b : BitVec 64) (cf af of : Bool) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) { cf, af, of }) = !(a == b) := by
  rw [← z_sub a b cf af of]
  simp [CondCode.interp_z, CondCode.interp_nz]

-- The words 0 to 2 of the header are writable.
theorem inside_hdr0 {m : Mem 64} {S : Addr} {k : Nat} (hk : k < 3) :
    Mem.Blocks.Inside (wordAt S k) 8 (writable m S) :=
  Mem.Blocks.Inside.base_add (by simp only [BitVec.toNat_ofNat]; omega)

-- The words of the stack and dest arrays are writable.
theorem inside_arr {m : Mem 64} {S : Addr} {k : Nat} (h1 : STACK ≤ k) (h2 : k < WORDS) :
    Mem.Blocks.Inside (wordAt S k) 8 (writable m S) := by
  simp only [STACK, WORDS_eq] at h1 h2
  have : wordAt S k = wordAt S STACK + BitVec.ofNat 64 (8 * (k - 8)) := by
    simp only [STACK]; bv_omega
  rw [this]
  exact (Mem.Blocks.Inside.base_add (by simp only [BitVec.toNat_ofNat, MAX_N]; omega)).tail

theorem Wf.load_readable {m : Mem 64} {S x : Addr} {n : Nat} (hw : Wf m S)
    (h : Mem.Blocks.Inside x n (readable m S)) : (m.loadInt x n).isSome = true :=
  hw.mapped.loadInt_isSome (inside_append.mpr (Or.inr h))

theorem Wf.load_writable {m : Mem 64} {S x : Addr} {n : Nat} (hw : Wf m S)
    (h : Mem.Blocks.Inside x n (writable m S)) : (m.loadInt x n).isSome = true :=
  hw.mapped.loadInt_isSome (inside_append.mpr (Or.inl h))

/-! ## `is_spilled` -/

-- A target value `v` that is a variable selects its spilled byte.
theorem isSpilled_envOf {m : Mem 64} {S : Addr} {v : Word} {d : Nat} (hd : d < nOf m S)
    (hv : rd m (wordAt (tgtOf m S) d) = v) (h2 : 2 ≤ v.toNat) (he : v.toNat % 2 = 0) :
    isSpilled (envOf m S) v = (rdb m (splOf m S + BitVec.ofNat 64 ((v.toNat - 2) / 2)) != 0#8) := by
  have ht : tgtVar m S ((v.toNat - 2) / 2) = true :=
    List.any_eq_true.mpr ⟨d, List.mem_range.mpr hd, by simp [hv, h2, he]⟩
  simp only [isSpilled, envOf, ht, ite_true, h2, he]
  simp [bne]
  congr 1

-- The spilled byte of a target variable is in `splBlocks`.
theorem inside_splBlocks {m : Mem 64} {S : Addr} {v : Word} {d : Nat} (hd : d < nOf m S)
    (hv : rd m (wordAt (tgtOf m S) d) = v) (h2 : 2 ≤ v.toNat) (he : v.toNat % 2 = 0) :
    Mem.Blocks.Inside (splOf m S + BitVec.ofNat 64 ((v.toNat - 2) / 2)) 1 (splBlocks m S) :=
  inside_of_mem (p := (splOf m S + BitVec.ofNat 64 ((v.toNat - 2) / 2), 1)) (List.mem_filterMap.mpr ⟨d, List.mem_range.mpr hd, by simp [hv, h2, he]⟩)
    (Mem.Blocks.Inside.base (Nat.le_refl 1))

-- The address of the spilled byte that `is_spilled` reads.
theorem spl_addr {m : Mem 64} {S v : Addr} (h2 : 2 ≤ v.toNat) :
    BitVec.ofInt 64 (m.loadInt (S + BitVec.ofInt 64 (Int64.toInt 40)) 8).get!
        + (v - 2#64).ushiftRight (((1#64).take 8).toNat &&& 63) + BitVec.ofInt 64 (Int64.toInt 0)
      = splOf m S + BitVec.ofNat 64 ((v.toNat - 2) / 2) := by
  have h40 : BitVec.ofInt 64 (Int64.toInt 40) = BitVec.ofNat 64 (8 * 5) := by decide
  have h0 : BitVec.ofInt 64 (Int64.toInt 0) = 0#64 := by decide
  rw [sub_two_shr h2, h40, h0, BitVec.add_zero]
  rfl

theorem isSpilled_body [Host] [FunDecls] : Body isSpilledAsm isSpilledF isSpilledA isSpilledR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "is_spilled", t => t = s.pushRa ra
      | .label ".LB1", t => Done s ra (BitVec.ofNat 64 (isSpilled (env s) (rsi s)).toNat) t
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.right t ht =>
    kvcgen64
    · simp [ht.retAddr]
    · exact Done.ret (R := isSpilledR) hpre ht fun t' hm hax => ⟨hax, by
        rw [st', hm]; exact (pushRa_keeps hpre).2.2.1⟩
  case right.left t ht =>
    subst ht
    obtain ⟨hw, -, -, henv⟩ := pushRa_keeps (ra := ra) hpre
    obtain ⟨d, hd, hv⟩ := hpre.2.2
    rw [← henv] at hd hv
    simp only [Env.n, envOf, List.length_map, List.length_range] at hd
    replace hv : rd (s.pushRa ra).dmem (wordAt (tgtOf (s.pushRa ra).dmem (rdi s)) d) = rsi s := by
      have hd' := hd
      simp only [Reg64s.get64_rdi] at hd'
      rw [← hv]; simp [envOf, hd']
    kvcgen64
    all_goals simp only [pushRa_rbx, pushRa_rcx, pushRa_rdx, pushRa_rsi, pushRa_rdi,
      pushRa_rbp, pushRa_r8, pushRa_r9, pushRa_r10, pushRa_r11, pushRa_r12, pushRa_r13, pushRa_r14,
      pushRa_r15] at *
    case vc1 hbe _ =>
      have h1 : s.regs.rsi.toNat < 2 := of_decide_eq_true ((be_sub_one _ _ _).symm.trans hbe)
      cfg_goto
      · exact stack_pushRa rfl
      · refine Done.intro rfl rfl ?_ rfl rfl rfl rfl rfl rfl
        simp [isSpilled, show ¬ 2 ≤ s.regs.rsi.toNat by omega]
      · simp
    case vc2 _ _ hnz _ =>
      have h1 : s.regs.rsi.toNat % 2 = 1 := of_decide_eq_true ((nz_and_one _ _).symm.trans hnz)
      cfg_goto
      · exact stack_pushRa rfl
      · refine Done.intro rfl rfl ?_ rfl rfl rfl rfl rfl rfl
        simp [isSpilled, h1]
      · simp
    case vc3 => decide
    case vc4 =>
      exact hw.load_readable (inside_hdr (k := 5) (by decide) (by decide))
    case vc5 hbe _ hnz _ _ _ _ =>
      have h2 : 2 ≤ (rsi s).toNat := Nat.not_lt.mp (of_decide_eq_false ((be_sub_one _ _ _).symm.trans hbe))
      have he : (rsi s).toNat % 2 = 0 := by
        have : ¬ (rsi s).toNat % 2 = 1 := of_decide_eq_false ((nz_and_one _ _).symm.trans hnz)
        omega
      have h := hw.load_readable (inside_splBlocks hd hv h2 he).tail.tail
      rw [← spl_addr h2] at h
      exact h
    case vc6 hbe _ hnz _ _ _ _ =>
      have h2 : 2 ≤ (rsi s).toNat := Nat.not_lt.mp (of_decide_eq_false ((be_sub_one _ _ _).symm.trans hbe))
      have he : (rsi s).toNat % 2 = 0 := by
        have : ¬ (rsi s).toNat % 2 = 1 := of_decide_eq_false ((nz_and_one _ _).symm.trans hnz)
        omega
      refine Done.intro rfl rfl ?_ rfl rfl rfl rfl rfl rfl
      rw [← henv, isSpilled_envOf hd hv h2 he, rdb, ← spl_addr h2]
      exact setne_zero _ _ _ _
    case vc7 => simp

end Bbu
