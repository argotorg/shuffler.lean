module

public import BbuKraken.Kit
import all BbuKraken.Kit
public import BbuKraken.Names
import all BbuKraken.Names
public import ProofKit.Cfg
import all ProofKit.Cfg

@[expose] public section

open Std.WP Lean.Order ProofKit
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
        status := t.status, dmem := t.dmem } :=
  Kit.Fm.ret (rs := []) (by decide) hpre
    ⟨h.1 ▸ Kit.Mid.init (by decide) hpre, h.1 ▸ Kit.wf_pushRa (by decide) hpre, nofun⟩
    h.2.1 h.2.2.2 fun t' hm hax => hR t' (hm.trans h.1) (hax.trans h.2.2.1)

end Leaf

/-! ## Flags and addresses -/

-- `setne %al` writes only `al`.
theorem setWidth_replaceLow (x : Word) (v : BitVec 8) : BitVec.setWidth 8 (x.replaceLow v) = v := by
  conv => rhs; rw [← BitVec.take_replaceLow_8 x v]
  ext i hi
  simp [BitVec.take]

-- `cmpb $0, b; setne %al` gives `b != 0` in `al`.
theorem setne_zero (x : Word) (b : BitVec 8) (cf af of : Bool) :
    BitVec.setWidth 8 (x.replaceLow (BitVec.ofNat 8
      (CondCode.nz.interp (StatusFlags.from_result (b - 0#8) { cf, af, of })).toNat))
      = BitVec.ofNat 8 (b != 0#8).toNat := by
  rw [setWidth_replaceLow]
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.sub_zero, BitVec.zero_eq, bne]

theorem Wf.load_readable {m : Mem 64} {S x : Addr} {n : Nat} (hw : Wf m S)
    (h : Mem.Blocks.Inside x n (readable m S)) : (m.loadInt x n).isSome = true :=
  hw.mapped.loadInt_isSome (inside_append.mpr (Or.inr h))

/-! ## `isSpilled` -/

-- `shrq $32; testb %dl, %dl; jne` jumps iff the kind (byte 4) is not 0.
theorem nz_kind (w : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result
      ((w.ushiftRight (((32#64).take 8).toNat &&& 63)).take 8
        &&& (w.ushiftRight (((32#64).take 8).toNat &&& 63)).take 8) r)
      = ((StackSlot.ofWord w).kind != 0#8) := by
  have : (w.ushiftRight (((32#64).take 8).toNat &&& 63)).take 8 = (StackSlot.ofWord w).kind := by
    rw [ushiftRight_imm]; ext i hi; simp [StackSlot.ofWord, BitVec.take]
  rw [this]; simp [CondCode.interp, StatusFlags.from_result, bne]

-- `shrq $40; testb %dl, %dl; je` jumps iff the opcode (byte 5) is 0.
theorem z_opcode (w : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result
      ((w.ushiftRight (((40#64).take 8).toNat &&& 63)).take 8
        &&& (w.ushiftRight (((40#64).take 8).toNat &&& 63)).take 8) r)
      = ((StackSlot.ofWord w).valueOpcode == 0#8) := by
  have : (w.ushiftRight (((40#64).take 8).toNat &&& 63)).take 8 = (StackSlot.ofWord w).valueOpcode := by
    rw [ushiftRight_imm]; ext i hi; simp [StackSlot.ofWord, BitVec.take]
  rw [this]; simp [CondCode.interp, StatusFlags.from_result]

-- `movl %esi, %esi` gives the payload.
theorem payload_take (w : Word) :
    BitVec.setWidth 64 (w.take 32) = BitVec.ofNat 64 (StackSlot.ofWord w).payload.toNat := by
  rw [BitVec.ofNat_toNat]
  ext i hi
  simp [StackSlot.ofWord, BitVec.take]

-- The spilled byte of a target variable is in `splBlocks`.
theorem inside_splBlocks {m : Mem 64} {S : Addr} {d i : Nat} (hd : d < nOf m S)
    (hi : spillId (tgtSlot m S d) = some i) :
    Mem.Blocks.Inside (splOf m S + BitVec.ofNat 64 i) 1 (splBlocks m S) :=
  inside_of_mem (p := (splOf m S + BitVec.ofNat 64 i, 1))
    (List.mem_filterMap.mpr ⟨d, List.mem_range.mpr hd, by simp [hi]⟩)
    (Mem.Blocks.Inside.base (Nat.le_refl 1))

-- A target slot that is a variable selects its spilled byte.
theorem isSpilled_envOf {m : Mem 64} {S : Addr} {d : Nat} (hd : d < nOf m S)
    (hk : (tgtSlot m S d).kind = Value) (ho : (tgtSlot m S d).valueOpcode ≠ Const) :
    isSpilled (envOf m S) (tgtSlot m S d)
      = (rdb m (splOf m S + BitVec.ofNat 64 (tgtSlot m S d).payload.toNat) != 0#8) := by
  have ht : tgtVar m S (tgtSlot m S d).payload.toNat = true :=
    List.any_eq_true.mpr ⟨d, List.mem_range.mpr hd, by simp [spillId, hk, ho]⟩
  simp [isSpilled, isLiteralValue, envOf, ht, hk, bne]
  rw [beq_eq_false_iff_ne.mpr ho]
  simp only [Bool.not_false, Bool.true_and]
  congr 1

-- The address of the spilled byte that `isSpilled` reads.
theorem spl_addr {m : Mem 64} {S : Addr} {w : Word} :
    BitVec.ofInt 64 (m.loadInt (S + BitVec.ofInt 64 (Int64.toInt 16)) 8).get!
        + BitVec.setWidth 64 (w.take 32) + BitVec.ofInt 64 (Int64.toInt 0)
      = splOf m S + BitVec.ofNat 64 (StackSlot.ofWord w).payload.toNat := by
  have h40 : BitVec.ofInt 64 (Int64.toInt 16) = BitVec.ofNat 64 (8 * 2) := by decide
  have h0 : BitVec.ofInt 64 (Int64.toInt 0) = 0#64 := by decide
  rw [payload_take, h40, h0, BitVec.add_zero]
  rfl

-- Both jumps fall through: the slot is a variable.
theorem var_of_flags {w : Word} {r r' : StatusFlags.from_result.Remaining}
    (hnz : CondCode.nz.interp (StatusFlags.from_result
      ((w.ushiftRight (((32#64).take 8).toNat &&& 63)).take 8
        &&& (w.ushiftRight (((32#64).take 8).toNat &&& 63)).take 8) r) = false)
    (hz : CondCode.z.interp (StatusFlags.from_result
      ((w.ushiftRight (((40#64).take 8).toNat &&& 63)).take 8
        &&& (w.ushiftRight (((40#64).take 8).toNat &&& 63)).take 8) r') = false) :
    (StackSlot.ofWord w).kind = Value ∧ (StackSlot.ofWord w).valueOpcode ≠ Const := by
  rw [nz_kind] at hnz
  rw [z_opcode] at hz
  simpa [Value, Const, bne] using And.intro hnz hz

-- The state at `.LB.Emission.isSpilled.0`: `al` holds the result. The C++ build has no `movzbl`, so the
-- upper bytes of `rax` are not fixed.
def SpillDone (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ r : Word, Done s ra r t ∧ r.setWidth 8 = BitVec.ofNat 8 (isSpilled (env s) (slot s)).toNat

theorem isSpilled_body [Host] [FunDecls] : Body isSpilledAsm isSpilledF isSpilledA isSpilledR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.isSpilled then t = s.pushRa ra
        else if l = ".LB.Emission.isSpilled.0" then SpillDone s ra t
        else False
      | .exit, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
    all_goals simp only [Names.isSpilled, ↓reduceIte]
  case right.right t ht =>
    simp only [Names.isSpilled, ↓reduceIte, String.reduceEq] at ht
    obtain ⟨r, hd, hr⟩ := ht
    kvcgen64
    · simp [hd.retAddr]
    · exact Done.ret (R := isSpilledR) hpre hd fun t' hm hax => ⟨by show (rax t').setWidth 8 = _; rw [hax]; exact hr, by
        rw [st', hm]; exact (pushRa_keeps hpre).2.2.1⟩
  case right.left t ht =>
    simp only [Names.isSpilled, ↓reduceIte] at ht
    subst ht
    obtain ⟨hw, -, -, henv⟩ := pushRa_keeps (ra := ra) hpre
    obtain ⟨d, hd, hv⟩ := hpre.2.2
    rw [← henv, n_envOf] at hd
    rw [← henv, target_get hd] at hv
    change tgtSlot _ _ d = slot s at hv
    kvcgen64
    all_goals try simp only [pushRa_rbx, pushRa_rcx, pushRa_rsi, pushRa_rdi,
      pushRa_rbp, pushRa_r8, pushRa_r9, pushRa_r10, pushRa_r11, pushRa_r12, pushRa_r13, pushRa_r14,
      pushRa_r15] at *
    case vc1 => decide
    case vc2 _ _ hnz _ =>
      have hk : (StackSlot.ofWord s.regs.rsi.toBitVec).kind ≠ Value := by
        have := (nz_kind _ _).symm.trans hnz
        simpa [Value, bne] using this
      cfg_goto
      · exact stack_pushRa rfl
      · simp only [Names.isSpilled, ↓reduceIte, String.reduceEq]
        refine ⟨_, Done.intro rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
        simp [isSpilled, beq_eq_false_iff_ne.mpr (show (slot s).kind ≠ Value from hk)]
      · simp
    case vc3 => decide
    case vc4 _ _ _ _ _ _ hz _ =>
      have ho : (StackSlot.ofWord s.regs.rsi.toBitVec).valueOpcode = Const := by
        have := (z_opcode _ _).symm.trans hz
        simpa [Const] using this
      cfg_goto
      · exact stack_pushRa rfl
      · simp only [Names.isSpilled, ↓reduceIte, String.reduceEq]
        refine ⟨_, Done.intro rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
        simp [isSpilled, isLiteralValue, show (slot s).valueOpcode = Const from ho]
      · simp
    case vc5 => exact hw.word_isSome hw.mapped (k := 2) (by decide)
    case vc6 _ _ _ _ hnz _ _ _ _ hz _ =>
      obtain ⟨hk, ho⟩ := var_of_flags (w := s.regs.rsi.toBitVec) hnz hz
      have hi : spillId (tgtSlot (s.pushRa ra).dmem (rdi s) d) = some (slot s).payload.toNat := by
        rw [hv]; simp [spillId, hk, ho]; rfl
      have h := hw.load_readable (inside_splBlocks hd hi).tail.tail.tail
      rw [← spl_addr] at h
      exact h
    case vc7 _ _ _ _ hnz _ _ _ _ hz _ =>
      obtain ⟨hk, ho⟩ := var_of_flags (w := rsi s) hnz hz
      simp only [Names.isSpilled, ↓reduceIte, String.reduceEq]
      refine ⟨_, Done.intro rfl rfl rfl rfl rfl rfl rfl rfl rfl, (setne_zero _ _ _ _ _).trans ?_⟩
      change _ = BitVec.ofNat 8 (isSpilled (envOf s.dmem (s.regs.get64 Reg64.rdi))
        (StackSlot.ofWord (s.regs.get64 Reg64.rsi))).toNat
      rw [← hv, ← henv, isSpilled_envOf hd (hv ▸ hk) (hv ▸ ho), rdb, hv, ← spl_addr]
      rfl
    case vc8 => simp

end Bbu
