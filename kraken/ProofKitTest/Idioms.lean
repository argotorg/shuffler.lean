import ProofKit.Idioms
import BbuKraken.Specs
import Kraken.X64.Parser

open Std.WP Lean.Order
open scoped Program.WP
set_option experimental.vcgen true

namespace Program.WP
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All, ite_true])

/-- `notq %r` -/
@[spec] theorem not_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (~~~ s.regs.get64 r) } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    run_step
    exact hn _ hq⟩
@[spec] theorem cmov_load_spec' (cc : CondCode) (rd b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 rd (if cc.interp s.status
            then BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get! else s.regs.get64 rd) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmovcc cc (.low rd .W64) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.setReg, Reg64s.set_low_W64, Reg64s.get_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)
end Program.WP

/-! # Tests: each lemma on the VC that `kvcgen64` gives for the asm pattern.

Each test program is a copy of an instruction sequence from the g++ -O1 build of the C++ port (`c/build_bottom_up.cpp`, variant F).
`step1_of_wp` makes the jump branch `⊥`, so each jump test has a precondition that makes
the jump impossible; the proof must use the lemma on the hypothesis to get the contradiction. -/

open Idioms

/-- `cmpq $15, %rax; ja` (swapWith:317, buildBottomUp:494). -/
def tJa := parse("
    cmpq $15, %rax
    ja foo
")
theorem tJa_ok [Host] (hp : tJa.IsInfix Host.prog) (s : MachineData)
    (h : s.regs.rax.toBitVec.toNat ≤ 15) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rax.toBitVec.toNat ≤ 15) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tJa]
  · rename_i hj
    rw [MachineData.status_mk, cmp_a_imm (w := 64) _ 15 (by decide)] at hj
    exact absurd (of_decide_eq_true hj) (by omega)
  · rename_i hj
    rw [MachineData.status_mk, cmp_a_imm (w := 64) _ 15 (by decide)] at hj
    exact Nat.le_of_not_lt (of_decide_eq_false hj)

/-- `cmpq $15, %rax; jbe` (produce:154, generate:394). -/
def tJbe := parse("
    cmpq $15, %rax
    jbe foo
")
theorem tJbe_ok [Host] (hp : tJbe.IsInfix Host.prog) (s : MachineData)
    (h : 15 < s.regs.rax.toBitVec.toNat) :
    Eventually (step1 Host.exe) (fun t => 15 < t.data.regs.rax.toBitVec.toNat) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tJbe]
  · rename_i hj
    rw [MachineData.status_mk, cmp_be_imm (w := 64) _ 15 (by decide)] at hj
    exact absurd (of_decide_eq_true hj) (by omega)
  · rename_i hj
    rw [MachineData.status_mk, cmp_be_imm (w := 64) _ 15 (by decide)] at hj
    exact Nat.lt_of_not_le (of_decide_eq_false hj)

/-- `cmpq %rsi, %rdx; jnb` (swapWith:308) and `cmpq %r13, %r15; jb` (buildBottomUp:529). -/
def tJnb := parse("
    cmpq %rsi, %rdx
    jnb foo
    cmpq %r13, %r15
    jb bar
")
theorem tJnb_ok [Host] (hp : tJnb.IsInfix Host.prog) (s : MachineData)
    (h1 : s.regs.rdx.toBitVec.toNat < s.regs.rsi.toBitVec.toNat)
    (h2 : s.regs.r13.toBitVec.toNat ≤ s.regs.r15.toBitVec.toNat) :
    Eventually (step1 Host.exe) (fun _ => True) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tJnb]
  · rename_i hj
    rw [MachineData.status_mk, cmp_nc] at hj
    exact absurd (of_decide_eq_true hj) (by omega)
  · rename_i hj
    rw [MachineData.status_mk, cmp_c] at hj
    exact absurd (of_decide_eq_true hj) (by omega)

/-- `cmpq $-1, %rax; je` (produce:150) and `cmpb $1, %dl; je` (produce:147). -/
def tJe := parse("
    cmpq $-1, %rax
    je foo
    cmpb $1, %dl
    je bar
")
theorem tJe_ok [Host] (hp : tJe.IsInfix Host.prog) (s : MachineData)
    (h1 : s.regs.rax.toBitVec ≠ -1#64) (h2 : s.regs.rdx.toBitVec.take 8 ≠ 1#8) :
    Eventually (step1 Host.exe) (fun _ => True) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tJe]
  · rename_i hj
    rw [MachineData.status_mk, cmp_z, beq_iff_eq] at hj
    exact absurd hj (by simpa using h1)
  · rename_i hj
    rw [MachineData.status_mk, cmp_z, beq_iff_eq] at hj
    exact absurd hj h2

/-- `testq %rax, %rax; js; leaq; movl; jle` (permuteDest:242-246): flags kept across lea. -/
def tJs := parse("
    testq %rax, %rax
    js foo
    leaq 16(%rsp), %rcx
    jle bar
")
theorem tJs_ok [Host] (hp : tJs.IsInfix Host.prog) (s : MachineData)
    (h : 0 < s.regs.rax.toBitVec.toInt) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rcx.toBitVec = s.regs.rsp.toBitVec + 16#64)
      ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tJs]
  · rename_i _ hj
    rw [MachineData.status_mk, test_s, BitVec.msb_eq_toInt] at hj
    exact absurd (of_decide_eq_true hj) (by omega)
  · rename_i _ _ hj
    rw [MachineData.status_mk, test_le] at hj
    exact absurd (of_decide_eq_true hj) (by omega)
  · rw [ofInt_toInt64]; rfl

/-- `testq %rdi, %rdi; je` (shallowestCopy:29, build_bottom_up:725). -/
def tTz := parse("
    testq %rdi, %rdi
    je foo
")
theorem tTz_ok [Host] (hp : tTz.IsInfix Host.prog) (s : MachineData) (h : s.regs.rdi.toBitVec ≠ 0#64) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rdi.toBitVec ≠ 0#64) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tTz]
  · rename_i _ hj
    rw [MachineData.status_mk, test_z, beq_iff_eq] at hj
    exact absurd hj h
  · exact h

/-- Slot pack: `movzbl %cl,%ecx; salq $40,%rcx; movabsq $~(0xFF<<40),%rax; andq; orq`
(buildBottomUp:475-479), and the `<<32` form (buildBottomUp:466-470). -/
def tPack := parse("
    movzbl %dl, %eax
    salq $32, %rax
    movabsq $-1095216660481, %rsi
    andq %rsi, %rbp
    orq %rax, %rbp
    movzbl %cl, %ecx
    salq $40, %rcx
    movabsq $-280375465082881, %rax
    andq %rax, %rbp
    orq %rcx, %rbp
")
theorem tPack_ok [Host] (hp : tPack.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun t =>
      t.data.regs.rbp.toBitVec.extractLsb' 0 32 = s.regs.rbp.toBitVec.extractLsb' 0 32 ∧
      t.data.regs.rbp.toBitVec.extractLsb' 32 8 = s.regs.rdx.toBitVec.take 8 ∧
      t.data.regs.rbp.toBitVec.extractLsb' 40 8 = s.regs.rcx.toBitVec.take 8) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tPack]
  all_goals first
    | decide
    | (rw [shiftLeft_imm, shiftLeft_imm]
       simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, pack40_payload, pack40_kind,
         pack40_op, pack32_payload, pack32_kind])

/-- Slot compare: `xorq (%rcx,%rax,8),%rdi; salq $16,%rdi; jne` (buildBottomUp:536, 648). -/
def tSlotEq := parse("
    xorq (%rcx,%rax,8), %rdi
    salq $16, %rdi
    jne foo
")
theorem tSlotEq_ok [Host] (hp : tSlotEq.IsInfix Host.prog) (s : MachineData)
    (hm : (Mem.loadInt s.dmem (s.regs.get64 Reg64.rcx + s.regs.get64 Reg64.rax * 8#64 +
      BitVec.ofInt 64 (Int64.toInt 0)) 8).isSome = true)
    (h : s.regs.rdi.toBitVec.extractLsb' 0 48 = (BitVec.ofInt 64 (Mem.loadInt s.dmem
      (s.regs.rcx.toBitVec + s.regs.rax.toBitVec * 8#64 + BitVec.ofInt 64 (Int64.toInt 0)) 8).get!).extractLsb' 0 48) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rdi.toBitVec = 0#64) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tSlotEq]
  · exact hm
  · decide
  · rename_i _ _ _ _ hj
    rw [MachineData.status_mk, slot_nz _ _ _ (by decide)] at hj
    simp only [bne_iff_ne, ne_eq] at hj
    exact absurd h hj
  · rw [shiftLeft_imm, show (16#64).toNat % 64 = 16 from rfl]
    exact (slot_eq_iff _ _).2 ((extract48_eq_iff _ _).1 h)

/-- `leaq (%rcx,%rcx,2),%rcx; salq $2,%rcx` (push:61) and `notq; addq` (swapWith:332). -/
def tLea := parse("
    leaq (%rcx,%rcx,2), %rcx
    salq $2, %rcx
    movq %rdx, %rsi
    notq %rsi
    addq %rax, %rsi
")
theorem tLea_ok [Host] (hp : tLea.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rcx.toBitVec = s.regs.rcx.toBitVec * 12#64 ∧
      t.data.regs.rsi.toBitVec = s.regs.rax.toBitVec - 1#64 - s.regs.rdx.toBitVec) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tLea]
  · decide
  · rw [shiftLeft_imm, lea_disp0]
    exact lea3_shl2 _
  · exact add_not _ _

/-- `cmpq $-1, %rax; cmove %rbx, %rax` (buildBottomUp:503). -/
def tCmove := parse("
    cmpq $-1, %rax
    cmove %rbx, %rax
")
theorem tCmove_ok [Host] (hp : tCmove.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rax.toBitVec =
      if s.regs.rax.toBitVec = -1#64 then s.regs.rbx.toBitVec else s.regs.rax.toBitVec) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tCmove]
  rw [cmove_sub]
  rfl

/-- `cmpq %r13,%r15; setb %cl; cmpq %r15,%r14; setb %dl; testb %dl,%cl; je` (buildBottomUp:516-521). -/
def tSetb := parse("
    cmpq %r13, %r15
    setb %cl
    cmpq %r15, %r14
    setb %dl
    testb %dl, %cl
    je foo
")
theorem tSetb_ok [Host] (hp : tSetb.IsInfix Host.prog) (s : MachineData)
    (h : s.regs.r15.toBitVec.toNat < s.regs.r13.toBitVec.toNat ∧
      s.regs.r14.toBitVec.toNat < s.regs.r15.toBitVec.toNat) :
    Eventually (step1 Host.exe) (fun _ => True) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tSetb]
  rename_i _ hj
  rw [MachineData.status_mk, setcc_test_z, cmp_c, cmp_c] at hj
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hj
  omega

/-- `cmpq %r14,%rax; sete %al; cmpq $15,%rdx; setne %dl; orb %dl,%al; jne` (buildBottomUp:494-500). -/
def tOrb := parse("
    cmpq %r14, %rax
    sete %al
    cmpq $15, %rdx
    setne %dl
    orb %dl, %al
    jne foo
")
theorem tOrb_ok [Host] (hp : tOrb.IsInfix Host.prog) (s : MachineData)
    (h : s.regs.rax.toBitVec ≠ s.regs.r14.toBitVec ∧ s.regs.rdx.toBitVec = 15#64) :
    Eventually (step1 Host.exe) (fun _ => True) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tOrb]
  rename_i _ hj
  rw [MachineData.status_mk, setcc_or_nz, cmp_z, cmp_nz] at hj
  simp [h.1, h.2] at hj

/-- `cmpq %r13, 32(%r12); setne %al; addl %eax, %eax` (buildBottomUp:703-705): Status 0 or 2. -/
def tStat := parse("
    cmpq %r13, %rcx
    setne %al
    addl %eax, %eax
")
theorem tStat_ok [Host] (hp : tStat.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rax.toBitVec.take 8 =
      if s.regs.rcx.toBitVec = s.regs.r13.toBitVec then 0#8 else 2#8) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tStat]
  rw [status_0_2, cmp_nz]
  by_cases h : s.regs.rcx.toBitVec = s.regs.r13.toBitVec <;> simp [h]

/-- Slot unpack: `movq %rsi,%rdx; shrq $32,%rdx; testb %dl,%dl; jne` (isSpilled:5-10). -/
def tUnpack := parse("
    movq %rsi, %rdx
    shrq $32, %rdx
    testb %dl, %dl
    jne foo
")
theorem tUnpack_ok [Host] (hp : tUnpack.IsInfix Host.prog) (s : MachineData)
    (h : s.regs.rsi.toBitVec.extractLsb' 32 8 = 0#8) :
    Eventually (step1 Host.exe) (fun _ => True) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tUnpack]
  · decide
  · rename_i _ hj
    rw [MachineData.status_mk, test_nz, ushiftRight_imm, take_ushiftRight,
      show (32#64).toNat % 64 = 32 from rfl, h] at hj
    exact absurd hj (by decide)

/-- The `ShuffleOp` kind (push:63-69). -/
def tKind := parse("
    testb %r8b, %r8b
    setne %sil
    testb %r9b, %r9b
    sete %r10b
    andl %r10d, %esi
    addl $3, %esi
")
theorem tKind_ok [Host] (hp : tKind.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rsi.toBitVec.take 8 =
      if s.regs.r8.toBitVec.take 8 ≠ 0#8 ∧ s.regs.r9.toBitVec.take 8 = 0#8 then 4#8 else 3#8)
      ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tKind]
  rw [kind_sel, test_nz, test_z]
  by_cases h1 : s.regs.r8.toBitVec.take 8 = 0#8 <;>
    by_cases h2 : s.regs.r9.toBitVec.take 8 = 0#8 <;> simp [h1, h2]

/-- `cmpb $2,%al; movq $-2,%rax; cmovne 48(%rsp),%rax` (build_bottom_up:781-784). -/
def tRet := parse("
    cmpb $2, %al
    movq $-2, %rax
    cmovne 48(%rsp), %rax
")
theorem tRet_ok [Host] (hp : tRet.IsInfix Host.prog) (s : MachineData)
    (hm : ∀ a, (Mem.loadInt s.dmem a 8).isSome = true) :
    Eventually (step1 Host.exe) (fun t => s.regs.rax.toBitVec.take 8 = 2#8 →
      t.data.regs.rax.toBitVec = 18446744073709551614#64) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tRet]
  · exact hm _
  · rename_i h
    rw [cmovne_sub, ite_eq_left h]
    rfl

/-- Status constants and moves: `movl $2,%edx; movl %edx,%eax` (push:75,84),
`leaq -1(%rsi),%r8` (permuteDest:250), `movl %esi,%esi` (isSpilled:15). -/
def tStat2 := parse("
    movl $2, %edx
    leaq -1(%rsi), %r8
    movl %edx, %eax
    movl %esi, %esi
")
theorem tStat2_ok [Host] (hp : tStat2.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rax.toBitVec = 2#64 ∧
      t.data.regs.r8.toBitVec = s.regs.rsi.toBitVec - 1#64 ∧
      t.data.regs.rsi.toBitVec.toNat = s.regs.rsi.toBitVec.toNat % 2 ^ 32) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tStat2]
  · rw [movl_imm]
  · rw [ofInt_toInt64, BitVec.sub_eq_add_neg]; rfl
  · exact movl_toNat _

/-- The `idioms` simp set on a jump VC (the `tJa` program). -/
theorem tMacro_ok [Host] (hp : tJa.IsInfix Host.prog) (s : MachineData)
    (h : s.regs.rax.toBitVec.toNat ≤ 15) :
    Eventually (step1 Host.exe) (fun _ => True) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tJa]
  rename_i hj
  idioms at hj
  bv_omega

/-- `addq 32(%rbx), %rdx; je` (produce:208), with a register source. -/
def tAdd := parse("
    addq %rcx, %rdx
    je foo
")
theorem tAdd_ok [Host] (hp : tAdd.IsInfix Host.prog) (s : MachineData)
    (h : s.regs.rdx.toBitVec + s.regs.rcx.toBitVec ≠ 0#64) :
    Eventually (step1 Host.exe) (fun _ => True) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tAdd]
  rename_i _ hj
  rw [MachineData.status_mk, z_result, beq_iff_eq] at hj
  exact absurd (by rw [BitVec.add_comm]; exact hj) h

/-- `cmpb $0, (%rax,%rsi); setne %al; ret` (isSpilled:17-18), with a register operand. -/
def tSet := parse("
    cmpq %rsi, %rdi
    setne %al
")
theorem tSet_ok [Host] (hp : tSet.IsInfix Host.prog) (s : MachineData) :
    Eventually (step1 Host.exe) (fun t => t.data.regs.rax.toBitVec.take 8 =
      if s.regs.rdi.toBitVec = s.regs.rsi.toBitVec then 0#8 else 1#8) ⟨s, startAddr hp⟩ := by
  apply Program.WP.step1_of_wp hp
  kvcgen64 [tSet]
  try rw [BitVec.take_replaceLow_8]
  rw [cmp_nz]
  by_cases h : s.regs.rdi.toBitVec = s.regs.rsi.toBitVec
  · simp [h]
  · rw [ite_eq_right h, bne_iff_ne.mpr h]; rfl
#print axioms tJa_ok
#print axioms tJbe_ok
#print axioms tJnb_ok
#print axioms tJe_ok
#print axioms tJs_ok
#print axioms tTz_ok
#print axioms tPack_ok
#print axioms tSlotEq_ok
#print axioms tLea_ok
#print axioms tCmove_ok
#print axioms tSetb_ok
#print axioms tOrb_ok
#print axioms tStat_ok
#print axioms tUnpack_ok
#print axioms tKind_ok
#print axioms tRet_ok
#print axioms tStat2_ok
#print axioms tMacro_ok
#print axioms tAdd_ok
#print axioms tSet_ok
