import Lift.P1.Command
import Lift.P1.Execution
import Lift.Level2.Code
import Skel.Gen.Derive.Blocks
import Skel.Gen.Generate
import Skel.Test.DeriveRead
import Skel.Gen.Derived.Level2z

/-! The condition and address forms of the reader that audit 2 found missing or wrong (task AF2-E, decision D46): the
signed compare of `Int64`, the signed 64-bit branches (`jl`, `jge`, `jg`, `jle`), the borrows of 16 and 32 bits, the
sign extension `movslq` and the addresses of three or more terms. The module is checked by `lake build
Skel.Test.DeriveReadForms`: each `#eval` throws when a check fails. No `set_option` changes a limit.

* **Small terms.** A raw proposition `fun d : MachineData => p` is read by `readCond`, compiled, and compared with the
  oracle `evalC` (`DeriveRead.lean`) on random start states and on the boundary pairs of `rax`, `rbx`.
* **Blocks.** Synthetic functions (one for each form) are lifted, their blocks derived with `blockTerm`, walked, read
  and compared with the raw terms on random states (`meaning` of `DeriveRead.lean`: 0 differences). -/

open Lean Meta Elab Term Skel.Gen Skel.Gen.Derive DeriveSiteTests DeriveRunTests DeriveWalkTests DeriveReadTests

namespace DeriveReadFormsTests

unsafe def evalPropUnsafe (e : Expr) : MetaM (MachineData → Bool) := do
  evalExpr (MachineData → Bool) (← mkArrow (mkConst ``MachineData) (mkConst ``Bool)) e

/-- The compiled function of a lambda `fun d : MachineData => p`: the truth of the proposition `p`. -/
@[implemented_by evalPropUnsafe] opaque evalProp (e : Expr) : MetaM (MachineData → Bool)

/-- The raw proposition of the body of `fun d : MachineData => p`, as a function of the state. -/
def rawProp (e : Expr) : MetaM (MachineData → Bool) :=
  lambdaTelescope e fun xs b => do evalProp (← mkLambdaFVars xs (← mkDecide b))

/-- The boundary pairs of two registers: equal values, neighbours, and the edges of the signed and the unsigned order. -/
def edges : List UInt64 :=
  [0, 1, 2, 5, 6, 7, 8, 0x7FFF, 0x8000, 0xFFFF, 0x10000, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000,
   0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x8000000000000001, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF]

/-- The start states: each pair of edge values in `rax`, `rbx` (the other registers and the flags random), then random
states. -/
def envs (random : Nat) : List Env :=
  let base := (sample [] 99).1
  let pairs := edges.flatMap fun a => edges.map fun b => ({ base with regs := (base.regs.set! 0 a).set! 1 b } : Env)
  pairs ++ (List.range random).map fun i => (sample [] (1000 + i)).1

/-- The number of states on which the read condition of the proposition `stx` differs from the raw proposition, and the
first of them. -/
def condDiffs (stx : TermElabM Syntax) : TermElabM (Nat × Option String) := do
  let e ← Term.elabTerm (← stx) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let c ← match ← readBody readCond e with
    | .ok c => pure c
    | .error err => throwError "the condition is not read: {repr err}"
  let raw ← rawProp e
  let mut n := 0
  let mut first : Option String := none
  for env in envs 300 do
    if evalC env c != some (raw (mkData env.regs env.flags)) then
      n := n + 1
      if first.isNone then first := some s!"{c.show}: rax {env.regs[0]!}, rbx {env.regs[1]!}"
  pure (n, first)

end DeriveReadFormsTests

open DeriveReadFormsTests

/-! ## `Int64` compares: the signed order -/

#eval show TermElabM Unit from do
  let (n, first) ← condDiffs `(fun d : MachineData => Int64.ofBitVec d.regs.rax.toBitVec ≤ Int64.ofBitVec d.regs.rbx.toBitVec)
  check (n == 0) s!"≤ of Int64 differs from the raw term on {n} states, first {first}"
  let (n, first) ← condDiffs `(fun d : MachineData => Int64.ofBitVec d.regs.rax.toBitVec < Int64.ofBitVec d.regs.rbx.toBitVec)
  check (n == 0) s!"< of Int64 differs from the raw term on {n} states, first {first}"

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readBody readCond (← elabE stx)
  check (isCond (← rc `(fun d : MachineData => Int64.ofBitVec d.regs.rax.toBitVec ≤ Int64.ofBitVec d.regs.rbx.toBitVec))
    (.not (.slt (r .rbx) (r .rax)))) "≤ of Int64 is ¬ (b <s a)"
  check (isCond (← rc `(fun d : MachineData => Int64.ofBitVec d.regs.rax.toBitVec < Int64.ofBitVec d.regs.rbx.toBitVec))
    (.slt (r .rax) (r .rbx))) "< of Int64 is <s"
  -- the unsigned compare of `UInt64` is unchanged
  check (isCond (← rc `(fun d : MachineData => d.regs.rax ≤ d.regs.rbx)) (.ule (r .rax) (r .rbx))) "≤ of UInt64 is ule"
  -- the oracle: `-1` (the bits of 2^64 - 1) is below `0` in the signed order, not in the unsigned order
  let env : Env := ⟨(Array.replicate 16 0).set! 0 0xFFFFFFFFFFFFFFFF, Array.replicate 6 false, #[]⟩
  check (evalC env (.not (.slt (r .rbx) (r .rax))) == some true) "-1 ≤s 0"
  check (evalC env (.ule (r .rax) (r .rbx)) == some false) "2^64 - 1 ≤u 0 is false"

/-! ## The synthetic functions

One function for each form. The sizes of the instructions are 4 bytes (and 0 for a label): the step function of the
lift is built for these sizes, and the tests do not compare the code with a binary. -/

namespace DeriveReadFormsCode

def program : Program := level2Program(r#"
.Lau.sxq:
sxq:
 movslq %edi, %rax
 retq
.Lfunc_end0:
.Lau.sxm:
sxm:
 movslq (%rdi), %rax
 retq
.Lfunc_end1:
.Lau.sxb:
sxb:
 movsbq %dil, %rax
 retq
.Lfunc_end2:
.Lau.sxw:
sxw:
 movswq %di, %rax
 retq
.Lfunc_end3:
.Lau.sxbl:
sxbl:
 movsbl %dil, %eax
 retq
.Lfunc_end4:
.Lau.sxwl:
sxwl:
 movswl %di, %eax
 retq
.Lfunc_end5:
.Lau.lea3:
lea3:
 leaq (%rdi,%rsi), %rax
 movq (%rax,%rdx,8), %rax
 retq
.Lfunc_end6:
.Lau.lea4:
lea4:
 leaq (%rdi,%rsi), %rax
 leaq (%rax,%rdx,4), %rax
 movq 16(%rax,%rcx,8), %rax
 retq
.Lfunc_end7:
.Lau.mat:
mat:
 imulq %rcx, %rsi
 addq %rdx, %rsi
 movq (%rdi,%rsi,8), %rax
 retq
.Lfunc_end8:
.Lau.sub2:
sub2:
 movq %rdi, %rax
 subq %rsi, %rax
 movq (%rax,%rdx,8), %rax
 retq
.Lfunc_end9:
.Lau.st3:
st3:
 leaq (%rdi,%rsi), %rax
 movq %rcx, (%rax,%rdx,8)
 retq
.Lfunc_end10:
.Lau.r8b:
r8b:
 cmpb %bl, %al
 jb .Lt_r8b
 xorl %edx, %edx
 retq
.Lt_r8b:
 movl $1, %edx
 retq
.Lfunc_end11:
.Lau.r8ae:
r8ae:
 cmpb %bl, %al
 jae .Lt_r8ae
 xorl %edx, %edx
 retq
.Lt_r8ae:
 movl $1, %edx
 retq
.Lfunc_end12:
.Lau.r8a:
r8a:
 cmpb %bl, %al
 ja .Lt_r8a
 xorl %edx, %edx
 retq
.Lt_r8a:
 movl $1, %edx
 retq
.Lfunc_end13:
.Lau.r8be:
r8be:
 cmpb %bl, %al
 jbe .Lt_r8be
 xorl %edx, %edx
 retq
.Lt_r8be:
 movl $1, %edx
 retq
.Lfunc_end14:
.Lau.r16b:
r16b:
 cmpw %bx, %ax
 jb .Lt_r16b
 xorl %edx, %edx
 retq
.Lt_r16b:
 movl $1, %edx
 retq
.Lfunc_end15:
.Lau.r16ae:
r16ae:
 cmpw %bx, %ax
 jae .Lt_r16ae
 xorl %edx, %edx
 retq
.Lt_r16ae:
 movl $1, %edx
 retq
.Lfunc_end16:
.Lau.r16a:
r16a:
 cmpw %bx, %ax
 ja .Lt_r16a
 xorl %edx, %edx
 retq
.Lt_r16a:
 movl $1, %edx
 retq
.Lfunc_end17:
.Lau.r16be:
r16be:
 cmpw %bx, %ax
 jbe .Lt_r16be
 xorl %edx, %edx
 retq
.Lt_r16be:
 movl $1, %edx
 retq
.Lfunc_end18:
.Lau.r32b:
r32b:
 cmpl %ebx, %eax
 jb .Lt_r32b
 xorl %edx, %edx
 retq
.Lt_r32b:
 movl $1, %edx
 retq
.Lfunc_end19:
.Lau.r32ae:
r32ae:
 cmpl %ebx, %eax
 jae .Lt_r32ae
 xorl %edx, %edx
 retq
.Lt_r32ae:
 movl $1, %edx
 retq
.Lfunc_end20:
.Lau.r32a:
r32a:
 cmpl %ebx, %eax
 ja .Lt_r32a
 xorl %edx, %edx
 retq
.Lt_r32a:
 movl $1, %edx
 retq
.Lfunc_end21:
.Lau.r32be:
r32be:
 cmpl %ebx, %eax
 jbe .Lt_r32be
 xorl %edx, %edx
 retq
.Lt_r32be:
 movl $1, %edx
 retq
.Lfunc_end22:
.Lau.l8b:
l8b:
 cmpb $7, %al
 jb .Lt_l8b
 xorl %edx, %edx
 retq
.Lt_l8b:
 movl $1, %edx
 retq
.Lfunc_end23:
.Lau.l8ae:
l8ae:
 cmpb $7, %al
 jae .Lt_l8ae
 xorl %edx, %edx
 retq
.Lt_l8ae:
 movl $1, %edx
 retq
.Lfunc_end24:
.Lau.l8a:
l8a:
 cmpb $7, %al
 ja .Lt_l8a
 xorl %edx, %edx
 retq
.Lt_l8a:
 movl $1, %edx
 retq
.Lfunc_end25:
.Lau.l8be:
l8be:
 cmpb $7, %al
 jbe .Lt_l8be
 xorl %edx, %edx
 retq
.Lt_l8be:
 movl $1, %edx
 retq
.Lfunc_end26:
.Lau.l16b:
l16b:
 cmpw $7, %ax
 jb .Lt_l16b
 xorl %edx, %edx
 retq
.Lt_l16b:
 movl $1, %edx
 retq
.Lfunc_end27:
.Lau.l16ae:
l16ae:
 cmpw $7, %ax
 jae .Lt_l16ae
 xorl %edx, %edx
 retq
.Lt_l16ae:
 movl $1, %edx
 retq
.Lfunc_end28:
.Lau.l16a:
l16a:
 cmpw $7, %ax
 ja .Lt_l16a
 xorl %edx, %edx
 retq
.Lt_l16a:
 movl $1, %edx
 retq
.Lfunc_end29:
.Lau.l16be:
l16be:
 cmpw $7, %ax
 jbe .Lt_l16be
 xorl %edx, %edx
 retq
.Lt_l16be:
 movl $1, %edx
 retq
.Lfunc_end30:
.Lau.l32b:
l32b:
 cmpl $7, %eax
 jb .Lt_l32b
 xorl %edx, %edx
 retq
.Lt_l32b:
 movl $1, %edx
 retq
.Lfunc_end31:
.Lau.l32ae:
l32ae:
 cmpl $7, %eax
 jae .Lt_l32ae
 xorl %edx, %edx
 retq
.Lt_l32ae:
 movl $1, %edx
 retq
.Lfunc_end32:
.Lau.l32a:
l32a:
 cmpl $7, %eax
 ja .Lt_l32a
 xorl %edx, %edx
 retq
.Lt_l32a:
 movl $1, %edx
 retq
.Lfunc_end33:
.Lau.l32be:
l32be:
 cmpl $7, %eax
 jbe .Lt_l32be
 xorl %edx, %edx
 retq
.Lt_l32be:
 movl $1, %edx
 retq
.Lfunc_end34:
.Lau.srl:
srl:
 cmpq %rbx, %rax
 jl .Lt_srl
 xorl %edx, %edx
 retq
.Lt_srl:
 movl $1, %edx
 retq
.Lfunc_end35:
.Lau.srge:
srge:
 cmpq %rbx, %rax
 jge .Lt_srge
 xorl %edx, %edx
 retq
.Lt_srge:
 movl $1, %edx
 retq
.Lfunc_end36:
.Lau.srg:
srg:
 cmpq %rbx, %rax
 jg .Lt_srg
 xorl %edx, %edx
 retq
.Lt_srg:
 movl $1, %edx
 retq
.Lfunc_end37:
.Lau.srle:
srle:
 cmpq %rbx, %rax
 jle .Lt_srle
 xorl %edx, %edx
 retq
.Lt_srle:
 movl $1, %edx
 retq
.Lfunc_end38:
.Lau.sll:
sll:
 cmpq $5, %rax
 jl .Lt_sll
 xorl %edx, %edx
 retq
.Lt_sll:
 movl $1, %edx
 retq
.Lfunc_end39:
.Lau.slge:
slge:
 cmpq $5, %rax
 jge .Lt_slge
 xorl %edx, %edx
 retq
.Lt_slge:
 movl $1, %edx
 retq
.Lfunc_end40:
.Lau.slg:
slg:
 cmpq $5, %rax
 jg .Lt_slg
 xorl %edx, %edx
 retq
.Lt_slg:
 movl $1, %edx
 retq
.Lfunc_end41:
.Lau.slle:
slle:
 cmpq $5, %rax
 jle .Lt_slle
 xorl %edx, %edx
 retq
.Lt_slle:
 movl $1, %edx
 retq
.Lfunc_end42:
.Lau.sml:
sml:
 cmpq $-1, %rax
 jl .Lt_sml
 xorl %edx, %edx
 retq
.Lt_sml:
 movl $1, %edx
 retq
.Lfunc_end43:
.Lau.smge:
smge:
 cmpq $-1, %rax
 jge .Lt_smge
 xorl %edx, %edx
 retq
.Lt_smge:
 movl $1, %edx
 retq
.Lfunc_end44:
.Lau.smg:
smg:
 cmpq $-1, %rax
 jg .Lt_smg
 xorl %edx, %edx
 retq
.Lt_smg:
 movl $1, %edx
 retq
.Lfunc_end45:
.Lau.smle:
smle:
 cmpq $-1, %rax
 jle .Lt_smle
 xorl %edx, %edx
 retq
.Lt_smle:
 movl $1, %edx
 retq
.Lfunc_end46:
.Lau.snl:
snl:
 cmpq $-9223372036854775808, %rax
 jl .Lt_snl
 xorl %edx, %edx
 retq
.Lt_snl:
 movl $1, %edx
 retq
.Lfunc_end47:
.Lau.snge:
snge:
 cmpq $-9223372036854775808, %rax
 jge .Lt_snge
 xorl %edx, %edx
 retq
.Lt_snge:
 movl $1, %edx
 retq
.Lfunc_end48:
.Lau.sng:
sng:
 cmpq $-9223372036854775808, %rax
 jg .Lt_sng
 xorl %edx, %edx
 retq
.Lt_sng:
 movl $1, %edx
 retq
.Lfunc_end49:
.Lau.snle:
snle:
 cmpq $-9223372036854775808, %rax
 jle .Lt_snle
 xorl %edx, %edx
 retq
.Lt_snle:
 movl $1, %edx
 retq
.Lfunc_end50:
.Lau.spl:
spl:
 cmpq $9223372036854775807, %rax
 jl .Lt_spl
 xorl %edx, %edx
 retq
.Lt_spl:
 movl $1, %edx
 retq
.Lfunc_end51:
.Lau.spge:
spge:
 cmpq $9223372036854775807, %rax
 jge .Lt_spge
 xorl %edx, %edx
 retq
.Lt_spge:
 movl $1, %edx
 retq
.Lfunc_end52:
.Lau.spg:
spg:
 cmpq $9223372036854775807, %rax
 jg .Lt_spg
 xorl %edx, %edx
 retq
.Lt_spg:
 movl $1, %edx
 retq
.Lfunc_end53:
.Lau.sple:
sple:
 cmpq $9223372036854775807, %rax
 jle .Lt_sple
 xorl %edx, %edx
 retq
.Lt_sple:
 movl $1, %edx
 retq
.Lfunc_end54:
.Lau.smeml:
smeml:
 cmpq %rbx, (%rdi)
 jl .Lt_smeml
 xorl %edx, %edx
 retq
.Lt_smeml:
 movl $1, %edx
 retq
.Lfunc_end55:
.Lau.smemge:
smemge:
 cmpq %rbx, (%rdi)
 jge .Lt_smemge
 xorl %edx, %edx
 retq
.Lt_smemge:
 movl $1, %edx
 retq
.Lfunc_end56:
.Lau.smemg:
smemg:
 cmpq %rbx, (%rdi)
 jg .Lt_smemg
 xorl %edx, %edx
 retq
.Lt_smemg:
 movl $1, %edx
 retq
.Lfunc_end57:
.Lau.smemle:
smemle:
 cmpq %rbx, (%rdi)
 jle .Lt_smemle
 xorl %edx, %edx
 retq
.Lt_smemle:
 movl $1, %edx
 retq
.Lfunc_end58:
.Lau.ssetl:
ssetl:
 cmpq %rbx, %rax
 setl %dl
 retq
.Lfunc_end59:
.Lau.ssetge:
ssetge:
 cmpq %rbx, %rax
 setge %dl
 retq
.Lfunc_end60:
.Lau.ssetg:
ssetg:
 cmpq %rbx, %rax
 setg %dl
 retq
.Lfunc_end61:
.Lau.ssetle:
ssetle:
 cmpq %rbx, %rax
 setle %dl
 retq
.Lfunc_end62:
.Lau.scmovl:
scmovl:
 cmpq %rbx, %rax
 cmovlq %rbx, %rax
 retq
.Lfunc_end63:
.Lau.scmovge:
scmovge:
 cmpq %rbx, %rax
 cmovgeq %rbx, %rax
 retq
.Lfunc_end64:
.Lau.scmovg:
scmovg:
 cmpq %rbx, %rax
 cmovgq %rbx, %rax
 retq
.Lfunc_end65:
.Lau.scmovle:
scmovle:
 cmpq %rbx, %rax
 cmovleq %rbx, %rax
 retq
.Lfunc_end66:
.Lau.tr8l:
tr8l:
 cmpb %bl, %al
 jl .Lt_tr8l
 xorl %edx, %edx
 retq
.Lt_tr8l:
 movl $1, %edx
 retq
.Lfunc_end67:
.Lau.tr8ge:
tr8ge:
 cmpb %bl, %al
 jge .Lt_tr8ge
 xorl %edx, %edx
 retq
.Lt_tr8ge:
 movl $1, %edx
 retq
.Lfunc_end68:
.Lau.tr8g:
tr8g:
 cmpb %bl, %al
 jg .Lt_tr8g
 xorl %edx, %edx
 retq
.Lt_tr8g:
 movl $1, %edx
 retq
.Lfunc_end69:
.Lau.tr8le:
tr8le:
 cmpb %bl, %al
 jle .Lt_tr8le
 xorl %edx, %edx
 retq
.Lt_tr8le:
 movl $1, %edx
 retq
.Lfunc_end70:
.Lau.tr16l:
tr16l:
 cmpw %bx, %ax
 jl .Lt_tr16l
 xorl %edx, %edx
 retq
.Lt_tr16l:
 movl $1, %edx
 retq
.Lfunc_end71:
.Lau.tr16ge:
tr16ge:
 cmpw %bx, %ax
 jge .Lt_tr16ge
 xorl %edx, %edx
 retq
.Lt_tr16ge:
 movl $1, %edx
 retq
.Lfunc_end72:
.Lau.tr16g:
tr16g:
 cmpw %bx, %ax
 jg .Lt_tr16g
 xorl %edx, %edx
 retq
.Lt_tr16g:
 movl $1, %edx
 retq
.Lfunc_end73:
.Lau.tr16le:
tr16le:
 cmpw %bx, %ax
 jle .Lt_tr16le
 xorl %edx, %edx
 retq
.Lt_tr16le:
 movl $1, %edx
 retq
.Lfunc_end74:
.Lau.tr32l:
tr32l:
 cmpl %ebx, %eax
 jl .Lt_tr32l
 xorl %edx, %edx
 retq
.Lt_tr32l:
 movl $1, %edx
 retq
.Lfunc_end75:
.Lau.tr32ge:
tr32ge:
 cmpl %ebx, %eax
 jge .Lt_tr32ge
 xorl %edx, %edx
 retq
.Lt_tr32ge:
 movl $1, %edx
 retq
.Lfunc_end76:
.Lau.tr32g:
tr32g:
 cmpl %ebx, %eax
 jg .Lt_tr32g
 xorl %edx, %edx
 retq
.Lt_tr32g:
 movl $1, %edx
 retq
.Lfunc_end77:
.Lau.tr32le:
tr32le:
 cmpl %ebx, %eax
 jle .Lt_tr32le
 xorl %edx, %edx
 retq
.Lt_tr32le:
 movl $1, %edx
 retq
.Lfunc_end78:
.Lau.tl8l:
tl8l:
 cmpb $7, %al
 jl .Lt_tl8l
 xorl %edx, %edx
 retq
.Lt_tl8l:
 movl $1, %edx
 retq
.Lfunc_end79:
.Lau.tl8ge:
tl8ge:
 cmpb $7, %al
 jge .Lt_tl8ge
 xorl %edx, %edx
 retq
.Lt_tl8ge:
 movl $1, %edx
 retq
.Lfunc_end80:
.Lau.tl8g:
tl8g:
 cmpb $7, %al
 jg .Lt_tl8g
 xorl %edx, %edx
 retq
.Lt_tl8g:
 movl $1, %edx
 retq
.Lfunc_end81:
.Lau.tl8le:
tl8le:
 cmpb $7, %al
 jle .Lt_tl8le
 xorl %edx, %edx
 retq
.Lt_tl8le:
 movl $1, %edx
 retq
.Lfunc_end82:
.Lau.tl16l:
tl16l:
 cmpw $7, %ax
 jl .Lt_tl16l
 xorl %edx, %edx
 retq
.Lt_tl16l:
 movl $1, %edx
 retq
.Lfunc_end83:
.Lau.tl16ge:
tl16ge:
 cmpw $7, %ax
 jge .Lt_tl16ge
 xorl %edx, %edx
 retq
.Lt_tl16ge:
 movl $1, %edx
 retq
.Lfunc_end84:
.Lau.tl16g:
tl16g:
 cmpw $7, %ax
 jg .Lt_tl16g
 xorl %edx, %edx
 retq
.Lt_tl16g:
 movl $1, %edx
 retq
.Lfunc_end85:
.Lau.tl16le:
tl16le:
 cmpw $7, %ax
 jle .Lt_tl16le
 xorl %edx, %edx
 retq
.Lt_tl16le:
 movl $1, %edx
 retq
.Lfunc_end86:
.Lau.tl32l:
tl32l:
 cmpl $7, %eax
 jl .Lt_tl32l
 xorl %edx, %edx
 retq
.Lt_tl32l:
 movl $1, %edx
 retq
.Lfunc_end87:
.Lau.tl32ge:
tl32ge:
 cmpl $7, %eax
 jge .Lt_tl32ge
 xorl %edx, %edx
 retq
.Lt_tl32ge:
 movl $1, %edx
 retq
.Lfunc_end88:
.Lau.tl32g:
tl32g:
 cmpl $7, %eax
 jg .Lt_tl32g
 xorl %edx, %edx
 retq
.Lt_tl32g:
 movl $1, %edx
 retq
.Lfunc_end89:
.Lau.tl32le:
tl32le:
 cmpl $7, %eax
 jle .Lt_tl32le
 xorl %edx, %edx
 retq
.Lt_tl32le:
 movl $1, %edx
 retq
.Lfunc_end90:
.Lau.bshr:
bshr:
 shrq $32, %rax
 cmpb $2, %al
 jbe .Lt_bshr
 xorl %edx, %edx
 retq
.Lt_bshr:
 movl $1, %edx
 retq
.Lfunc_end91:
.Lau.asbb:
asbb:
 notl %eax
 addl %ebx, %eax
 cmpl $1, %eax
 sbbq $-1, %rdx
 retq
.Lfunc_end92:
"#)

def sizes : List Nat := program.map fun d => match d with | .label _ => 0 | _ => 4

def code : _root_.Executable := ⟨1048576, program.zipWith (fun d n => ⟨d, n⟩) sizes⟩

end DeriveReadFormsCode

#lift_exact DeriveReadFormsCode.code as DeriveReadFormsCode.L1

/-- The functions of the synthetic program. -/
def DeriveReadFormsCode.fns : List String :=
  ["sxq", "sxm", "sxb", "sxw", "sxbl", "sxwl", "lea3", "lea4", "mat", "sub2", "st3",
   "r8b", "r8ae", "r8a", "r8be", "r16b", "r16ae", "r16a", "r16be", "r32b", "r32ae", "r32a", "r32be", "l8b", "l8ae", "l8a", "l8be", "l16b", "l16ae", "l16a", "l16be", "l32b", "l32ae", "l32a", "l32be",
   "srl", "srge", "srg", "srle", "sll", "slge", "slg", "slle", "sml", "smge", "smg", "smle", "snl", "snge", "sng", "snle", "spl", "spge", "spg", "sple", "smeml", "smemge", "smemg", "smemle", "ssetl", "ssetge", "ssetg", "ssetle", "scmovl", "scmovge", "scmovg", "scmovle",
   "tr8l", "tr8ge", "tr8g", "tr8le", "tr16l", "tr16ge", "tr16g", "tr16le", "tr32l", "tr32ge", "tr32g", "tr32le", "tl8l", "tl8ge", "tl8g", "tl8le", "tl16l", "tl16ge", "tl16g", "tl16le", "tl32l", "tl32ge", "tl32g", "tl32le", "bshr", "asbb"]

#derive_blocks DeriveReadFormsCode.derived DeriveReadFormsCode.L1.step DeriveReadFormsCode.code
  ["sxq", "sxm", "sxb", "sxw", "sxbl", "sxwl", "lea3", "lea4", "mat", "sub2", "st3",
   "r8b", "r8ae", "r8a", "r8be", "r16b", "r16ae", "r16a", "r16be", "r32b", "r32ae", "r32a", "r32be", "l8b", "l8ae", "l8a", "l8be", "l16b", "l16ae", "l16a", "l16be", "l32b", "l32ae", "l32a", "l32be",
   "srl", "srge", "srg", "srle", "sll", "slge", "slg", "slle", "sml", "smge", "smg", "smle", "snl", "snge", "sng", "snle", "spl", "spge", "spg", "sple", "smeml", "smemge", "smemg", "smemle", "ssetl", "ssetge", "ssetg", "ssetle", "scmovl", "scmovge", "scmovg", "scmovle"]

-- the functions of L2-READ, in a command of their own (one command for all functions passes the limit of heartbeats)
#derive_blocks DeriveReadFormsCode.derived2 DeriveReadFormsCode.L1.step DeriveReadFormsCode.code
  ["tr8l", "tr8ge", "tr8g", "tr8le", "tr16l", "tr16ge", "tr16g", "tr16le", "tr32l", "tr32ge", "tr32g", "tr32le", "tl8l", "tl8ge", "tl8g", "tl8le", "tl16l", "tl16ge", "tl16g", "tl16le", "tl32l", "tl32ge", "tl32g", "tl32le", "bshr", "asbb"]

namespace DeriveReadFormsTests

/-- The part of the first block of the function `fn`. -/
def partOf (fn : String) : Except String Part := do
  let some parts := DeriveReadFormsCode.derived.lookup fn <|> DeriveReadFormsCode.derived2.lookup fn
    | throw s!"{fn}: no function"
  let some r := parts.lookup 0 | throw s!"{fn}: no block at 0"
  r.mapError fun e => s!"{fn}: {repr e}"

/-- The value of the register `r` in the first block of `fn`. -/
def regOf (fn : String) (r : Reg64) : Except String String := do
  pure (regVal (← partOf fn).regs r).show

/-- The address of the first access of the first block of `fn`. -/
def addrOf (fn : String) (k : Nat) : Except String String := do
  match (← partOf fn).accesses[k]? with
  | some (.load _ a _) | some (.store _ a _ _) => pure a.show
  | none => throw s!"{fn}: no access {k}"

/-- The blocks of the functions `fns`: the walks, the compiled raw terms against the read values on `samples` random
states. The number of blocks read and compiled, the items and the compared values, the blocks not compiled and the
differences. -/
def blockMeaning (fns : List String) (pfx : Name) (samples : Nat) :
    TermElabM (Nat × Nat × Nat × List String × List String) := do
  let bases := fns.map fun fn => (fn, ((labelAddr DeriveReadFormsCode.code fn).getD 0))
  let specs := specsOf DeriveReadFormsCode.code bases
  let ws ← walkAll ``DeriveReadFormsCode.L1.step pfx specs
  meaning bases ws samples

end DeriveReadFormsTests

/-! ## `movslq`, `movsbq`, `movswq`, `movsbl`, `movswl`: the sign extension -/

#eval show TermElabM Unit from do
  let reg (fn : String) (want : String) : TermElabM Unit := do
    match regOf fn .rax with
    | .ok got => check (got == want) s!"{fn}: rax is {got}, expected {want}"
    | .error e => throwError e
  reg "sxq" "(sext32 Reg64.rdi)"
  reg "sxm" "(sext32 load0)"
  reg "sxb" "(sext8 Reg64.rdi)"
  reg "sxw" "(sext16 Reg64.rdi)"
  reg "sxbl" "zext32 (sext8 Reg64.rdi)"
  reg "sxwl" "zext32 (sext16 Reg64.rdi)"

#eval show TermElabM Unit from do
  let fns := ["sxq", "sxm", "sxb", "sxw", "sxbl", "sxwl"]
  let (blocks, nitems, compared, skipped, bad) ← blockMeaning fns `DeriveReadFormsCode.m1 300
  logInfo m!"sign extension: {blocks} blocks, {nitems} items, {compared} values compared, not compiled {skipped}, {bad.length} different {bad.take 3}"
  check (blocks == fns.length && skipped.isEmpty) s!"sign extension: {blocks} blocks read and compiled, not compiled {skipped}"
  check bad.isEmpty s!"sign extension: the raw terms and the read values differ: {bad.take 3}"

/-! ## Addresses of three or more terms -/

#eval show TermElabM Unit from do
  let addr (fn : String) (k : Nat) (want : Val) : TermElabM Unit := do
    match addrOf fn k with
    | .ok got => check (got == want.show) s!"{fn}: the address {k} is {got}, expected {want.show}"
    | .error e => throwError e
  addr "lea3" 0 (.add (.add (r .rdi) (.mul (r .rsi) (n 1))) (.mul (r .rdx) (n 8)))
  addr "lea4" 0 (.add (.add (.add (.add (r .rdi) (.mul (r .rsi) (n 1))) (.mul (r .rdx) (n 4))) (.mul (r .rcx) (n 8))) (n 16))
  addr "sub2" 0 (.add (.add (r .rdi) (.mul (r .rsi) (n 0xFFFFFFFFFFFFFFFF))) (.mul (r .rdx) (n 8)))
  addr "st3" 0 (.add (.add (r .rdi) (.mul (r .rsi) (n 1))) (.mul (r .rdx) (n 8)))

#eval show TermElabM Unit from do
  let fns := ["lea3", "lea4", "mat", "sub2", "st3"]
  let (blocks, nitems, compared, skipped, bad) ← blockMeaning fns `DeriveReadFormsCode.m2 300
  logInfo m!"addresses: {blocks} blocks, {nitems} items, {compared} values compared, not compiled {skipped}, {bad.length} different {bad.take 3}"
  check (blocks == fns.length && skipped.isEmpty) s!"addresses: {blocks} blocks read and compiled, not compiled {skipped}"
  check bad.isEmpty s!"addresses: the raw terms and the read values differ: {bad.take 3}"

/-- The text of the statement of the block of `fn` (the first obligation of `generate`). -/
def DeriveReadFormsTests.statement (fn : String) : Except String String := do
  let tgt : Target := { step := "DeriveReadFormsCode.L1.step", lo := "lo", hi := "hi", entryPC := "pc", imports := [], callees := [] }
  let g ← (generate tgt Hints.none .storeChain DeriveReadFormsCode.code (.derived DeriveReadFormsCode.derived) fn).mapError
    fun e => s!"{fn}: generate: {repr e}"
  let some ob := g.obligations.find? (fun ob => ob.origin matches .block _) | throw s!"{fn}: no block obligation"
  pure ob.statement

#eval show TermElabM Unit from do
  for (fn, want) in [("lea3", "d.regs.rdi.toBitVec + d.regs.rsi.toBitVec * 1 + d.regs.rdx.toBitVec * 8"),
      ("lea4", "d.regs.rdi.toBitVec + d.regs.rsi.toBitVec * 1 + d.regs.rdx.toBitVec * 4 + d.regs.rcx.toBitVec * 8 + 16"),
      ("mat", "d.regs.rdi.toBitVec + d.regs.rdx.toBitVec * 8 + d.regs.rsi.toBitVec * d.regs.rcx.toBitVec * 8"),
      ("sub2", "d.regs.rdi.toBitVec + d.regs.rsi.toBitVec * 18446744073709551615 + d.regs.rdx.toBitVec * 8"),
      ("st3", "d.regs.rdi.toBitVec + d.regs.rsi.toBitVec * 1 + d.regs.rdx.toBitVec * 8")] do
    match DeriveReadFormsTests.statement fn with
    | .ok s => check ((s.splitOn want).length > 1) s!"{fn}: the statement has the address {want}: {s}"
    | .error e => throwError e

/-! ## The borrows of 8, 16 and 32 bits: `cmpb`, `cmpw`, `cmpl` of two registers or of a register and the literal 7, then
`jb`, `jae`, `ja`, `jbe` -/

namespace DeriveReadFormsTests

/-- The functions of the narrow compares: `r` (two registers) or `l` (a literal), the width, the jump. -/
def narrowFns : List String :=
  ["r", "l"].flatMap fun k => [8, 16, 32].flatMap fun w => ["b", "ae", "a", "be"].map fun cc => s!"{k}{w}{cc}"

/-- The compiled raw terms of the blocks of `ws` against the read values on the states `envs` (the edge pairs of `rax`
and `rbx`, then random states); loads are 0. The number of compared values and the differences. -/
def blockEdges (ws : List (Spec × Walk)) (bases : List (String × Nat)) (random : Nat) :
    MetaM (Nat × List String) := do
  let mut compared := 0
  let mut bad : List String := []
  for (s, w) in ws do
    let .ok b := readWalk (baseOf bases s) w | bad := bad ++ [s!"{name s}: not read"]; continue
    let its := rawItems w b
    let some run ← compileRaw w (its.map (·.1)) | bad := bad ++ [s!"{name s}: not compiled"]; continue
    let nloads := (w.accesses.toList.filter fun | .load .. => true | .store .. => false).length
    for env in envs random do
      let env := { env with loads := Array.replicate nloads 0 }
      let got := run env.regs env.flags (Array.replicate nloads 0)
      for ((_, it), i) in its.zipIdx do
        match oracle env it with
        | some x =>
          compared := compared + 1
          if got[i]? != some x then
            bad := bad ++ [s!"{name s} item {i}: raw {got[i]?}, read {x}, rax {env.regs[0]!}, rbx {env.regs[1]!}"]
        | none => pure ()
  pure (compared, bad)

end DeriveReadFormsTests

#eval show TermElabM Unit from do
  let fns := DeriveReadFormsTests.narrowFns
  let (blocks, nitems, compared, skipped, bad) ← blockMeaning fns `DeriveReadFormsCode.m3 300
  logInfo m!"narrow borrows: {blocks} blocks, {nitems} items, {compared} values compared, not compiled {skipped}, {bad.length} different {bad.take 3}"
  check (blocks == 3 * fns.length && skipped.isEmpty) s!"narrow borrows: {blocks} blocks read and compiled, not compiled {skipped}"
  check bad.isEmpty s!"narrow borrows: the raw terms and the read values differ: {bad.take 3}"

#eval show TermElabM Unit from do
  let fns := DeriveReadFormsTests.narrowFns
  let bases := fns.map fun fn => (fn, ((labelAddr DeriveReadFormsCode.code fn).getD 0))
  let ws ← walkAll ``DeriveReadFormsCode.L1.step `DeriveReadFormsCode.m4 (specsOf DeriveReadFormsCode.code bases)
  let (compared, bad) ← DeriveReadFormsTests.blockEdges ws bases 300
  logInfo m!"narrow borrows, edge pairs: {compared} values compared, {bad.length} different {bad.take 3}"
  check bad.isEmpty s!"narrow borrows: the raw terms and the read values differ at the edges: {bad.take 3}"

#eval show TermElabM Unit from do
  -- each narrow jump reads as a condition on the low bits of the registers; `jb` has the fall-through block (offset 8) as
  -- its first target, the others the jump target (offset 16)
  let low (w : Nat) (v : Val) : Val := if w == 8 then .zext .b8 v else if w == 16 then .zext .b16 v else .zext32 v
  for k in ["r", "l"] do
    for w in [8, 16, 32] do
      for cc in ["b", "ae", "a", "be"] do
        let fn := s!"{k}{w}{cc}"
        let a := low w (r .rax)
        let b := if k == "r" then low w (r .rbx) else n 7
        let want : Cond := match cc with
          | "a" => .ult b a
          | "be" => .ule a b
          | _ => .ule b a
        let .ok p := partOf fn | throwError "{fn}: no part"
        match p.term with
        | .branch c (.goto y) (.goto _) =>
          check (c.show == want.show) s!"{fn}: the condition is {c.show}, expected {want.show}"
          check (y == if cc == "b" then 8 else 16) s!"{fn}: the first target is {y}"
        | _ => throwError "{fn}: no branch"

/-! ### The borrow forms on small terms: the read condition against the raw proposition, and the refused forms -/

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readBody readCond (← elabE stx)
  for w in [8, 16, 32] do
    let M := 2 ^ w
    let m := Syntax.mkNumLit (toString M)
    let c := Syntax.mkNumLit (toString (M - 7))
    let low (v : Val) : Val := if w == 8 then .zext .b8 v else if w == 16 then .zext .b16 v else .zext32 v
    -- nocarryn_iff_le: `rbx` is subtracted from `rax`
    let nonlit := `(fun d : MachineData =>
      (((($m - d.regs.rbx.toNat % $m : Nat)) : Int) + (d.regs.rax.toNat : Int)) % $m =
        (d.regs.rax.toNat : Int) % $m - (d.regs.rbx.toNat : Int) % $m)
    check (isCond (← rc nonlit) (.ule (low (r .rbx)) (low (r .rax)))) s!"nocarryn_iff_le, {w} bits"
    let (nd, first) ← condDiffs nonlit
    check (nd == 0) s!"nocarryn_iff_le, {w} bits: differs from the raw term on {nd} states, first {first}"
    -- nocarryn_lit_iff_le: the literal 7 is subtracted from `rax`
    let lit := `(fun d : MachineData => (($c : Int) + (d.regs.rax.toNat : Int)) % $m = (d.regs.rax.toNat : Int) % $m - 7)
    check (isCond (← rc lit) (.ule (n 7) (low (r .rax)))) s!"nocarryn_lit_iff_le, {w} bits"
    let (nd, first) ← condDiffs lit
    check (nd == 0) s!"nocarryn_lit_iff_le, {w} bits: differs from the raw term on {nd} states, first {first}"
    -- refused: the numeral C is not M - K, the modulus of an operand is not M, the operands differ
    let wrongC := Syntax.mkNumLit (toString (M - 6))
    check (isErr (← rc `(fun d : MachineData =>
        (($wrongC : Int) + (d.regs.rax.toNat : Int)) % $m = (d.regs.rax.toNat : Int) % $m - 7))
      (· == .unsupported ``Int)) s!"{w} bits: C + K is not 2^w"
    let wrongM := Syntax.mkNumLit (toString (M * 2))
    check (isErr (← rc `(fun d : MachineData =>
        (((($m - d.regs.rbx.toNat % $m : Nat)) : Int) + (d.regs.rax.toNat : Int)) % $m =
          (d.regs.rax.toNat : Int) % $wrongM - (d.regs.rbx.toNat : Int) % $m))
      (· == .unsupported ``Int)) s!"{w} bits: a modulus that is not 2^w"
    check (isErr (← rc `(fun d : MachineData =>
        (((($m - d.regs.rbx.toNat % $m : Nat)) : Int) + (d.regs.rax.toNat : Int)) % $m =
          (d.regs.rax.toNat : Int) % $m - (d.regs.rcx.toNat : Int) % $m))
      (· == .unsupported ``Int)) s!"{w} bits: the subtrahend is not the same register"
  -- a modulus that is not a width of the table: 2^12
  check (isErr (← rc `(fun d : MachineData => ((4089 : Int) + (d.regs.rax.toNat : Int)) % 4096 = (d.regs.rax.toNat : Int) % 4096 - 7))
    (· == .unsupported ``Int)) "a modulus of 12 bits is refused"

/-! ## The signed 64-bit branches: `cmpq` then `jl`, `jge`, `jg`, `jle` (two registers, the literals 5, -1, -2^63 and
2^63 - 1, a memory operand), `setl`, `cmovl` and the other forms of the flags -/

namespace DeriveReadFormsTests

/-- The functions of the signed compares. -/
def signedFns : List String :=
  (["r", "l", "m", "n", "p"].flatMap fun k => ["l", "ge", "g", "le"].map fun cc => s!"s{k}{cc}") ++
  (["smem", "sset", "scmov"].flatMap fun k => ["l", "ge", "g", "le"].map fun cc => s!"{k}{cc}")

end DeriveReadFormsTests

#eval show TermElabM Unit from do
  let fns := DeriveReadFormsTests.signedFns
  let (blocks, nitems, compared, skipped, bad) ← blockMeaning fns `DeriveReadFormsCode.m5 300
  logInfo m!"signed compares: {blocks} blocks, {nitems} items, {compared} values compared, not compiled {skipped}, {bad.length} different {bad.take 3}"
  check (blocks == 3 * (fns.length - 8) + 8 && skipped.isEmpty) s!"signed compares: {blocks} blocks read and compiled, not compiled {skipped}"
  check bad.isEmpty s!"signed compares: the raw terms and the read values differ: {bad.take 3}"

#eval show TermElabM Unit from do
  let fns := DeriveReadFormsTests.signedFns
  let bases := fns.map fun fn => (fn, ((labelAddr DeriveReadFormsCode.code fn).getD 0))
  let ws ← walkAll ``DeriveReadFormsCode.L1.step `DeriveReadFormsCode.m6 (specsOf DeriveReadFormsCode.code bases)
  let (compared, bad) ← DeriveReadFormsTests.blockEdges ws bases 300
  logInfo m!"signed compares, edge pairs: {compared} values compared, {bad.length} different {bad.take 3}"
  check bad.isEmpty s!"signed compares: the raw terms and the read values differ at the edges: {bad.take 3}"

#eval show TermElabM Unit from do
  -- the first target is the fall-through block (offset 8) for `jl`, the jump target (offset 16) for the others
  let slt (a b : Val) : Cond := .slt a b
  for (k, a, b) in [("r", r .rax, r .rbx), ("l", r .rax, n 5), ("m", r .rax, n 0xFFFFFFFFFFFFFFFF),
      ("n", r .rax, n 0x8000000000000000), ("p", r .rax, n 0x7FFFFFFFFFFFFFFF)] do
    for cc in ["l", "ge", "g", "le"] do
      let fn := s!"s{k}{cc}"
      let want : Cond := match cc with
        | "g" => slt b a
        | "le" => .not (slt b a)
        | _ => .not (slt a b)
      let .ok p := partOf fn | throwError "{fn}: no part"
      match p.term with
      | .branch c (.goto y) (.goto _) =>
        check (c.show == want.show) s!"{fn}: the condition is {c.show}, expected {want.show}"
        check (y == if cc == "l" then 8 else 16) s!"{fn}: the first target is {y}"
      | _ => throwError "{fn}: no branch"
  -- the memory operand: `cmpq %rbx, (%rdi)` compares the load with `rbx`
  for cc in ["l", "ge", "g", "le"] do
    let fn := s!"smem{cc}"
    let want : Cond := match cc with
      | "g" => slt (r .rbx) (.load 0)
      | "le" => .not (slt (r .rbx) (.load 0))
      | _ => .not (slt (.load 0) (r .rbx))
    let .ok p := partOf fn | throwError "{fn}: no part"
    match p.term with
    | .branch c _ _ => check (c.show == want.show) s!"{fn}: the condition is {c.show}, expected {want.show}"
    | _ => throwError "{fn}: no branch"
  -- `cmovg`
  match regOf "scmovg" .rax with
  | .ok got => check (got == "(if (Reg64.rbx <s Reg64.rax) then Reg64.rbx else Reg64.rax)") s!"scmovg: rax is {got}"
  | .error e => throwError e

/-! ### The signed forms on small terms: the read condition against the raw proposition, and the refused forms -/

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readBody readCond (← elabE stx)
  let ok (what : String) (stx : TermElabM Syntax) (want : Cond) : TermElabM Unit := do
    check (isCond (← rc stx) want) s!"{what}"
    let (nd, first) ← condDiffs stx
    check (nd == 0) s!"{what}: differs from the raw term on {nd} states, first {first}"
  -- msb_sub_eq_of_iff_not_slt
  ok "msb = of" `(fun d : MachineData => (d.regs.rax.toBitVec - d.regs.rbx.toBitVec).msb =
      ((d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt).bmod 18446744073709551616 !=
        d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt)) (.not (.slt (r .rax) (r .rbx)))
  -- msb_sub_lit_eq_of_iff_not_slt: a negative literal is `x.toInt + J`, a positive one `x.toInt - K`
  ok "msb = of, the literal -1" `(fun d : MachineData => (d.regs.rax.toBitVec - 18446744073709551615#64).msb =
      ((d.regs.rax.toBitVec.toInt + 1).bmod 18446744073709551616 != d.regs.rax.toBitVec.toInt + 1))
    (.not (.slt (r .rax) (n 0xFFFFFFFFFFFFFFFF)))
  ok "msb = of, the literal 5" `(fun d : MachineData => (d.regs.rax.toBitVec - 5#64).msb =
      ((d.regs.rax.toBitVec.toInt - 5).bmod 18446744073709551616 != d.regs.rax.toBitVec.toInt - 5))
    (.not (.slt (r .rax) (n 5)))
  ok "msb = of, the literal -2^63" `(fun d : MachineData => (d.regs.rax.toBitVec - 9223372036854775808#64).msb =
      ((d.regs.rax.toBitVec.toInt + 9223372036854775808).bmod 18446744073709551616 !=
        d.regs.rax.toBitVec.toInt + 9223372036854775808)) (.not (.slt (r .rax) (n 0x8000000000000000)))
  -- ne_and_msb_sub_eq_of_iff_slt (`jg`), not_msb_sub_eq_of_or_zero_iff_not_slt (`jle`)
  ok "jg" `(fun d : MachineData => ¬ d.regs.rax.toBitVec - d.regs.rbx.toBitVec = 0#64 ∧
      (d.regs.rax.toBitVec - d.regs.rbx.toBitVec).msb =
        ((d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt).bmod 18446744073709551616 !=
          d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt)) (.slt (r .rbx) (r .rax))
  ok "jle" `(fun d : MachineData => ¬ (d.regs.rax.toBitVec - d.regs.rbx.toBitVec).msb =
        ((d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt).bmod 18446744073709551616 !=
          d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt) ∨ d.regs.rax.toBitVec - d.regs.rbx.toBitVec = 0#64)
    (.not (.slt (r .rbx) (r .rax)))
  ok "jg, the literal 5" `(fun d : MachineData => ¬ d.regs.rax.toBitVec - 5#64 = 0#64 ∧
      (d.regs.rax.toBitVec - 5#64).msb =
        ((d.regs.rax.toBitVec.toInt - 5).bmod 18446744073709551616 != d.regs.rax.toBitVec.toInt - 5))
    (.slt (n 5) (r .rax))
  ok "jle, the literal -1" `(fun d : MachineData => ¬ (d.regs.rax.toBitVec - 18446744073709551615#64).msb =
      ((d.regs.rax.toBitVec.toInt + 1).bmod 18446744073709551616 != d.regs.rax.toBitVec.toInt + 1) ∨
        d.regs.rax.toBitVec - 18446744073709551615#64 = 0#64) (.not (.slt (n 0xFFFFFFFFFFFFFFFF) (r .rax)))
  -- refused: the overflow flag of other operands, of another literal, of another modulus; the msb of another width
  let refused (what : String) (stx : TermElabM Syntax) (h : Name) : TermElabM Unit :=
    do check (isErr (← rc stx) (· == .unsupported h)) s!"refused: {what}"
  refused "the overflow of another register" `(fun d : MachineData => (d.regs.rax.toBitVec - d.regs.rbx.toBitVec).msb =
      ((d.regs.rax.toBitVec.toInt - d.regs.rcx.toBitVec.toInt).bmod 18446744073709551616 !=
        d.regs.rax.toBitVec.toInt - d.regs.rcx.toBitVec.toInt)) ``BitVec.msb
  refused "the overflow of another literal" `(fun d : MachineData => (d.regs.rax.toBitVec - 18446744073709551615#64).msb =
      ((d.regs.rax.toBitVec.toInt + 2).bmod 18446744073709551616 != d.regs.rax.toBitVec.toInt + 2)) ``BitVec.msb
  refused "the overflow of a literal with the wrong sign" `(fun d : MachineData => (d.regs.rax.toBitVec - 5#64).msb =
      ((d.regs.rax.toBitVec.toInt + 5).bmod 18446744073709551616 != d.regs.rax.toBitVec.toInt + 5)) ``BitVec.msb
  refused "the overflow modulo 2^32" `(fun d : MachineData => (d.regs.rax.toBitVec - d.regs.rbx.toBitVec).msb =
      ((d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt).bmod 4294967296 !=
        d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt)) ``BitVec.msb
  refused "the sign of another difference" `(fun d : MachineData => (d.regs.rax.toBitVec - d.regs.rcx.toBitVec).msb =
      ((d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt).bmod 18446744073709551616 !=
        d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt)) ``BitVec.msb
  refused "the sign flag alone" `(fun d : MachineData => (d.regs.rax.toBitVec - d.regs.rbx.toBitVec).msb = true) ``BitVec.msb
  refused "jg of two differences" `(fun d : MachineData => ¬ d.regs.rax.toBitVec - d.regs.rcx.toBitVec = 0#64 ∧
      (d.regs.rax.toBitVec - d.regs.rbx.toBitVec).msb =
        ((d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt).bmod 18446744073709551616 !=
          d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt)) ``And
  refused "jle of two differences" `(fun d : MachineData => ¬ (d.regs.rax.toBitVec - d.regs.rbx.toBitVec).msb =
        ((d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt).bmod 18446744073709551616 !=
          d.regs.rax.toBitVec.toInt - d.regs.rbx.toBitVec.toInt) ∨ d.regs.rax.toBitVec - d.regs.rcx.toBitVec = 0#64) ``Or

/-! ## L2-READ: the narrow signed branches, a shifted operand of a borrow, and `notl` in a 32-bit `sbb`

The three reader gaps of `docs/research/l2z-census-20261119.md` (D2) and of AF2-E2: `cmpb`, `cmpw`, `cmpl` then `jl`, `jge`,
`jg`, `jle` (the sign flag of a `w`-bit difference, the overflow flag modulo `2^w`); a borrow of the low `w` bits of
`x >>> k` (`shrq $32; cmpb $2; jbe`, `l2zBits` entry); and the 32-bit borrow of a sum with a `notl` term
(`notl; addl; cmpl $1; sbbq $-1`, `l2zArith` entry). -/

namespace DeriveReadFormsTests

/-- The functions of the narrow signed compares: `r` (two registers) or `l` (the literal 7), the width, the jump. -/
def narrowSignedFns : List String :=
  ["r", "l"].flatMap fun k => [8, 16, 32].flatMap fun w => ["l", "ge", "g", "le"].map fun cc => s!"t{k}{w}{cc}"

/-- The signed `<` of the low `w` bits: `slt32` for 32 bits, else `slt` of the sign extensions. -/
def sltW (w : Nat) (a b : Val) : Cond :=
  if w == 32 then .slt32 a b else if w == 16 then .slt (.sext .b16 a) (.sext .b16 b) else .slt (.sext .b8 a) (.sext .b8 b)

end DeriveReadFormsTests

#eval show TermElabM Unit from do
  let fns := DeriveReadFormsTests.narrowSignedFns ++ ["bshr", "asbb"]
  let (blocks, nitems, compared, skipped, bad) ← blockMeaning fns `DeriveReadFormsCode.m7 300
  logInfo m!"L2-READ forms: {blocks} blocks, {nitems} items, {compared} values compared, not compiled {skipped}, {bad.length} different {bad.take 3}"
  check (blocks == 3 * (fns.length - 1) + 1 && skipped.isEmpty) s!"L2-READ forms: {blocks} blocks read and compiled, not compiled {skipped}"
  check bad.isEmpty s!"L2-READ forms: the raw terms and the read values differ: {bad.take 3}"

#eval show TermElabM Unit from do
  let fns := DeriveReadFormsTests.narrowSignedFns ++ ["bshr", "asbb"]
  let bases := fns.map fun fn => (fn, ((labelAddr DeriveReadFormsCode.code fn).getD 0))
  let ws ← walkAll ``DeriveReadFormsCode.L1.step `DeriveReadFormsCode.m8 (specsOf DeriveReadFormsCode.code bases)
  let (compared, bad) ← DeriveReadFormsTests.blockEdges ws bases 300
  logInfo m!"L2-READ forms, edge pairs: {compared} values compared, {bad.length} different {bad.take 3}"
  check bad.isEmpty s!"L2-READ forms: the raw terms and the read values differ at the edges: {bad.take 3}"

#eval show TermElabM Unit from do
  -- the first target is the fall-through block (offset 8) for `jl`, the jump target (offset 16) for the others
  for k in ["r", "l"] do
    for w in [8, 16, 32] do
      for cc in ["l", "ge", "g", "le"] do
        let fn := s!"t{k}{w}{cc}"
        let a := r .rax
        let b := if k == "r" then r .rbx else n 7
        let slt := DeriveReadFormsTests.sltW w
        let want : Cond := match cc with
          | "g" => slt b a
          | "le" => .not (slt b a)
          | _ => .not (slt a b)
        let .ok p := partOf fn | throwError "{fn}: no part"
        match p.term with
        | .branch c (.goto y) (.goto _) =>
          check (c.show == want.show) s!"{fn}: the condition is {c.show}, expected {want.show}"
          check (y == if cc == "l" then 8 else 16) s!"{fn}: the first target is {y}"
        | _ => throwError "{fn}: no branch"
  -- `shrq $32; cmpb $2; jbe`: the low byte of `rax >>> 32` is at most 2
  let .ok p := partOf "bshr" | throwError "bshr: no part"
  let want : Cond := .ule (.zext .b8 (.shr (r .rax) ⟨32, by decide⟩)) (n 2)
  match p.term with
  | .branch c _ _ => check (c.sameNorm want || c.sameNorm (.not want)) s!"bshr: the condition is {c.show}, expected {want.show}"
  | _ => throwError "bshr: no branch"

#eval show TermElabM Unit from do
  let rc (stx : TermElabM Syntax) := do readBody readCond (← elabE stx)
  let ok (what : String) (stx : TermElabM Syntax) (want : Option Cond) : TermElabM Unit := do
    match ← rc stx with
    | .ok c => if let some c' := want then check (c.show == c'.show) s!"{what}: read {c.show}, expected {c'.show}"
    | .error e => throwError "{what}: refused {repr e}"
    let (nd, first) ← condDiffs stx
    check (nd == 0) s!"{what}: differs from the raw term on {nd} states, first {first}"
  let refused (what : String) (stx : TermElabM Syntax) : TermElabM Unit :=
    do check (isErr (← rc stx) fun _ => true) s!"refused: {what}"
  for w in [8, 16, 32] do
    let M := 2 ^ w
    let m := Syntax.mkNumLit (toString M)
    let wn := Syntax.mkNumLit (toString w)
    let low (v : Val) : Val := if w == 8 then .zext .b8 v else if w == 16 then .zext .b16 v else .zext32 v
    let slt := DeriveReadFormsTests.sltW w
    -- msbn_sub_eq_of_iff_not_slt: `jge` of two registers
    ok s!"jge, {w} bits" `(fun d : MachineData =>
        (d.regs.rax.toBitVec.extractLsb' 0 $wn - d.regs.rbx.toBitVec.extractLsb' 0 $wn).msb =
          (((d.regs.rax.toNat : Int) - (d.regs.rbx.toNat : Int)).bmod $m !=
            (d.regs.rax.toNat : Int).bmod $m - (d.regs.rbx.toNat : Int).bmod $m)) (some (.not (slt (r .rax) (r .rbx))))
    -- msbn_sub_lit_eq_of_iff_not_slt: `jge` of a register and the literal 7
    ok s!"jge 7, {w} bits" `(fun d : MachineData =>
        (d.regs.rax.toBitVec.extractLsb' 0 $wn - BitVec.ofNat $wn 7).msb =
          (((d.regs.rax.toNat : Int) - 7).bmod $m != (d.regs.rax.toNat : Int).bmod $m - 7)) (some (.not (slt (r .rax) (n 7))))
    -- refused: the overflow of another register, of another modulus, of another literal
    refused s!"{w} bits: the overflow of another register" `(fun d : MachineData =>
        (d.regs.rax.toBitVec.extractLsb' 0 $wn - d.regs.rbx.toBitVec.extractLsb' 0 $wn).msb =
          (((d.regs.rax.toNat : Int) - (d.regs.rcx.toNat : Int)).bmod $m !=
            (d.regs.rax.toNat : Int).bmod $m - (d.regs.rcx.toNat : Int).bmod $m))
    let m2 := Syntax.mkNumLit (toString (2 * M))
    refused s!"{w} bits: the overflow modulo 2^(w+1)" `(fun d : MachineData =>
        (d.regs.rax.toBitVec.extractLsb' 0 $wn - d.regs.rbx.toBitVec.extractLsb' 0 $wn).msb =
          (((d.regs.rax.toNat : Int) - (d.regs.rbx.toNat : Int)).bmod $m2 !=
            (d.regs.rax.toNat : Int).bmod $m2 - (d.regs.rbx.toNat : Int).bmod $m2))
    refused s!"{w} bits: the overflow of another literal" `(fun d : MachineData =>
        (d.regs.rax.toBitVec.extractLsb' 0 $wn - BitVec.ofNat $wn 7).msb =
          (((d.regs.rax.toNat : Int) - 6).bmod $m != (d.regs.rax.toNat : Int).bmod $m - 6))
    -- int_toNat_shiftRight with not_nocarryn_lit_or_zero_iff_le: `shrq $32; cmpb $2; jbe` at `w` bits
    let c := Syntax.mkNumLit (toString (M - 2))
    ok s!"jbe of rax >>> 32, {w} bits" `(fun d : MachineData =>
        ¬ (($c : Int) + ((d.regs.rax.toNat : Int) >>> 32)) % ($m : Int) =
            ((d.regs.rax.toNat : Int) >>> 32) % ($m : Int) - 2 ∨
          (d.regs.rax.toBitVec >>> 32).extractLsb' 0 $wn - BitVec.ofNat $wn 2 = 0#$wn)
      (some (.ule (low (.shr (r .rax) ⟨32, by decide⟩)) (n 2)))
  -- the 64-bit borrow of a shifted operand: `(C + ↑x.toNat >>> 8) % 2^64 = ↑x.toNat >>> 8 - K`
  ok "jae of rax >>> 8, 64 bits" `(fun d : MachineData =>
      ((18446744073709551609 : Int) + ((d.regs.rax.toNat : Int) >>> 8)) % (18446744073709551616 : Int) =
        ((d.regs.rax.toNat : Int) >>> 8) - 7) (some (.ule (n 7) (.shr (r .rax) ⟨8, by decide⟩)))
  -- natCast_sub_mod_eq: the `notl` term `↑(2^32 - 1 - x % 2^32)` of a 32-bit sum (`l2zArith`)
  ok "sbb of a sum with notl" `(fun d : MachineData =>
      ((4294967295 : Int) + (((d.regs.rbx.toNat : Int) + ((4294967295 - d.regs.rax.toNat % 4294967296 : Nat) : Int)) %
        (4294967296 : Int)) % (18446744073709551616 : Int)) % (4294967296 : Int) =
        ((d.regs.rbx.toNat : Int) + ((4294967295 - d.regs.rax.toNat % 4294967296 : Nat) : Int)) % (4294967296 : Int) - 1)
      none
  -- refused: `c - x % 2^32` with `c < 2^32 - 1` (the subtraction of `Nat` can cut at 0)
  refused "a sum with a cut subtraction" `(fun d : MachineData =>
      ((4294967295 : Int) + (((d.regs.rbx.toNat : Int) + ((4294967294 - d.regs.rax.toNat % 4294967296 : Nat) : Int)) %
        (4294967296 : Int)) % (18446744073709551616 : Int)) % (4294967296 : Int) =
        ((d.regs.rbx.toNat : Int) + ((4294967294 - d.regs.rax.toNat % 4294967296 : Nat) : Int)) % (4294967296 : Int) - 1)
  -- refused: a shift by 64 or more
  refused "a shift by 64" `(fun d : MachineData =>
      ((18446744073709551609 : Int) + ((d.regs.rax.toNat : Int) >>> 64)) % (18446744073709551616 : Int) =
        ((d.regs.rax.toNat : Int) >>> 64) - 7)

/-! ### The real functions: the entry blocks of `l2zBits` and `l2zArith` derive; LBB16_3 of `l2zFlags` derives (D43,
L2-FLAGS): the `cmovb` and the `seta` at its start read `cf` and `zf` of the `cmpq %rsi, %rdi` of the entry block, which
the entry block keeps -/

#eval show TermElabM Unit from do
  let part (fn : String) (off : Nat) : TermElabM (Except GenError Part) := do
    let some parts := Skel.Gen.Derived.level2z.lookup fn | throwError "{fn}: no function"
    let some r := parts.lookup off | throwError "{fn}: no block at {off}"
    pure r
  for fn in ["l2zBits", "l2zArith"] do
    match ← part fn 0 with
    | .ok _ => pure ()
    | .error e => throwError "{fn}: the entry block does not derive: {repr e}"
  -- L2-FLAGS: the entry block keeps the flags, so LBB16_3 derives (`Skel/Test/DeriveFlags.lean`)
  match ← part "l2zFlags" 8 with
  | .error e => throwError "l2zFlags LBB16_3: {repr e}"
  | .ok _ => pure ()

#eval show TermElabM Unit from do
  -- the read values of all blocks of `l2zBits` and `l2zArith` against the raw terms
  let fns := ["l2zBits", "l2zArith"]
  let bases := fns.map fun fn => (fn, ((labelAddr Lift.Level2z.Code.code fn).getD 0))
  let ws ← walkAll ``Lift.Level2z.L1.step `DeriveReadFormsCode.m9 (specsOf Lift.Level2z.Code.code bases)
  let (blocks, nitems, compared, skipped, bad) ← meaning bases ws 300
  logInfo m!"l2zBits, l2zArith: {blocks} blocks, {nitems} items, {compared} values compared, not compiled {skipped}, {bad.length} different {bad.take 3}"
  check (blocks == 4 && skipped.isEmpty) s!"l2zBits, l2zArith: {blocks} blocks read and compiled, not compiled {skipped}"
  check bad.isEmpty s!"l2zBits, l2zArith: the raw terms and the read values differ: {bad.take 3}"
