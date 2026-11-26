import Lift.P1.Command
import Kraken.X64.Parser
import Lean

/-! The machine code of the synthetic functions of the test of the stack words (task AF-B, `Skel/Test/GenSaved.lean`):
callers of `leaf` that push 2 or 4 saved registers, call, pop the registers and return. The form is that of `toyJob`: the
entry block branches, and the block that pushes is not the entry. The instruction sizes are those of the encodings of GNU as;
the unit starts at 0x100000, as the toy units do.

* `leaf`: `rax := rdi`.
* `save2`, `save4`: a store through `rdi` before the call, and the pops in the order of the ABI.
* `save2b`, `save4b`: the store through `rbx` after the call.
* `save2n`: no store through a register (the frame form, which the generator does not make).
* `save2x`: the pops are in the order of the pushes: each pop reads the word of another register.
* `frame8`, `frame4` (G1-16): the frame form with no call: a slot of 8 bytes (`rdi`) and a slot of 4 bytes (`edi`) below
  `sub rsp`, read back into `rax` (`eax`).
* `frameCall` (G1-16): the frame form with a call of `leaf`: `rbx` pushed, `rbx := rdi`, the call, `rax + rbx`, the pop. -/

namespace Skel.Test.Saved.Code

def sizes : List Nat :=
  [0, 0, 3, 1, 0, 0, 0, 4, 4, 2, 2, 1, 0, 1, 2, 3,
   3, 4, 3, 5, 2, 2, 1, 1, 0, 0, 0, 4, 4, 2, 2, 1,
   0, 1, 2, 3, 3, 5, 4, 2, 2, 1, 1, 0, 0, 0, 4, 4,
   2, 2, 1, 0, 1, 2, 2, 1, 3, 3, 4, 3, 5, 2, 1, 2,
   2, 1, 1, 0, 0, 0, 4, 4, 2, 2, 1, 0, 1, 2, 2, 1,
   3, 3, 5, 4, 2, 1, 2, 2, 1, 1, 0, 0, 0, 4, 4, 2,
   2, 1, 0, 1, 2, 3, 3, 5, 2, 2, 1, 1, 0, 0, 0, 4,
   4, 2, 2, 1, 0, 1, 2, 3, 3, 4, 3, 5, 2, 1, 2, 1,
   0,
   0, 0, 4, 4, 4, 4, 1, 0,
   0, 0, 4, 4, 4, 4, 1, 0,
   0, 0, 1, 3, 5, 3, 1, 1, 0]

elab "savedProgram(" source:str ")" : term => do
  match Kraken.X64.Parser.parse (Kraken.X64.Parser.stripDirectives source.getString) with
  | .ok p => return Lean.toExpr p
  | .error e => Lean.throwErrorAt source e

def program : Program := savedProgram(".Lfix.leaf:\nleaf:\n movq\t%rdi, %rax\n retq\n.Lfunc_end0:\n.Lfix.save2:\nsave2:\n movq\t8(%rdi), %rsi\n cmpq\t16(%rdi), %rsi\n jbe\t.LBB1_2\n xorl\t%eax, %eax\n retq\n.LBB1_2:\n pushq\t%rbx\n pushq\t%r14\n movq\t%rdi, %rbx\n movq\t%rdi, %r14\n movq\t%rsi, 8(%rdi)\n movq\t(%rdi), %rdi\n callq\t.Lfix.leaf\n xorl\t%eax, %eax\n popq\t%r14\n popq\t%rbx\n retq\n.Lfunc_end1:\n.Lfix.save2b:\nsave2b:\n movq\t8(%rdi), %rsi\n cmpq\t16(%rdi), %rsi\n jbe\t.LBB2_2\n xorl\t%eax, %eax\n retq\n.LBB2_2:\n pushq\t%rbx\n pushq\t%r14\n movq\t%rdi, %rbx\n movq\t(%rdi), %rdi\n callq\t.Lfix.leaf\n movq\t%rax, 24(%rbx)\n xorl\t%eax, %eax\n popq\t%r14\n popq\t%rbx\n retq\n.Lfunc_end2:\n.Lfix.save4:\nsave4:\n movq\t8(%rdi), %rsi\n cmpq\t16(%rdi), %rsi\n jbe\t.LBB3_2\n xorl\t%eax, %eax\n retq\n.LBB3_2:\n pushq\t%rbp\n pushq\t%r15\n pushq\t%r14\n pushq\t%rbx\n movq\t%rdi, %rbx\n movq\t%rdi, %r14\n movq\t%rsi, 8(%rdi)\n movq\t(%rdi), %rdi\n callq\t.Lfix.leaf\n xorl\t%eax, %eax\n popq\t%rbx\n popq\t%r14\n popq\t%r15\n popq\t%rbp\n retq\n.Lfunc_end3:\n.Lfix.save4b:\nsave4b:\n movq\t8(%rdi), %rsi\n cmpq\t16(%rdi), %rsi\n jbe\t.LBB4_2\n xorl\t%eax, %eax\n retq\n.LBB4_2:\n pushq\t%rbp\n pushq\t%r15\n pushq\t%r14\n pushq\t%rbx\n movq\t%rdi, %rbx\n movq\t(%rdi), %rdi\n callq\t.Lfix.leaf\n movq\t%rax, 24(%rbx)\n xorl\t%eax, %eax\n popq\t%rbx\n popq\t%r14\n popq\t%r15\n popq\t%rbp\n retq\n.Lfunc_end4:\n.Lfix.save2n:\nsave2n:\n movq\t8(%rdi), %rsi\n cmpq\t16(%rdi), %rsi\n jbe\t.LBB5_2\n xorl\t%eax, %eax\n retq\n.LBB5_2:\n pushq\t%rbx\n pushq\t%r14\n movq\t%rdi, %rbx\n movq\t(%rdi), %rdi\n callq\t.Lfix.leaf\n xorl\t%eax, %eax\n popq\t%r14\n popq\t%rbx\n retq\n.Lfunc_end5:\n.Lfix.save2x:\nsave2x:\n movq\t8(%rdi), %rsi\n cmpq\t16(%rdi), %rsi\n jbe\t.LBB6_2\n xorl\t%eax, %eax\n retq\n.LBB6_2:\n pushq\t%rbx\n pushq\t%r14\n movq\t%rdi, %rbx\n movq\t%rdi, %r14\n movq\t%rsi, 8(%rdi)\n movq\t(%rdi), %rdi\n callq\t.Lfix.leaf\n xorl\t%eax, %eax\n popq\t%rbx\n popq\t%r14\n retq\n.Lfunc_end6:\n.Lfix.frame8:\nframe8:\n subq\t$8, %rsp\n movq\t%rdi, (%rsp)\n movq\t(%rsp), %rax\n addq\t$8, %rsp\n retq\n.Lfunc_end7:\n.Lfix.frame4:\nframe4:\n subq\t$8, %rsp\n movl\t%edi, 4(%rsp)\n movl\t4(%rsp), %eax\n addq\t$8, %rsp\n retq\n.Lfunc_end8:\n.Lfix.frameCall:\nframeCall:\n pushq\t%rbx\n movq\t%rdi, %rbx\n callq\t.Lfix.leaf\n addq\t%rbx, %rax\n popq\t%rbx\n retq\n.Lfunc_end9:\n")

def code : _root_.Executable :=
  ⟨1048576, program.zipWith (fun d n => ⟨d, n⟩) sizes⟩

#guard program.length == sizes.length

end Skel.Test.Saved.Code
