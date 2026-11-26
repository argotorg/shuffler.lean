import Lift.P1.Command
import Kraken.X64.Parser
import Lean

/-! The machine code of the synthetic pair of a callee with memory (task PIL-CALL, `Skel/Test/GenCallMem.lean`). The
instruction sizes are those of the encodings of GNU as; the unit starts at 0x100000, as the toy units do.

* `put`: stores `rsi` at `(rdi)`, returns 0. Its result has memory.
* `putCall`: saves `rbx`, calls `put` on its own `rdi`, reads the stored word back into `rax`, restores `rbx`.
* `putBad`: saves `rbx`, calls `put` with `rdi := rsp`: `put` writes the word of the saved `rbx`.
* `inc`: returns `rdi + 1`. Its result has no memory (MULTI-CALLEE).
* `two`: saves `rbx`, calls `put` on its own `rdi` and `rsi`, loads the stored word into `rdi`, calls `inc`, adds 1, restores `rbx`:
  two callees with different interfaces (MULTI-CALLEE, `Skel/Test/GenMultiCallee.lean`).
* `twice`: saves `rbx`, calls `put` on its own `rdi` and `rsi`, calls `put` again from the next block on `rbx` and `rbx`, loads the
  stored word into `rax`, restores `rbx`: one callee with memory called from two blocks at one depth (MULTI-CALLEE2).
* `twoDepth`: `twice` with a push of `rbx` before the second call, so the two calls of `put` are at two depths (MULTI-CALLEE2,
  the negative). -/

namespace Skel.Test.CallMem.Code

def sizes : List Nat :=
  [0, 0, 3, 2, 1, 0,
   0, 0, 1, 3, 5, 3, 1, 1, 0,
   0, 0, 1, 3, 5, 1, 1, 0,
   0, 0, 4, 1, 0,
   0, 0, 1, 3, 5, 3, 5, 4, 1, 1, 0,
   0, 0, 1, 3, 5, 3, 3, 5, 3, 1, 1, 0,
   0, 0, 1, 3, 5, 1, 3, 5, 1, 3, 1, 1, 0]

elab "callMemProgram(" source:str ")" : term => do
  match Kraken.X64.Parser.parse (Kraken.X64.Parser.stripDirectives source.getString) with
  | .ok p => return Lean.toExpr p
  | .error e => Lean.throwErrorAt source e

def program : Program := callMemProgram(".Lcm.put:\nput:\n movq\t%rsi, (%rdi)\n xorl\t%eax, %eax\n retq\n.Lfunc_end0:\n.Lcm.putCall:\nputCall:\n pushq\t%rbx\n movq\t%rdi, %rbx\n callq\t.Lcm.put\n movq\t(%rbx), %rax\n popq\t%rbx\n retq\n.Lfunc_end1:\n.Lcm.putBad:\nputBad:\n pushq\t%rbx\n movq\t%rsp, %rdi\n callq\t.Lcm.put\n popq\t%rbx\n retq\n.Lfunc_end2:\n.Lcm.inc:\ninc:\n leaq\t1(%rdi), %rax\n retq\n.Lfunc_end3:\n.Lcm.two:\ntwo:\n pushq\t%rbx\n movq\t%rdi, %rbx\n callq\t.Lcm.put\n movq\t(%rbx), %rdi\n callq\t.Lcm.inc\n leaq\t1(%rax), %rax\n popq\t%rbx\n retq\n.Lfunc_end4:\n.Lcm.twice:\ntwice:\n pushq\t%rbx\n movq\t%rdi, %rbx\n callq\t.Lcm.put\n movq\t%rbx, %rdi\n movq\t%rbx, %rsi\n callq\t.Lcm.put\n movq\t(%rbx), %rax\n popq\t%rbx\n retq\n.Lfunc_end5:\n.Lcm.twoDepth:\ntwoDepth:\n pushq\t%rbx\n movq\t%rdi, %rbx\n callq\t.Lcm.put\n pushq\t%rbx\n movq\t%rbx, %rsi\n callq\t.Lcm.put\n popq\t%rbx\n movq\t(%rbx), %rax\n popq\t%rbx\n retq\n.Lfunc_end6:\n")

def code : _root_.Executable :=
  ⟨1048576, program.zipWith (fun d n => ⟨d, n⟩) sizes⟩

#guard program.length == sizes.length

end Skel.Test.CallMem.Code
