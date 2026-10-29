import BbuKraken.Asm
import Kraken.X64.Parser

open Kraken.X64.Parser

namespace Bbu

set_option maxRecDepth 100000

-- The function programs make up the linked file.
example : bbuAsm = isSpilledAsm ++ shallowestCopyAsm ++ swapWithAsm ++ pushAsm
    ++ dupAsm ++ produceAsm ++ generateAsm ++ finishAsm ++ loopAsm ++ buildBottomUpAsm := by rfl

-- `bbuParseFile` reads `leaq disp(,%i,8), %r` as the operand with no base.
example : swapWithAsm[6]? = some (.instr (.regular .W64 .W64
    (.lea (.low .rdi .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩))) := by rfl

-- The other lines are as `parse` reads them.
example : swapWithAsm.take 6 = parse("swapWith:
	movq	(%rdi), %r10
	cmpq	%r10, %rsi
	jnb	.LB12
	movq	%rdi, %rax
	movq	%rsi, %rdx") := by rfl

-- Each line with an operand with no base.
example : (bbuAsm.filter fun
    | .instr (.regular _ _ (.lea _ a)) => a.base.isNone
    | _ => false) =
    [.instr (.regular .W64 .W64 (.lea (.low .rdi .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rsi .W64) ⟨none, some ⟨.r8, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .r14 .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .r10 .W64) ⟨none, some ⟨.r8, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rsi .W64) ⟨none, some ⟨.r10, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .r8 .W64) ⟨none, some ⟨.rax, .W64⟩, .int64 0⟩))] := by
  rfl

end Bbu

namespace Bbu

-- A malformed line still makes the parse fail, with or without an operand with no base.
#guard (parseLines "\tleaq\t0(,%rsi,8, %rdi" matches .error _)
#guard (parseLines "\tmovq\t0(,%rsi,8), %rdi" matches .error _)
#guard (parseLines "\tleaq\t0(,%rsi,8), %rdi\n\tfoo\t%rax" matches .error _)
#guard (parseLines "\tmovq\t(%rdi), %r10\n\tmovq\t%rdi, (%rax" matches .error _)
-- A good line parses.
#guard (parseLines "\tleaq\t0(,%rsi,8), %rdi" matches .ok _)

end Bbu
