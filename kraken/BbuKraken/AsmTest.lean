import BbuKraken.Asm
import Kraken.X64.Parser

open Kraken.X64.Parser

namespace Bbu

set_option maxRecDepth 100000

-- The function programs make up the linked file.
example : bbuAsm = isSpilledAsm ++ shallowestCopyAsm ++ pushAsm ++ dupAsm ++ produceAsm
    ++ swapWithAsm ++ generateAsm ++ finishAsm ++ loopAsm ++ popAsm ++ buildBottomUpAsm
    ++ emissionPopAsm ++ spillSetAddAsm ++ spillSetAsm ++ removeSurplusAsm ++ removeSurplusEntryAsm := by
  rfl

-- `bbuParseFile` reads `leaq disp(,%i,8), %r` as the operand with no base.
example : swapWithAsm[7]? = some (.instr (.regular .W64 .W64
    (.lea (.low .rdi .W64) ⟨none, some ⟨.rdx, .W64⟩, .int64 0⟩))) := by rfl

-- The other lines are as `parse` reads them.
example : swapWithAsm.take 7 = parse("_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset:
	movq	%rdi, %rax
	movq	%rsi, %rdx
	movq	32(%rdi), %rsi
	movl	$2, %ecx
	cmpq	%rsi, %rdx
	jnb	.LB35") := by rfl

-- Each line with an operand with no base.
example : (bbuAsm.filter fun
    | .instr (.regular _ _ (.lea _ a)) => a.base.isNone
    | _ => false) =
    [.instr (.regular .W64 .W64 (.lea (.low .r14 .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdi .W64) ⟨none, some ⟨.rdx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rbx .W64) ⟨none, some ⟨.r14, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.r12, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .r8 .W64) ⟨none, some ⟨.rdi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩))] := by
  rfl

-- `bbuParseFn` reads the file of the name.
example : (isSpilledAsm.head? = some (.label Names.isSpilled)) := by rfl
example : (buildBottomUpAsm.head? = some (.label Names.build_bottom_up)) := by rfl
example : (popAsm.head? = some (.label Names.pop)) := by rfl
example : (emissionPopAsm.head? = some (.label Names.emission_pop)) := by rfl
example : (spillSetAddAsm.head? = some (.label Names.spillSetAdd)) := by rfl
example : (spillSetAsm.head? = some (.label Names.spill_set)) := by rfl
example : (removeSurplusAsm.head? = some (.label Names.removeSurplus)) := by rfl
example : (removeSurplusEntryAsm.head? = some (.label Names.remove_surplus)) := by rfl

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

namespace Bbu.AsmTest

def notLiteral : String := "a" ++ "b"
def noFile : String := "noFile"

-- `bbuParseFn` takes only a def with a string literal value, and the file must exist.
/-- error: Bbu.AsmTest.notLiteral is not a def with a string literal as its value -/
#guard_msgs in
example : Program := bbuParseFn(notLiteral)
/--
error: no such file or directory (error code: 2)
  file: c/bbu/noFile.S
-/
#guard_msgs in
example : Program := bbuParseFn(noFile)

end Bbu.AsmTest
