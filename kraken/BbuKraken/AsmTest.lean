module

public import BbuKraken.Asm
import all BbuKraken.Asm
public import Kraken.X64.Parser
import all Kraken.X64.Parser

@[expose] public section

open Kraken.X64.Parser

namespace Bbu

set_option maxRecDepth 100000

-- The function programs make up the linked file.
example : bbuAsm = isSpilledAsm ++ shallowestCopyAsm ++ dupAsm ++ pushAsm ++ produceAsm
    ++ swapWithAsm ++ generateAsm ++ finishAsm ++ loopAsm ++ spillSetAddAsm ++ mapAsm
    ++ closestCopyAsm ++ mapInPlaceAsm ++ mapClosestCopiesAsm ++ mapWildcardSlotCopiesAsm
    ++ keepWildcardSlotsAsm ++ absorbSurplusAsm ++ popAsm ++ removeSurplusAsm
    ++ permuteAtLowestHeightAsm ++ isAvailableAsm ++ runAsm ++ isRetainedAsm
    ++ hasOtherRetainedCopyAsm ++ isDemandedAsm ++ classifyAsm ++ resolveAsm ++ plannerRunAsm
    ++ buildBottomUpAsm ++ emissionPopAsm ++ spillSetAsm ++ removeSurplusEntryAsm
    ++ permuteEntryAsm ++ permuteAtLowestHeightEntryAsm ++ buildMappingAsm ++ resolveEntryAsm
    ++ emitAsm ++ planAsm := by
  rfl

-- `bbuParseFile` reads `leaq disp(,%i,8), %r` as the operand with no base.
example : swapWithAsm[7]? = some (.instr (.regular .W64 .W64
    (.lea (.low .rcx .W64) ⟨none, some ⟨.rdx, .W64⟩, .int64 0⟩))) := by rfl

-- The other lines are as `parse` reads them.
example : swapWithAsm.take 7 = parse("_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset:
	subq	$8, %rsp
	movq	%rsi, %rdx
	movq	32(%rdi), %rsi
	cmpq	%rsi, %rdx
	jnb	.LB.Emission.swapWith.0
	movq	%rdi, %rax") := by rfl

-- Each line with an operand with no base.
example : (bbuAsm.filter fun
    | .instr (.regular _ _ (.lea _ a)) => a.base.isNone
    | _ => false) =
    [.instr (.regular .W64 .W64 (.lea (.low .r14 .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rcx .W64) ⟨none, some ⟨.rdx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rcx .W64) ⟨none, some ⟨.r14, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rbx .W64) ⟨none, some ⟨.r14, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rbx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rbx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rbx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rbx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .r8 .W64) ⟨none, some ⟨.rdi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .r14 .W64) ⟨none, some ⟨.rcx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rcx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.r12, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rcx .W64) ⟨none, some ⟨.rbx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rsi, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rsi .W64) ⟨none, some ⟨.rbx, .W64⟩, .int64 0⟩)),
     .instr (.regular .W64 .W64 (.lea (.low .rdx .W64) ⟨none, some ⟨.rbx, .W64⟩, .int64 0⟩))] := by
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
example : (finishAsm.head? = some (.label Names.permute)) := by rfl
example : (permuteEntryAsm.head? = some (.label Names.permuteEntry)) := by rfl
example : (permuteAtLowestHeightAsm.head? = some (.label Names.permuteAtLowestHeight)) := by rfl
example : (isAvailableAsm.head? = some (.label Names.isAvailable)) := by rfl
example : (runAsm.head? = some (.label Names.run)) := by rfl
example : (emitAsm.head? = some (.label Names.emit)) := by rfl
example : (plannerRunAsm.head? = some (.label Names.plannerRun)) := by rfl
example : (planAsm.head? = some (.label Names.plan)) := by rfl
example : (permuteAtLowestHeightEntryAsm.head? = some (.label Names.permute_at_lowest_height)) := by
  rfl
example : (mapAsm.head? = some (.label Names.map)) := by rfl
example : (closestCopyAsm.head? = some (.label Names.closestCopy)) := by rfl
example : (mapInPlaceAsm.head? = some (.label Names.mapInPlace)) := by rfl
example : (mapClosestCopiesAsm.head? = some (.label Names.mapClosestCopies)) := by rfl
example : (mapWildcardSlotCopiesAsm.head? = some (.label Names.mapWildcardSlotCopies)) := by rfl
example : (keepWildcardSlotsAsm.head? = some (.label Names.keepWildcardSlots)) := by rfl
example : (absorbSurplusAsm.head? = some (.label Names.absorbSurplus)) := by rfl
example : (buildMappingAsm.head? = some (.label Names.build_mapping)) := by rfl
example : (isRetainedAsm.head? = some (.label Names.isRetained)) := by rfl
example : (hasOtherRetainedCopyAsm.head? = some (.label Names.hasOtherRetainedCopy)) := by rfl
example : (isDemandedAsm.head? = some (.label Names.isDemanded)) := by rfl
example : (classifyAsm.head? = some (.label Names.classify)) := by rfl
example : (resolveAsm.head? = some (.label Names.resolve)) := by rfl
example : (resolveEntryAsm.head? = some (.label Names.resolveEntry)) := by rfl

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

-- `bbuParseFn` takes only a def with a string literal value, and the function must exist.
/-- error: Bbu.AsmTest.notLiteral is not a def with a string literal as its value -/
#guard_msgs in
example : Program := bbuParseFn(notLiteral)
/-- error: assembly function not found: noFile -/
#guard_msgs in
example : Program := bbuParseFn(noFile)

end Bbu.AsmTest
