module

public import ProofKit.Lea32
import all ProofKit.Lea32
public import BbuKraken.Specs
import all BbuKraken.Specs
public import Kraken.X64.Parser
import all Kraken.X64.Parser
public import ProofKit.SymExec
import all ProofKit.SymExec

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace ProofKitTest.Lea32

/-- This sequence checks the negative displacement through two branches and a load. -/
def branchLoad : Program := parse("
 leal -1(%r13), %eax
 cmpb $1, %al
 jbe .free
 cmpb $0, 3(%rsp)
 je .free
")

theorem branchLoad_wp [Host] [FunDecls] (t : MachineData)
    (h : (t.dmem.loadInt (t.regs.rsp.toBitVec + 3#64) 1).isSome = true) :
    WP.wp branchLoad (fun _ _ => True) (fun _ _ => True) t := by
  unfold branchLoad
  kvcgen64 [lea32_neg1_spec]
  all_goals first | exact h | trivial

def decrement : Program := parse("leal -1(%r13), %eax\n")

theorem decrement_wp [Host] [FunDecls] (t : MachineData) :
    WP.wp decrement
      (fun _ u => u.regs.rax.toBitVec =
        ((t.regs.r13.toBitVec - 1#64).take 32).zeroExtend 64)
      (fun _ _ => False) t := by
  unfold decrement
  kvcgen64 [lea32_neg1_spec]

example : ((0#64 - 1#64).take 32).zeroExtend 64 = 4294967295#64 := by decide
example : ((4294967296#64 - 1#64).take 32).zeroExtend 64 = 4294967295#64 := by decide
example : ((1#64 - 1#64).take 32).zeroExtend 64 = 0#64 := by decide
example : ((4294967297#64 - 1#64).take 32).zeroExtend 64 = 0#64 := by decide

end ProofKitTest.Lea32
