import BbuKraken.Unit.Plan.ClassifyReturnPrefix

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

theorem prologue_continue [Host] [FunDecls]
    (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (hok : c.Ok) (ha : classifyA c s) (t : MachineData)
    (lo : List Word) (w q : Word) (hb : Bd P c F s ra lo w q t)
    (hdi : t.regs.rdi.toBitVec = P) (hsi : t.regs.rsi.toBitVec = c.h.mp)
    (hdx : t.regs.rdx.toBitVec = c.h.dn) (hcx : t.regs.rcx.toBitVec = rcx s)
    (flags : StatusFlags) (hr : (inp c s).slot.kind ≠ FunctionReturnLabel) :
    WP.wp prologueScratchTail (prologueI P c F s ra (.label ".LB.Planner.classify.0") 2)
      (Program.Intercept (Program.labels classifyAsm) (s.pushRa ra)
        (prologueI P c F s ra) (E P c F s ra))
      (returnPrefixState t c.h.p.src (sw c s) (inp c s).slot.kind flags) := by
  apply prologue_scratch P c F s ra hok ha _ lo w q
  · exact hb.next rfl rfl
  · exact hdi
  · exact hsi
  · exact hdx
  · exact hcx
  · simp only [returnPrefixState, hcx]
  · rfl
  · exact widen8_low _
  · exact hr

end Bbu.Unit.ClassifyU
