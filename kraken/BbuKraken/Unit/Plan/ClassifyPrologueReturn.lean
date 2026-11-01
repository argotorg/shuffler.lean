module

public import BbuKraken.Unit.Plan.ClassifyReturnPrefix
import all BbuKraken.Unit.Plan.ClassifyReturnPrefix

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

theorem classify_return_lookup :
    (Program.labels classifyAsm)[9]? = some ".LB.Planner.classify.8" := by
  rw [classify_labels]
  rfl

theorem noClass_low : (4294967295#64).setWidth 8 = Flat.NOCLASS := by
  unfold Flat.NOCLASS
  bv_decide

theorem return_prefix_inv
    (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) (lo : List Word) (w q : Word) (hb : Bd P c F s ra lo w q t)
    (flags : StatusFlags) (hr : (inp c s).slot.kind = FunctionReturnLabel) :
    Inv P c F s ra (.label ".LB.Planner.classify.8")
      (returnPrefixState t c.h.p.src (sw c s) (inp c s).slot.kind flags) := by
  apply prologue_return
  · exact hb.next rfl rfl
  · change (4294967295#64).setWidth 8 = (inp c s).eval
    exact noClass_low.trans (eval_return (inp c s) hr).symm

theorem prologue_return_exit [Host] [FunDecls]
    (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) (lo : List Word) (w q : Word) (hb : Bd P c F s ra lo w q t)
    (flags : StatusFlags) (hr : (inp c s).slot.kind = FunctionReturnLabel) :
    Program.Intercept (Program.labels classifyAsm) (s.pushRa ra)
      (prologueI P c F s ra) (E P c F s ra)
      (label ".LB.Planner.classify.8")
      (returnPrefixState t c.h.p.src (sw c s) (inp c s).slot.kind flags) := by
  apply Program.Intercept.intro_label classify_return_lookup
  refine Or.inl ⟨?_, ?_, ?_⟩
  · exact hb.kb.stack (by decide)
  · exact return_prefix_inv P c F s ra t lo w q hb flags hr
  · exact Or.inl (by decide : 0 < 20)

end Bbu.Unit.ClassifyU
