module

public import BbuKraken.Unit.Plan.ClassifyPrologueReturn
import all BbuKraken.Unit.Plan.ClassifyPrologueReturn
public import BbuKraken.Unit.Plan.ClassifyPrologueContinue
import all BbuKraken.Unit.Plan.ClassifyPrologueContinue

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

set_option maxRecDepth 4096 in
theorem prologue_tail [Host] [FunDecls]
    (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (hok : c.Ok) (ha : classifyA c s) (t : MachineData)
    (lo : List Word) (w q : Word) (hb : Bd P c F s ra lo w q t)
    (hdi' : t.regs.rdi.toBitVec = P) (hsi' : t.regs.rsi.toBitVec = c.h.mp)
    (hdx' : t.regs.rdx.toBitVec = c.h.dn) (hcx' : t.regs.rcx.toBitVec = rcx s) :
    WP.wp prologueTail (prologueI P c F s ra (.label ".LB.Planner.classify.0") 2)
      (Program.Intercept (Program.labels classifyAsm) (s.pushRa ra)
        (prologueI P c F s ra) (E P c F s ra)) t := by
  obtain ⟨_, hp⟩ := CView.pv hb.kb.vmem
  have ksrc := PView.isSome_src hp
  have rsrc := PView.rd_src hp
  obtain ⟨_, hsw⟩ := PView.wd_sw hp hok ha.1.2.2
  change (Wd (slotAt c.h.p.src (rcx s).toNat) (sw c s) ∗ _).get t.dmem at hsw
  have kw := Wd.isSome hsw
  have rw := Wd.rd hsw
  have kk := Wd.isSome_byte hsw (j := 4) (by decide)
  have rk := Wd.rdb_byte hsw (j := 4) (by decide)
  have hs := slot_eq c s hok ha
  have hkind := congrArg StackSlot.kind hs
  change (sw c s).extractLsb' 32 8 = (inp c s).slot.kind at hkind
  simp only [Nat.reduceMul, hkind] at rk
  unfold rd at rsrc rw
  unfold rdb at rk
  refine return_prefix t c.h.p.src (sw c s) (inp c s).slot.kind _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [hdi'] using ksrc
  · simpa only [hdi'] using rsrc
  · simpa only [hcx'] using kw
  · simpa only [hcx'] using rw
  · simpa only [hcx'] using kk
  · simpa only [hcx'] using rk
  · exact prologue_return_exit P c F s ra t lo w q hb
  · exact prologue_continue P c F s ra hok ha t lo w q hb hdi' hsi' hdx' hcx'

end Bbu.Unit.ClassifyU
