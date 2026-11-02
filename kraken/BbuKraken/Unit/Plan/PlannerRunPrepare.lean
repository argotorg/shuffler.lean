module

public import BbuKraken.Unit.Plan.PlannerRunCheckDefs
import all BbuKraken.Unit.Plan.PlannerRunCheckDefs
public import BbuKraken.Unit.Plan.PlannerRunStore
import all BbuKraken.Unit.Plan.PlannerRunStore

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU

def PrepareHead (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, LoopLI P g F s ra lo locals t ∧
    t.regs.r15.toBitVec = t.regs.rsp.toBitVec + 32#64 ∧
    locals[3]? = some g.countPtr ∧ Flat.targetsFrom g.p.fl g.spills 0 = true

set_option maxRecDepth 4096 in
theorem b_4 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hprepare : ∀ t, PrepareHead P g F s ra t →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.19") t) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.5" →
      ∀ t, CheckDone P g F s ra t → WP.wp blk.body K
        (Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hc, htgt⟩
  let u : MachineData := { t with
    dmem := t.dmem.storeInt (t.regs.rsp.toBitVec + 16#64) 8 g.sourcesPtr.toInt }
  have hs : Bd P g F s ra lo (locals.set 2 g.sourcesPtr) u :=
    hc.toBd.storeLocal (i := 2) (by decide) g.sourcesPtr rfl rfl
  have ksrc := hc.localSome (i := 2) (by decide)
  have kcount := hs.localSome (i := 3) (by decide)
  simp only [u, Nat.reduceMul] at ksrc kcount
  have hsrc := hc.sources
  simp only [r8, Reg64s.get64_r8] at hsrc
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hsrc, hc.rbp] at ⊢
  vc_by_shape
  | load => simp only [ksrc, kcount]
  | goto ".LB.Planner.run.19" =>
    apply hprepare
    refine ⟨lo, (locals.set 2 g.sourcesPtr).set 3 g.countPtr, ?_, rfl, ?_, htgt⟩
    · refine ⟨hs.storeLocal (i := 3) (by decide) g.countPtr rfl rfl,
        hc.rbx, hc.r14, ?_, ?_, ?_⟩
      · simpa only [List.getElem?_set, show ¬ (3 = 1) by decide,
          show ¬ (2 = 1) by decide, ↓reduceIte] using hc.ops
      · simpa only [List.getElem?_set, show ¬ (3 = 0) by decide,
          show ¬ (2 = 0) by decide, ↓reduceIte] using hc.strategy
      · simp only [List.getElem?_set, show ¬ (3 = 2) by decide,
          hc.localLength, show (2 : Nat) < 4121 by decide, ↓reduceIte]
    · exact List.getElem?_set_self (by rw [hs.localLength]; decide)

end Bbu.Unit.PlannerRunU
