module

public import BbuKraken.Unit.Plan.PlannerRunFrame
import all BbuKraken.Unit.Plan.PlannerRunFrame

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

-- This is the actual epilogue block. Its caller supplies the model result
-- already established by the preceding blocks.
set_option maxRecDepth 4096 in
theorem b_26 [Host] [FunDecls] (P : Addr) (g g' : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (hok : g'.Ok)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.26" →
      ∀ t, (∃ lo locals, Bd P g' F s ra lo locals t ∧ plannerRunQ g g' s t) →
        WP.wp blk.body K
          (Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I'
            (fun a u => a = ra ∧ VPost PlannerRunView PlannerRunG.Ok P F plannerRunD
              (fun g'' u => plannerRunQ g g'' s u) s u ∧ Sep.mod.Agree s u)) t := by
  cfg_block
  intro t ⟨lo, locals, hb, hq⟩
  let u : MachineData := { t with
    regs := { t.regs with
      rsp := ⟨32968#64 + t.regs.rsp.toBitVec + 48#64⟩
      rbx := ⟨rd t.dmem (32968#64 + t.regs.rsp.toBitVec)⟩
      rbp := ⟨rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 8#64)⟩
      r12 := ⟨rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 16#64)⟩
      r13 := ⟨rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 24#64)⟩
      r14 := ⟨rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 32#64)⟩
      r15 := ⟨rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 40#64)⟩ }
    status := StatusFlags.from_result (32968#64 + t.regs.rsp.toBitVec)
      { cf := ((32968#64 + t.regs.rsp.toBitVec).toNat : Int) !=
          (32968 + (t.regs.rsp.toBitVec.toNat : Int))
        af := (((32968#64 + t.regs.rsp.toBitVec).extractLsb' 0 4).toNat : Int) !=
          (((8 : Nat) : Int) + ((t.regs.rsp.toBitVec.extractLsb' 0 4).toNat : Int))
        of := (32968#64 + t.regs.rsp.toBitVec).signed !=
          (32968#64).signed + t.regs.rsp.toBitVec.signed } }
  have hu : Kg (PlannerRunView P g' ∗ F) s ra (fr s lo locals) u :=
    hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
  have k0 := hb.popSome 0 (by decide)
  have k1 := hb.popSome 1 (by decide)
  have k2 := hb.popSome 2 (by decide)
  have k3 := hb.popSome 3 (by decide)
  have k4 := hb.popSome 4 (by decide)
  have k5 := hb.popSome 5 (by decide)
  simp only [BitVec.add_comm t.regs.rsp.toBitVec (32968#64), BitVec.add_zero,
    Nat.reduceMul, BitVec.add_assoc] at k0 k1 k2 k3 k4 k5
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k0
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | with_reducible exact k5
  | retAddr =>
    apply Option.isSome_iff_exists.mpr
    refine ⟨ra, ?_⟩
    simpa only [u, rd, BitVec.add_assoc] using hu.retAddr
  | ret =>
    have hr := Kg.vret (V := PlannerRunView) (ok := PlannerRunG.Ok) (S := P)
      (a' := g') (F := F) (d := plannerRunD) (s := s) (ra := ra)
      (t := u) (ls := plannerRunAsm.labels) (I' := I')
      (fr := fr s lo locals) (Q := fun g'' u => plannerRunQ g g'' s u) hu
      hb.length hok (fun u _ hax => plannerRunQ_rax (g := g) (g' := g') hq hax)
    refine Eq.mp ?_ hr
    simp only [u, rd, Reg64s.get64_rsp, BitVec.add_assoc, BitVec.reduceAdd]
    rfl

end Bbu.Unit.PlannerRunU
