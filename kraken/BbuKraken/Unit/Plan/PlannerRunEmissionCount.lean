module

public import BbuKraken.Unit.Plan.PlannerRunEmissionDefs
import all BbuKraken.Unit.Plan.PlannerRunEmissionDefs
public import BbuKraken.Unit.Run.Model
import all BbuKraken.Unit.Run.Model

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Flat Bbu.Sep

private theorem pos_addr (sp i : Word) :
    sp + 16480#64 + i * 8#64 + 8248#64 =
      sp + BitVec.ofNat 64 (8 * (3091 + i.toNat)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

set_option maxRecDepth 4096 in
theorem b_15 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64) (hok : g.Ok)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rax u = rax t → EmitCountNext P g M F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.14") u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.15" →
      EmitCountHead P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, j, c, hc, hj, hax, hdx, hp, hmodel⟩
  have hjN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) hok.planner.n
  have hidx : 3091 + j.toNat < 4121 := by change j.toNat < 1024 at hjN; omega
  have hr := hc.localRead hidx
  have he := hc.pos j.toNat (BitVec.lt_def.mp hj)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at he
  rw [List.getElem?_eq_getElem (hc.localLength ▸ hidx)] at he
  replace hr := hr.trans (Option.some.inj he)
  have hpread := hc.localRead (i := 4115) (by decide)
  rw [List.getElem?_eq_getElem (by rw [hc.localLength]; decide)] at hp
  replace hpread := hpread.trans (Option.some.inj hp)
  have hax' : t.regs.rax.toBitVec = t.regs.rsp.toBitVec + 16480#64 + j * 8#64 := hax
  have kpos := hc.localSome hidx
  have kpend := hc.localSome (i := 4115) (by decide)
  unfold rd at hr hpread
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hax', pos_addr, hr, hpread] at ⊢
  vc_by_shape
  | load =>
    simp only [kpos, kpend]
  | goto ".LB.Planner.run.14" =>
    first
    | (rename_i hne
       symexec_norm at hne
       simp only [hax', pos_addr, hr, sub_beq_zero, Bool.not_eq_true', Bool.not_eq_false',
         beq_eq_false_iff_ne, beq_iff_eq] at hne
       change get M.pos j ≠ NONE at hne
       apply hnext
       · rfl
       refine ⟨lo, locals, j, c, hc.next rfl rfl rfl rfl rfl rfl rfl rfl,
         hj, hax, hdx, ?_, ?_⟩
       · exact List.getElem?_eq_getElem _ |>.trans (congrArg some (Option.some.inj hp))
       · rw [RunU.unmapped_step hj] at hmodel
         simp only [show (countState g M).pos = M.pos from rfl, hne] at hmodel
         exact hmodel)
    | (rename_i heq
       symexec_norm at heq
       simp only [hax', pos_addr, hr, sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at heq
       change get M.pos j = NONE at heq
       apply hnext
       · rfl
       refine ⟨lo, locals.set 4115 (1#64 + c), j, 1#64 + c,
         hc.storePending hok (1#64 + c) ?_ rfl rfl rfl rfl rfl rfl rfl,
         hj, hax, hdx, ?_, ?_⟩
       · rfl
       · exact List.getElem?_set_self (by rw [hc.localLength]; decide)
       · rw [RunU.unmapped_step hj] at hmodel
         simp only [show (countState g M).pos = M.pos from rfl, heq, ite_eq_left] at hmodel
         simpa only [BitVec.add_comm c 1#64] using hmodel)

end Bbu.Unit.PlannerRunU
