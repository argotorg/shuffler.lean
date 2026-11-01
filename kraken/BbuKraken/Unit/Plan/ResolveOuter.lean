module

public import BbuKraken.Unit.Plan.ResolveChoose
import all BbuKraken.Unit.Plan.ResolveChoose
public import BbuKraken.Unit.Plan.ResolveCursor
import all BbuKraken.Unit.Plan.ResolveCursor
public import BbuKraken.Unit.Plan.ResolveWorkModel
import all BbuKraken.Unit.Plan.ResolveWorkModel

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU
open Bbu.Sep

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {w : Work} {lo : List Word} {L : Lc}

theorem outer_start (h : Core P r F s ra w lo L t) (hm : w.Model r s)
    (hc : w.count ≠ 0#64)
    (hmem : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 23#64) 1 0)
    (hsp : u.regs.rsp = t.regs.rsp) (h12 : u.regs.r12 = t.regs.r12)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13)
    (h15 : u.regs.r15.toBitVec = Flat.NONE)
    (hbx : u.regs.rbx.toBitVec = t.regs.rsp.toBitVec + 48#64) : Pick P r F s ra u := by
  obtain ⟨v, hbu, hcls⟩ := h.bd.storeClass 0 hmem hsp
  refine ⟨w, lo, { L with classWord := v }, 0, Flat.NONE, 0,
    ⟨h.withClass hbu hsp h12 h14 h13, by bv_omega, ?_, h15,
      hcls, Or.inl rfl⟩, hm, rfl⟩
  rw [hbx, hsp]
  bv_omega

end

section
variable [Host] [FunDecls]
  (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
  (hok : r.Ok)

include hok

theorem b_8 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.8" →
      Obl P r F s ra (loopPhase P r F s ra rest) (loopVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte, Outer] at ht
  obtain ⟨w, lo, L, h, hm⟩ := ht
  obtain ⟨R, hmc⟩ := h.bd.typedWord 5 (by decide)
  have hsome := Wd.isSome hmc
  have hrc := Wd.rd hmc
  change rd t.dmem (t.regs.rsp.toBitVec + 40#64) = L.count at hrc
  have hcs := h.bd.classSome
  have hcount := h.ok.count
  have hd := cursor_distance t.regs.rsp.toBitVec w.count 0 h.ok.count (by bv_omega)
  symexec_norm at hd
  simp only [BitVec.mul_zero, BitVec.add_zero, Nat.sub_zero] at hd
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => first | with_reducible exact hsome | exact hcs
  | goto ".LB.Planner.resolve.16" =>
    rename_i hj
    symexec_norm at hj
    have hc : w.count = 0#64 := by
      have hh : rd t.dmem (t.regs.rsp.toBitVec + 40#64) = 0#64 := by
        simpa only [rd, BitVec.sub_zero, beq_iff_eq, BitVec.zero_eq] using hj
      rw [hrc, h.count] at hh
      exact hh
    cfg_goto
    · exact h.bd.kb.stack (by decide)
    · simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Return]
      exact ⟨w.ghost r, lo, L.toList, h.bd.next rfl rfl,
        update_ok hok w.spills w.dropped, Work.empty h.ok hm hc⟩
    · left; simp [V, loopVar]
  | goto ".LB.Planner.resolve.12" =>
    rename_i hj
    symexec_norm at hj
    have hc : w.count ≠ 0#64 := by
      intro he
      have hr : rd t.dmem (t.regs.rsp.toBitVec + 40#64) = 0#64 := hrc.trans (h.count.trans he)
      change (rd t.dmem (t.regs.rsp.toBitVec + 40#64) - 0#64 == BitVec.zero 64) = false at hj
      rw [hr] at hj
      change true = false at hj
      cases hj
    cfg_goto
    · exact h.bd.kb.stack (by decide)
    · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
      exact outer_start h hm hc rfl rfl rfl rfl rfl rfl rfl
    · left
      simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
      symexec_norm at ⊢
      rw [rd_store_class, h.r13, hd]
      change w.count.toNat ≤ 1024 at hcount
      omega

end
end Bbu.Unit.ResolveU
