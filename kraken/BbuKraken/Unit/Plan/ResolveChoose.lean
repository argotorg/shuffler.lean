module

public import BbuKraken.Unit.Plan.ResolveClassByte
import all BbuKraken.Unit.Plan.ResolveClassByte

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem rd_store_class (m : Mem 64) (sp : Addr) (z : Int) :
    rd (m.storeInt (sp + 23#64) 1 z) (sp + 32#64) = rd m (sp + 32#64) := by
  rw [rd, rd, Mem.loadInt_congr (m' := m)]
  intro i hi
  apply Mem.get?_storeInt_of_ne
  intro j hj
  bv_omega

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {w : Work} {lo : List Word} {L : Lc} {i best : Word} {cls : BitVec 8}

theorem pending_commit (h : Core P r F s ra w lo L t) (hi : i < w.count)
    (hbx : t.regs.rbx.toBitVec = t.regs.rsp.toBitVec + 48#64 + 8#64 * i)
    (hp : L.pending = best) (ha : al t = cls)
    (hv : BestValid r.p.fl w.spills r.M w.droppedNow best cls)
    (hm : w.Model r s) (heq : PickEq r w (i + 1) best cls)
    (hmem : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 23#64) 1 (al t).toInt)
    (hsp : u.regs.rsp = t.regs.rsp) (h12 : u.regs.r12 = t.regs.r12)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13)
    (h15 : u.regs.r15.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64))
    (hbxu : u.regs.rbx = t.regs.rbx) : PickNext P r F s ra u := by
  obtain ⟨v, hbu, hcls⟩ := h.bd.storeClass (al t).toInt hmem hsp
  obtain ⟨R, hmp⟩ := h.bd.typedWord 1 (by decide)
  have hr := Wd.rd hmp
  change rd t.dmem (t.regs.rsp.toBitVec + 8#64) = L.pending at hr
  refine ⟨w, lo, { L with classWord := v }, i, best, cls,
    ⟨h.withClass hbu hsp h12 h14 h13, hi, ?_, h15.trans (hr.trans hp),
      ?_, hv⟩, hm, heq⟩
  · rw [hbxu, hsp]
    exact hbx
  · exact hcls.trans (BitVec.ofInt_toInt.trans ha)

end

section
variable [Host] [FunDecls]
  (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)

theorem b_10 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.10" →
      Obl P r F s ra (loopPhase P r F s ra rest) (loopVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte, Pending] at ht
  obtain ⟨w, lo, L, i, best, cls, h, hi, hbx, hp, ha, hv, hm, heq⟩ := ht
  obtain ⟨R, hmp⟩ := h.bd.typedWord 1 (by decide)
  have hs := Wd.isSome hmp
  have hcs := h.bd.classSome
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => first | with_reducible exact hs | exact hcs
  | other =>
    first
    | (simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
       apply pending_commit h hi hbx hp ha hv hm heq
       · simp only [al, rax, Reg64s.get64_rax,
           BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
       all_goals rfl)
    | (left
       simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
       symexec_norm at ⊢
       rw [rd_store_class]
       omega)

end
end Bbu.Unit.ResolveU
