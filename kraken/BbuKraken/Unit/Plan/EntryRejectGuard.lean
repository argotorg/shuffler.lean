module

public import BbuKraken.Unit.Plan.EntryReject
import all BbuKraken.Unit.Plan.EntryReject
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.EntryU
open Bbu.Sep

private theorem frame88 (x : Word) : x - 8#64 - 8#64 - 80#64 = x - 8#64 - 88#64 := by
  bv_omega

private theorem arg96 (x : Word) : x - 8#64 - 8#64 - 80#64 + 96#64 = x := by bv_omega
private theorem arg104 (x : Word) : x - 8#64 - 8#64 - 80#64 + 104#64 = x + 8#64 := by bv_omega

private theorem low8_widen_extract (w : BitVec 32) :
    (w.setWidth 64).extractLsb' 0 8 = w.setWidth 8 := by
  simpa only [BitVec.take] using low8_widen w

section
variable [Host] [FunDecls] (a b : BitVec 32) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_fn (hp : RejectPre a b F s) : planAsm.ForallBlocks fun blk =>
    blk.label = .label Names.plan → Obl a b F s ra blk := by
  cfg_block [Obl, Names.plan]
  intro t ht
  simp only [Inv, Names.plan, ↓reduceIte] at ht
  subst t
  obtain ⟨hg, fr, v, hl, hm⟩ := hp
  have hk := Kg.init (ra := ra) hm
  have hx := hk.pushes (xs := [s.regs.rbx.toBitVec]) (by simp [hl])
  have hh := hx.2
  simp only [List.length_singleton, List.reverse_singleton] at hh
  obtain ⟨R, he⟩ : ∃ R, Stk (rsp s) (fr.take (fr.length - 1) ++ [s.regs.rbx.toBitVec])
      ra.toBitVec ∗ Args s a b F = B32 (rsp s) a ∗ R := ⟨_, by unfold Args; ecancel⟩
  have ha := b32_read (he ▸ hh)
  have ka := B32.isSome (he ▸ hh)
  obtain ⟨R', he'⟩ : ∃ R', Stk (rsp s) (fr.take (fr.length - 1) ++ [s.regs.rbx.toBitVec])
      ra.toBitVec ∗ Args s a b F = B32 (rsp s + 8#64) b ∗ R' := ⟨_, by unfold Args; ecancel⟩
  have hb := b32_read (he' ▸ hh)
  have kb := B32.isSome (he' ▸ hh)
  have kp := hx.1.1
  simp only [pushes] at hh ha ka hb kb
  have h96 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 80#64 + 96#64 = rsp s := by
    exact arg96 (rsp s)
  have h104 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 80#64 + 104#64 = rsp s + 8#64 := by
    exact arg104 (rsp s)
  have hbx : (s.pushRa ra).regs.rbx = s.regs.rbx := rfl
  have hlo : (fr.take (fr.length - 1)).length = 10 := by simp [hl]
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [h96, h104, hbx, ha, hb] at ⊢
  vc_by_shape
  | load =>
    first
    | (guard_target =ₛ (Mem.loadInt (s.pushRa ra).dmem
        ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8).isSome = true
       exact kp)
    | (guard_target =ₛ (Mem.loadInt
        (Mem.storeInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rsp.toBitVec - 8#64)
          8 s.regs.rbx.toBitVec.toInt) (s.regs.get64 Reg64.rsp) 4).isSome = true
       exact ka)
    | exact kb
  | goto ".LB.plan.12" =>
    cfg_goto
    · refine Kb.stack (P := Args s a b F)
        (fr := fr.take (fr.length - 1) ++ [s.regs.rbx.toBitVec]) (d := 88#64) ?_ (by decide)
      exact ⟨hh, frame88 (rsp s)⟩
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte, true_or]
      refine ⟨_, ⟨⟨hh, ?_⟩, hlo, rfl, rfl, rfl, rfl, rfl⟩⟩
      exact frame88 (rsp s)
    · left; simp [V, Names.plan]
  | goto ".LB.plan.13" =>
    cfg_goto
    · refine Kb.stack (P := Args s a b F)
        (fr := fr.take (fr.length - 1) ++ [s.regs.rbx.toBitVec]) (d := 88#64) ?_ (by decide)
      exact ⟨hh, frame88 (rsp s)⟩
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte, or_true]
      refine ⟨_, ⟨⟨hh, ?_⟩, hlo, rfl, rfl, rfl, rfl, rfl⟩⟩
      exact frame88 (rsp s)
    · left; simp [V, Names.plan]
  | goto ".LB.plan.14" =>
    rename_i hm hn af he af' hz
    rw [MachineData.status_mk, Idioms.cmp_a_imm _ 1024 (by decide)] at hm hn
    rw [MachineData.status_mk, Idioms.cmp_a_imm _ 1 (by decide)] at he
    symexec_norm at he
    simp only [h96, h104, hbx, ha, hb, low8_widen_extract, decide_eq_false_iff_not] at he
    simp only [decide_eq_false_iff_not] at hm hn
    change ¬ 1024 < (rdi s).toNat at hm
    change ¬ 1024 < (rsi s).toNat at hn
    have henum : ¬ (1 < (b.setWidth 8).toNat ∨ 1 < (a.setWidth 8).toNat) :=
      fun h => he ((bad_or b a).mpr h)
    exact False.elim (hg.elim hm (fun h => h.elim hn
      (fun h => henum (h.elim Or.inr Or.inl))))
  | goto ".LB.plan.1" =>
    rename_i hm hn af he af' hz
    rw [MachineData.status_mk, Idioms.cmp_a_imm _ 1024 (by decide)] at hm hn
    rw [MachineData.status_mk, Idioms.cmp_a_imm _ 1 (by decide)] at he
    symexec_norm at he
    simp only [h96, h104, hbx, ha, hb, low8_widen_extract, decide_eq_false_iff_not] at he
    simp only [decide_eq_false_iff_not] at hm hn
    change ¬ 1024 < (rdi s).toNat at hm
    change ¬ 1024 < (rsi s).toNat at hn
    have henum : ¬ (1 < (b.setWidth 8).toNat ∨ 1 < (a.setWidth 8).toNat) :=
      fun h => he ((bad_or b a).mpr h)
    exact False.elim (hg.elim hm (fun h => h.elim hn
      (fun h => henum (h.elim Or.inr Or.inl))))

end
end Bbu.Unit.EntryU
