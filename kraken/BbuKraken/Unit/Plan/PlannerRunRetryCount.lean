module

public import BbuKraken.Unit.Plan.PlannerRunRetryDefs
import all BbuKraken.Unit.Plan.PlannerRunRetryDefs
public import BbuKraken.Unit.Plan.PlannerRunRetrySpec
import all BbuKraken.Unit.Plan.PlannerRunRetrySpec

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

def byteCount (c : Word) (b : BitVec 8) : Word := if b = 0#8 then c else c + 1#64

theorem count_byte (c : Word) (b : BitVec 8) :
    c - 18446744073709551615#64 - BitVec.ofNat 64
      (((b - 1#8).toNat : Int) != (b.toNat : Int) - 1).toNat = byteCount c b := by
  rw [Idioms.cf_sub_imm b 1 (by decide)]
  by_cases hb : b = 0#8
  · simp [hb, byteCount]
    bv_omega
  · have hn : ¬ b.toNat < 1 := by bv_omega
    simp [hn, byteCount, hb]
    bv_omega

theorem dropped_step {m i c : Word} {d : Vector (BitVec 8) MAX_N} (hi : i < m) :
    Flat.droppedFrom m d i c = Flat.droppedFrom m d (i + 1#64) (byteCount c (get d i)) := by
  by_cases hz : get d i = 0#8
  · rw [byteCount, ite_eq_left hz]
    exact dropped_zero hi hz
  · rw [byteCount, ite_eq_right hz]
    exact dropped_nonzero hi hz

set_option maxRecDepth 4096 in
theorem b_29 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hloop : ∀ u, DropBeforeHead P g M F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.29") u)
    (hdone : ∀ u, ResolveHead P g M F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.29" →
      ∀ t, DropBeforeHead P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, i, h, hi, hax, hdx, hmodel⟩
  have hiN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) h.ok.planner.m
  obtain ⟨R, hb⟩ := dropped_read h.kb.vmem hiN (BitVec.lt_def.mp hi)
  have ks := B8.isSome hb
  have rd := B8.rdb hb
  unfold rdb at rd
  have hax' : t.regs.rax.toBitVec = g.p.drp + i := hax
  have hdx' : t.regs.rdx.toBitVec = g.p.drp + g.p.m := hdx
  have hmodel' := (dropped_step hi).symm.trans hmodel
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hax', rd, count_byte] at ⊢
  vc_by_shape
  | load => exact ks
  | goto ".LB.Planner.run.29" =>
    rename_i hj
    symexec_norm at hj
    simp only [hax', hdx', BitVec.zero_eq,
      Bool.not_eq_true', beq_eq_false_iff_ne] at hj
    have hne : i + 1#64 ≠ g.p.m := by intro he; apply hj; bv_omega
    have hin : i + 1#64 < g.p.m := by bv_omega
    apply hloop
    refine ⟨lo, locals, i + 1#64, ?_, hin, ?_, hdx, hmodel'⟩
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · change 1#64 + (g.p.drp + i) = g.p.drp + (i + 1#64)
      bv_omega
  | other =>
    rename_i hj
    symexec_norm at hj
    simp only [hax', hdx', BitVec.zero_eq,
      Bool.not_eq_false', beq_iff_eq] at hj
    have he : i + 1#64 = g.p.m := by bv_omega
    apply hdone
    refine ⟨lo, locals, ?_, ?_⟩
    · exact h.next rfl rfl rfl rfl rfl rfl rfl
    · have hend := dropped_end (m := g.p.m) (d := g.dropped)
        (i := i + 1#64) (count := byteCount t.regs.rbp.toBitVec (get g.dropped i)) (by bv_omega)
      exact hend.symm.trans hmodel'

end Bbu.Unit.PlannerRunU
