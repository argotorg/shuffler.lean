module

public import FlatShuffler.Unit.Plan.PlannerRunRead
import all FlatShuffler.Unit.Plan.PlannerRunRead
public import FlatShuffler.Unit.Plan.PlannerRunValidate
import all FlatShuffler.Unit.Plan.PlannerRunValidate

public import FlatShuffler.Unit.Memory
import all FlatShuffler.Unit.Memory

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

private theorem low8 (w : Word) : w.extractLsb' 0 8 = w.setWidth 8 := by bv_decide

set_option maxRecDepth 4096 in
theorem b_3 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s t : MachineData) (ra : Int64) (hok : g.Ok) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rcx u = rcx t → CheckNext P g F s ra u →
      Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E
        (label ".LB.Planner.run.0") u)
    (hbad : ∀ u, rcx u = rcx t → CheckBad P g F s ra u →
      Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E
        (label ".LB.Planner.run.4") u)
    (hfall : ∀ u, rcx u = rcx t → CheckBad P g F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.3" →
      CheckMissing P g F s ra t → WP.wp blk.body K
        (Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, he, hkind, hfree, hcontains⟩
  have hv := hc.kb.mem
  rw [sep_lc] at hv
  obtain ⟨_, hp⟩ := target_payload hv hok hi
  have hpay := rd32_b32 hp
  have kpay := B32.isSome hp
  have hptr := spill_pointer hv
  have kptr := spill_pointer_some hv
  simp only [rcx, rsi, Reg64s.get64_rcx, Reg64s.get64_rsi] at hpay kpay hkind
  have hspill : ∀ hk : (Flat.get g.p.fl.target (rcx t)).kind = 0#8,
      ∃ R, (B8 (g.p.spl + BitVec.ofNat 64 (Flat.get g.p.fl.target (rcx t)).payload.toNat)
        (g.spills (Flat.get g.p.fl.target (rcx t)).payload) ∗ R).get t.dmem :=
    fun hk => target_spill hv hok hi (variable_of_not_generated hfree hk)
  unfold rd at hptr
  clear hp hv
  kvcgen64 [movl_idx8_spec]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hc.r10, hc.rbx, fold_slot, hpay, hptr] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact kpay
    | with_reducible exact kptr
    | (rename_i af hz
       symexec_norm at hz
       have hk : (Flat.get g.p.fl.target (rcx t)).kind = 0#8 := by
         simpa only [rcx, Reg64s.get64_rcx, low8, hkind, BitVec.and_self, BitVec.zero_eq,
           Bool.not_eq_false', beq_iff_eq] using hz
       obtain ⟨_, hs⟩ := hspill hk
       simpa only [rcx, Reg64s.get64_rcx, BitVec.ofNat_toNat] using B8.isSome hs)
  | goto ".LB.Planner.run.4" =>
    rename_i hz
    symexec_norm at hz
    have hk : (Flat.get g.p.fl.target (rcx t)).kind ≠ 0#8 := by
      simpa only [rcx, Reg64s.get64_rcx, low8, hkind, BitVec.and_self, BitVec.zero_eq,
        Bool.not_eq_true', beq_eq_false_iff_ne] using hz
    apply hbad
    · rfl
    refine ⟨lo, locals, hc.toEarlyLI.next rfl rfl rfl rfl rfl rfl rfl, ?_⟩
    rw [he]
    exact target_missing_bad hi hfree hcontains (spill_false_of_kind hk)
  | goto ".LB.Planner.run.0" =>
    rename_i hz hsp
    symexec_norm at hz hsp
    have hk : (Flat.get g.p.fl.target (rcx t)).kind = 0#8 := by
      simpa only [rcx, Reg64s.get64_rcx, low8, hkind, BitVec.and_self, BitVec.zero_eq,
        Bool.not_eq_false', beq_iff_eq] using hz
    obtain ⟨_, hs⟩ := hspill hk
    have hb := B8.rdb hs
    unfold rdb at hb
    simp only [Reg64s.get64_rcx, BitVec.ofNat_toNat] at hb
    simp only [hc.r10, hc.rbx, fold_slot, hpay, hptr, hb, BitVec.sub_zero,
      BitVec.zero_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hsp
    apply hnext
    · rfl
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl, hi, ?_⟩
    rw [he]
    apply targets_next hi
    have hvar := variable_of_not_generated hfree hk
    have hsp' : Flat.spillIsSpilled g.spills (Flat.get g.p.fl.target (rcx t)) = true := by
      simp only [Flat.spillIsSpilled, hvar, Bool.true_and, bne_iff_ne]
      exact hsp
    simp only [hfree, hsp', Bool.false_or, Bool.or_true]
  | other =>
    rename_i hz hsp
    symexec_norm at hz hsp
    have hk : (Flat.get g.p.fl.target (rcx t)).kind = 0#8 := by
      simpa only [rcx, Reg64s.get64_rcx, low8, hkind, BitVec.and_self, BitVec.zero_eq,
        Bool.not_eq_false', beq_iff_eq] using hz
    obtain ⟨_, hs⟩ := hspill hk
    have hb := B8.rdb hs
    unfold rdb at hb
    simp only [Reg64s.get64_rcx, BitVec.ofNat_toNat] at hb
    simp only [hc.r10, hc.rbx, fold_slot, hpay, hptr, hb, BitVec.sub_zero,
      BitVec.zero_eq, Bool.not_eq_false', beq_iff_eq] at hsp
    apply hfall
    · rfl
    · refine ⟨lo, locals, hc.toEarlyLI.next rfl rfl rfl rfl rfl rfl rfl, ?_⟩
      rw [he]
      apply target_missing_bad hi hfree hcontains
      simp [Flat.spillIsSpilled, Reg64s.get64_rcx, hsp]

end FlatShuffler.Unit.PlannerRunU
