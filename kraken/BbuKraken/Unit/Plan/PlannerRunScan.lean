module

public import BbuKraken.Unit.Plan.PlannerRunScanDefs
import all BbuKraken.Unit.Plan.PlannerRunScanDefs
public import BbuKraken.Unit.Plan.PlannerRunMem
import all BbuKraken.Unit.Plan.PlannerRunMem
public import BbuKraken.Unit.ShallowestCopy
import all BbuKraken.Unit.ShallowestCopy
public import BbuKraken.Specs
import all BbuKraken.Specs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

private theorem add1 (i : Word) : 1#64 + i = i + 1 := by bv_omega

set_option maxRecDepth 4096 in
theorem b_2 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s t : MachineData) (ra : Int64) (hok : g.Ok) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rcx u = rcx t → CheckNext P g F s ra u →
      Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E
        (label ".LB.Planner.run.0") u)
    (hscan : ∀ u, rcx u = rcx t → rax u = 1#64 + rax t → CheckScan P g F s ra u →
      Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E
        (label ".LB.Planner.run.2") u)
    (hmissing : ∀ u, rcx u = rcx t → CheckMissing P g F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.2" →
      CheckScan P g F s ra t → WP.wp blk.body K
        (Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, he, hkind, hfree, hm, hsrc, hslot, hj, hcontains⟩
  have hv := hc.kb.mem
  rw [sep_lc] at hv
  obtain ⟨_, hp⟩ := pv hv
  have hword := PView.rd_sw hp hok.planner (BitVec.lt_def.mp hj)
  have kword := PView.isSome_sw hp hok.planner (BitVec.lt_def.mp hj)
  simp only [rax, rcx, r9, rdi, Reg64s.get64_rax, Reg64s.get64_rcx,
    Reg64s.get64_r9, Reg64s.get64_rdi] at hword kword hkind hfree hm hsrc hslot hj hcontains
  unfold rd at hword
  clear hp hv
  kvcgen64 [Program.WP.xor_reg_mem_idx8_spec]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hsrc, fold_slot] at ⊢
  vc_by_shape
  | load => with_reducible exact kword
  | goto ".LB.Planner.run.0" =>
    rename_i hmatch
    symexec_norm at hmatch
    have hs := hmatch
    simp only [hsrc, fold_slot, ShallowestCopy.shl_xor_beq, decide_eq_true_eq] at hs
    rw [hword, hslot] at hs
    apply hnext
    · rfl
    refine ⟨lo, locals, ?_, ?_, ?_⟩
    · exact hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · simp only [rcx, Reg64s.get64_rcx]
      exact hi
    have hfound := hcontains.trans (contains_found hj hs.symm)
    simp only [rcx, Reg64s.get64_rcx]
    exact he.trans (targets_next (pl := g.p.fl) (sp := g.spills)
      (j := t.regs.rcx.toBitVec) hi (by
        change (_ || _ || Flat.containsFrom g.p.fl.source g.p.m
          (Flat.get g.p.fl.target t.regs.rcx.toBitVec) 0 || _) = true
        simp only [hfound, Bool.or_true, Bool.true_or]))
  | goto ".LB.Planner.run.2" =>
    rename_i hmatch heq
    symexec_norm at hmatch
    have hs := hmatch
    simp only [hsrc, fold_slot, ShallowestCopy.shl_xor_beq, decide_eq_false_iff_not] at hs
    rw [hword, hslot] at hs
    symexec_norm at heq
    simp only [sub_beq_zero, hm, Bool.not_eq_true', beq_eq_false_iff_ne] at heq
    apply hscan
    · rfl
    · rfl
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl, hi,
      he, hkind, hfree, hm, hsrc, hslot, succ_lt hj ?_, ?_⟩
    · exact Ne.symm heq
    · simp only [rcx, rax, Reg64s.get64_rcx, Reg64s.get64_rax]
      rw [add1]
      exact hcontains.trans (contains_next hj (Ne.symm hs))
  | other =>
    rename_i hmatch heq
    symexec_norm at hmatch
    have hs := hmatch
    simp only [hsrc, fold_slot, ShallowestCopy.shl_xor_beq, decide_eq_false_iff_not] at hs
    rw [hword, hslot] at hs
    symexec_norm at heq
    simp only [sub_beq_zero, hm, Bool.not_eq_false', beq_iff_eq] at heq
    apply hmissing
    · rfl
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl, hi,
      he, hkind, hfree, ?_⟩
    simp only [rcx, Reg64s.get64_rcx]
    have heq' : t.regs.rax.toBitVec + 1 = g.p.m := (add1 _).symm.trans heq.symm
    exact hcontains.trans ((contains_next hj (Ne.symm hs)).trans
      (contains_end (by rw [heq']; exact BitVec.lt_irrefl _)))
  | closed => decide

end Bbu.Unit.PlannerRunU
