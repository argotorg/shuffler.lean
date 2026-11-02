module

public import FlatShuffler.Unit.Plan.PlannerRunResolveDefs
import all FlatShuffler.Unit.Plan.PlannerRunResolveDefs
public import FlatShuffler.Unit.Plan.PlannerRunResolveTail
import all FlatShuffler.Unit.Plan.PlannerRunResolveTail

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

set_option maxRecDepth 8192 in
theorem b_30_call [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64) (locals : List Word)
    (hl : locals.length = 4121) (hin : ResolveInputs g M locals hl) (before : Word)
    (hresolve : VSpecWithExit RView RG.Ok Names.resolve resolveA 1182 resolveQ resolveX)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hfinish : ∀ spills dropped res lo' u,
      PostEmitLI P (withResolve g spills dropped) M F s ra lo' locals u →
      Resolved g M locals hl spills dropped res → al u = ResolveU.code res →
      res ≠ .assertionFailed →
      u.regs.rbp.toBitVec = before →
      WP.wp resolveTail K (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) u)
    (hstop : ∀ spills dropped lo' u, lo'.length = 4113 →
      (Stk (rsp s) (fr s lo' locals) ra.toBitVec ∗
        (plannerCallOwnedMemory P (withResolve g spills dropped) ∗ F)).get u.dmem →
      Resolved g M locals hl spills dropped .assertionFailed →
      u.regs.get64 .rdi = 1#64 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label "exit") u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.17" →
      ∀ t, (∃ lo, PostEmitLI P g M F s ra lo locals t) →
        t.regs.rbp.toBitVec = before → WP.wp blk.body K
          (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  simp only [Names.resolve] at hresolve
  cfg_block
  intro t ⟨lo, h⟩ hbp
  let off := resolveOffset locals hl
  let ex := resolveExcess locals hl
  have kro := h.localSome (i := 4116) (by decide)
  have ro : FlatShuffler.rd t.dmem (t.regs.rsp.toBitVec + 32928#64) = off :=
    h.localRead (i := 4116) (by decide)
  have kre := h.localSome (i := 4117) (by decide)
  have re : FlatShuffler.rd t.dmem (t.regs.rsp.toBitVec + 32936#64) = ex :=
    h.localRead (i := 4117) (by decide)
  have krs := h.localSome (i := 2064) (by decide)
  have rs : FlatShuffler.rd t.dmem (t.regs.rsp.toBitVec + 16512#64) = resolveSize locals hl :=
    h.localRead (i := 2064) (by decide)
  simp only [Nat.reduceMul] at kro kre krs
  unfold FlatShuffler.rd at ro re rs
  kvcgen64 [hresolve]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [ro, re, rs] at ⊢
  vc_by_shape
  | load => simp only [kro, kre, krs]
  | other =>
    let y : MachineData := {t with regs := {t.regs with
      r12 := .ofBitVec off, r13 := .ofBitVec ex,
      rsi := .ofBitVec (t.regs.rsp.toBitVec + 96#64),
      r9 := .ofBitVec (resolveSize locals hl),
      r8 := .ofBitVec (t.regs.rsp.toBitVec + 16536#64),
      rdx := .ofBitVec off, rcx := .ofBitVec ex, rdi := t.regs.rbx}}
    have hy : PostEmitLI P g M F s ra lo locals y := by
      apply h.next
      all_goals rfl
    refine hy.toBd.callResolve ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hy.mappingEq]
      exact plannerResolve_ok h.ok _ _ hin.mapping
    · exact h.rbx
    · refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
      · exact hin.size
      · exact hin.offset
      · exact hin.excess
      · exact hin.current
    · intro r' u hq
      have hr := (hq ⟨Vector.replicate maxStackSize 0#8, Vector.replicate maxStackSize 0#64⟩).2.1
      rw [hr]
      rfl
    · intro r' u hq
      have hr := (hq ⟨Vector.replicate maxStackSize 0#8, Vector.replicate maxStackSize 0#64⟩).2
      rw [hr]
      rfl
    · intro spills dropped u lo' hb hq hag
      have hp := hy.afterResolve spills dropped hb hag
      obtain ⟨res, hal, hnormal, hmodel⟩ := resolved_of_resolveQ hq
      apply hfinish spills dropped res lo' u hp ?_ hal hnormal ?_
      · simp only [plannerResolve, hy.mappingEq] at hmodel
        exact hmodel
      · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]
        exact hbp
    · intro spills dropped u lo' hlo hmem hx harg
      apply hstop spills dropped lo' u hlo hmem
      · have hmodel := resolved_of_resolveX hx
        simp only [plannerResolve, hy.mappingEq] at hmodel
        exact hmodel
      · exact harg

theorem b_30 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64) (locals : List Word)
    (hl : locals.length = 4121) (hin : ResolveInputs g M locals hl) (before : Word)
    (hresolve : VSpecWithExit RView RG.Ok Names.resolve resolveA 1182 resolveQ resolveX)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hbad : ∀ spills dropped res lo' u,
      Resolved g M locals hl spills dropped res →
      PostEmitLI P (withResolve g spills dropped) M F s ra lo' locals u →
      res = .stuck → al u = ResolveU.code res →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.12") u)
    (hzero : ∀ spills dropped res lo' u,
      Resolved g M locals hl spills dropped res →
      PostEmitLI P (withResolve g spills dropped) M F s ra lo' locals u →
      res = .dropped → g.p.sourceSize = 0#64 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.13") u)
    (hmore : ∀ spills dropped res lo' u,
      Resolved g M locals hl spills dropped res →
      PostEmitLI P (withResolve g spills dropped) M F s ra lo' locals u →
      res = .dropped → g.p.sourceSize ≠ 0#64 → u.regs.rbp.toBitVec = before →
      rax u = g.p.drp → rcx u = g.p.drp + g.p.sourceSize → rdx u = 0#64 → K () u)
    (hstop : ∀ spills dropped lo' u, lo'.length = 4113 →
      (Stk (rsp s) (fr s lo' locals) ra.toBitVec ∗
        (plannerCallOwnedMemory P (withResolve g spills dropped) ∗ F)).get u.dmem →
      Resolved g M locals hl spills dropped .assertionFailed →
      u.regs.get64 .rdi = 1#64 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label "exit") u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.17" →
      ∀ t, (∃ lo, PostEmitLI P g M F s ra lo locals t) →
        t.regs.rbp.toBitVec = before → WP.wp blk.body K
          (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  refine b_30_call P g M F s ra locals hl hin before hresolve K I' E ?_ hstop
  intro spills dropped res lo' u h hmodel hal hnormal hbp
  apply resolve_tail P (withResolve g spills dropped) M F s ra lo'
    locals u res before h hal hnormal hbp K I' E
  · intro v hv hres ha
    exact hbad spills dropped res lo' v hmodel hv hres ha
  · intro v hv hres hm
    exact hzero spills dropped res lo' v hmodel hv hres hm
  · intro v hv hres hm hb ha hc hd
    exact hmore spills dropped res lo' v hmodel hv hres hm hb ha hc hd

end FlatShuffler.Unit.PlannerRunU
