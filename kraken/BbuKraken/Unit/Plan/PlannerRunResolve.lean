import BbuKraken.Unit.Plan.PlannerRunResolveSetup
import BbuKraken.Unit.Plan.PlannerRunResolveTail

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

set_option maxRecDepth 8192 in
theorem b_30_call [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64) (locals : List Word)
    (hl : locals.length = 4121) (hin : ResolveInputs g M locals hl) (before : Word)
    (hresolve : VSpec RView RG.Ok Names.resolve resolveA 1182 resolveQ)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hfinish : ∀ spills dropped res lo' u,
      PostEmitLI P (withResolve g spills dropped) M F s ra lo' (resolveLocals locals hl) u →
      Resolved g M locals hl spills dropped res → al u = ResolveU.code res →
      u.regs.rbp.toBitVec = before →
      WP.wp resolveTail K (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.30" →
      ∀ t, (∃ lo, PostEmitLI P g M F s ra lo locals t) →
        t.regs.rbp.toBitVec = before → WP.wp blk.body K
          (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  simp only [Names.resolve] at hresolve
  cfg_block
  intro t ⟨lo, h⟩ hbp
  let off := resolveOffset locals hl
  let ex := resolveExcess locals hl
  let v : MachineData := {t with dmem := t.dmem.storeInt t.regs.rsp.toBitVec 8 off.toInt}
  have hv : PostEmitLI P g M F s ra lo (locals.set 0 off) v :=
    h.storeFront (by decide) off (by simp [v]) rfl rfl rfl rfl rfl rfl
  let w : MachineData := {v with dmem := v.dmem.storeInt t.regs.rsp.toBitVec 8 off.toInt}
  have hw : PostEmitLI P g M F s ra lo ((locals.set 0 off).set 0 off) w :=
    hv.storeFront (by decide) off (by simp [w, v]) rfl rfl rfl rfl rfl rfl
  let x : MachineData := {w with dmem := (w.dmem.storeInt
    (t.regs.rsp.toBitVec + 8#64) 8 ex.toInt)}
  have hx : PostEmitLI P g M F s ra lo (resolveLocals locals hl) x :=
    hw.storeFront (by decide) ex rfl rfl rfl rfl rfl rfl rfl
  have kro := h.localSome (i := 4116) (by decide)
  have k0 := h.localSome (i := 0) (by decide)
  have k1 := hw.localSome (i := 1) (by decide)
  have ro : Bbu.rd t.dmem (t.regs.rsp.toBitVec + 32928#64) = off :=
    h.localRead (i := 4116) (by decide)
  have kr0 := hv.localSome (i := 0) (by decide)
  have r0 : Bbu.rd v.dmem t.regs.rsp.toBitVec = off := by
    simpa [v] using hv.localRead (i := 0) (by decide)
  have kre := hv.localSome (i := 4117) (by decide)
  have re : Bbu.rd v.dmem (t.regs.rsp.toBitVec + 32936#64) = ex := by
    simpa [v, ex, resolveExcess] using
      hv.localRead (i := 4117) (by decide)
  have krs := hx.localSome (i := 2064) (by decide)
  have rs : Bbu.rd x.dmem (t.regs.rsp.toBitVec + 16512#64) = resolveSize locals hl := by
    simpa [x, w, v, resolveLocals, resolveSize] using
      hx.localRead (i := 2064) (by decide)
  simp only [v, Nat.reduceMul, BitVec.add_zero] at kr0 kre
  simp only [Nat.reduceMul, BitVec.add_zero] at kro k0
  simp only [w, v, Nat.reduceMul] at k1
  simp only [x, w, v, Nat.reduceMul] at krs rs
  unfold Bbu.rd at ro r0 re rs
  simp only [v] at r0 re
  kvcgen64 [hresolve]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [ro, r0, re, rs] at ⊢
  vc_by_shape
  | load => simp only [kro, k0, k1, kr0, kre, krs]
  | other =>
    let y : MachineData := {x with regs :=
      (((((((t.regs.set64 .rax off).set64 .rcx ex).set64 .rdx off).set64 .rsi
        (t.regs.rsp.toBitVec + 96#64)).set64 .rdi t.regs.rbx.toBitVec).set64 .r8
          (t.regs.rsp.toBitVec + 16536#64)).set64 .r9 (resolveSize locals hl))}
    have hy : PostEmitLI P g M F s ra lo (resolveLocals locals hl) y := by
      apply hx.next
      all_goals rfl
    refine hy.toBd.callResolve ?_ ?_ ?_ ?_ ?_
    · rw [hy.mappingEq]
      exact plannerResolve_ok h.ok _ _ hin.mapping
    · exact h.rbx
    · refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
      · exact hin.size
      · exact hin.offset
      · exact hin.excess
      · rw [resolveLocals_current hl hy.localLength]
        exact hin.current
    · intro r' u hq
      have hr := (hq ⟨Vector.replicate MAX_N 0#8, Vector.replicate MAX_N 0#64⟩).2
      rw [hr]
      rfl
    · intro spills dropped u lo' hb hq hag
      have hp := hy.afterResolve spills dropped hb hag
      obtain ⟨res, hal, hmodel⟩ := resolved_of_resolveQ hq
      apply hfinish spills dropped res lo' u hp ?_ hal ?_
      · simp only [plannerResolve, hy.mappingEq,
          resolveLocals_current hl hy.localLength] at hmodel
        exact hmodel
      · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]
        exact hbp

theorem b_30 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64) (locals : List Word)
    (hl : locals.length = 4121) (hin : ResolveInputs g M locals hl) (before : Word)
    (hresolve : VSpec RView RG.Ok Names.resolve resolveA 1182 resolveQ)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hbad : ∀ spills dropped res lo' u,
      Resolved g M locals hl spills dropped res →
      PostEmitLI P (withResolve g spills dropped) M F s ra lo' (resolveLocals locals hl) u →
      res ≠ .dropped → al u = ResolveU.code res →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.26") u)
    (hzero : ∀ spills dropped res lo' u,
      Resolved g M locals hl spills dropped res →
      PostEmitLI P (withResolve g spills dropped) M F s ra lo' (resolveLocals locals hl) u →
      res = .dropped → g.p.m = 0#64 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.24") u)
    (hmore : ∀ spills dropped res lo' u,
      Resolved g M locals hl spills dropped res →
      PostEmitLI P (withResolve g spills dropped) M F s ra lo' (resolveLocals locals hl) u →
      res = .dropped → g.p.m ≠ 0#64 → u.regs.rbp.toBitVec = before →
      rax u = g.p.drp → rcx u = g.p.drp + g.p.m → rdx u = 0#64 → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.30" →
      ∀ t, (∃ lo, PostEmitLI P g M F s ra lo locals t) →
        t.regs.rbp.toBitVec = before → WP.wp blk.body K
          (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  apply b_30_call P g M F s ra locals hl hin before hresolve K I' E
  intro spills dropped res lo' u h hmodel hal hbp
  apply resolve_tail P (withResolve g spills dropped) M F s ra lo'
    (resolveLocals locals hl) u res before h hal hbp K I' E
  · intro v hv hres ha
    exact hbad spills dropped res lo' v hmodel hv hres ha
  · intro v hv hres hm
    exact hzero spills dropped res lo' v hmodel hv hres hm
  · intro v hv hres hm hb ha hc hd
    exact hmore spills dropped res lo' v hmodel hv hres hm hb ha hc hd

end Bbu.Unit.PlannerRunU
