module

public import BbuKraken.Unit.Plan.PlannerRunBuilderDefs
import all BbuKraken.Unit.Plan.PlannerRunBuilderDefs
public import BbuKraken.Unit.Plan.PlannerRunEmissionDefs
import all BbuKraken.Unit.Plan.PlannerRunEmissionDefs
public import Kraken.X64.Parser
import all Kraken.X64.Parser

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def builderTail : Program := parse("
  movzbl 56(%rbx), %eax
  testb %al, %al
  movzbl 88(%rsp), %edx
  cmove %edx, %eax
  movb %al, 56(%rbx)
  movl $0, %eax
  cmpq $0, 8(%rbx)
  je .LB.Planner.run.28
")

def mergeSaw (old saw : BitVec 8) : BitVec 8 := if old = 0#8 then saw else old

private theorem saw_low (pad : BitVec 56) (saw : BitVec 8) :
    (pad ++ saw).extractLsb' 0 8 = saw := by bv_decide

private theorem select_saw (old saw : BitVec 8) :
    (BitVec.extractLsb' 0 8
      (BitVec.setWidth 64
        (if (BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) &&&
              BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) ==
                BitVec.zero 8) = true then
          BitVec.extractLsb' 0 32 (BitVec.setWidth 64 (BitVec.setWidth 32 saw))
        else BitVec.extractLsb' 0 32 (BitVec.setWidth 64 (BitVec.setWidth 32 old))))) =
      mergeSaw old saw := by
  unfold mergeSaw
  bv_decide

theorem BuilderLocals.sawWord (l : BuilderLocals) (b : BG) :
    (l.toList b)[11]? = some (l.sawPad ++ b.saw) := by
  simp [BuilderLocals.toList, List.append_assoc, List.getElem?_append]

theorem BuildLI.storeSaw {P : Addr} {g : PlannerRunG} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo : List Word} {l : BuilderLocals}
    {M : Flat.Mapping} {saw : BitVec 8}
    (h : BuildLI P g F s ra lo l M saw t) (hok : g.Ok) (x : Int)
    (hm : u.dmem = t.dmem.storeInt (P + 56#64) 1 x)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (_h13 : u.regs.r13 = t.regs.r13) (_h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) :
    AttemptLI P (withSaw g (BitVec.ofInt 8 x)) M F s ra lo
      (l.toList (plannerBuilder g s M saw)) u := by
  have hc := MapCells.localMapping h.toBd hok
  rw [l.mapping] at hc
  exact ⟨⟨h.toBd.storeSaw x hm hsp, hbx ▸ h.rbx, h14 ▸ h.r14,
    h.ops, h.strategy, h.sources⟩, h.count, hc, fun _ => l.mapping _,
      by simpa only [h15, hsp] using h.r15⟩

set_option maxRecDepth 4096 in
theorem builder_tail [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (hok : g.Ok) (M : Flat.Mapping) (saw : BitVec 8)
    (lo : List Word) (l : BuilderLocals) (t : MachineData)
    (hb : BuildLI P g F s ra lo l M saw t)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hzero : ∀ u, g.p.m = 0#64 →
      AttemptLI P (withSaw g (mergeSaw g.p.saw saw)) M F s ra lo
        (l.toList (plannerBuilder g s M saw)) u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.28") u)
    (hnonzero : ∀ u, g.p.m ≠ 0#64 → rax u = 0#64 →
      AttemptLI P (withSaw g (mergeSaw g.p.saw saw)) M F s ra lo
        (l.toList (plannerBuilder g s M saw)) u → K () u) :
    WP.wp builderTail K (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  obtain ⟨RF, hframe⟩ : ∃ RF, PlannerRunView P g ∗
      (Stk (rsp s) (fr s lo (l.toList (plannerBuilder g s M saw))) ra.toBitVec ∗ F) =
      B8 (P + 56#64) g.p.saw ∗ RF := ⟨_, by unfold PlannerRunView PView; ecancel⟩
  have hsaw := hframe ▸ hb.kb.vmem
  have ksaw := B8.isSome hsaw
  have rsaw := B8.rdb hsaw
  obtain ⟨R, he⟩ := hb.localFocus
  have hi : 11 < (l.toList (plannerBuilder g s M saw)).length := by rw [hb.localLength]; decide
  obtain ⟨Q, hf, _⟩ := ResolveU.Arr_focus_set t.regs.rsp.toBitVec
    (l.toList (plannerBuilder g s M saw)) hi
  have hm := he _ hb.localLength ▸ hb.kb.mem
  rw [hf, MProp.sep_assoc] at hm
  have hw := l.sawWord (plannerBuilder g s M saw)
  rw [List.getElem?_eq_getElem hi] at hw
  rw [Option.some.inj hw] at hm
  have kbyte := Wd.isSome_byte hm (j := 0) (by decide)
  have rbyte := Wd.rdb_byte hm (j := 0) (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero, saw_low, plannerBuilder, builderGhost] at kbyte rbyte
  have hb' := hb.storeSaw hok (mergeSaw g.p.saw saw).toInt
    (u := {t with dmem := t.dmem.storeInt (P + 56#64) 1 (mergeSaw g.p.saw saw).toInt})
    rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨_, hp⟩ := pv hb'.kb.vmem
  have km := PView.isSome_m hp
  have rm := PView.rd_m hp
  simp only [withSaw, BitVec.ofInt_toInt] at km rm hb'
  unfold rdb at rsaw rbyte
  unfold rd at rm
  have hselect := select_saw g.p.saw saw
  simp only [BitVec.zero_eq] at hselect
  have hselect' := hselect
  simp only [beq_iff_eq] at hselect'
  unfold builderTail
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hb.rbx, rsaw, rbyte, select_saw] at ⊢
  vc_by_shape
  | load => simp only [ksaw, kbyte, km]
  | goto ".LB.Planner.run.28" =>
    rename_i af hj
    symexec_norm at hj
    simp only [hb.rbx, rsaw, rbyte, hselect', rm, BitVec.sub_zero,
      BitVec.zero_eq, beq_iff_eq] at hj
    apply hzero _ hj
    exact hb'.next rfl rfl rfl rfl rfl rfl rfl rfl
  | other =>
    rename_i af hj
    symexec_norm at hj
    simp only [hb.rbx, rsaw, rbyte, hselect, rm, BitVec.sub_zero,
      BitVec.zero_eq, beq_eq_false_iff_ne] at hj
    apply hnonzero _ hj rfl
    exact hb'.next rfl rfl rfl rfl rfl rfl rfl rfl

end Bbu.Unit.PlannerRunU
