module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionData
import all FlatShuffler.Unit.Plan.PlannerRunEmissionData

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open Flat FlatShuffler.Sep

private theorem slot_addr (p i : Word) : p + i * 8#64 = slotAt p i.toNat := by
  simp only [slotAt, BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

set_option maxRecDepth 4096 in
theorem b_10 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64) (hok : g.Ok)
    (wanted : Vector StackSlot MAX_N)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ data u, rax u = 1#64 + rax t →
      EmitDataHead P {g with data := data} M F s ra wanted u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.24") u)
    (hdone : ∀ data u, data.map StackSlot.ofWord = wanted →
      EmitDestHead P {g with data := data} M F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.24" →
      EmitDataHead P g M F s ra wanted t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, hmodel⟩
  let i := rax t
  have hiN : i.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hok.planner.m
  have hcap : i.toNat < g.dataCapacity :=
    Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) (Nat.le_max_left _ _)
  obtain ⟨_, hp0⟩ := pv hc.kb.vmem
  obtain ⟨_, ha0⟩ := plannerObjectOwnedMemory.arr_src hp0
  have hraw : rd t.dmem (slotAt g.p.src i.toNat) = g.p.sw[i.toNat]! := by
    have hidx : i.toNat < g.p.sw.length := hok.planner.sw ▸ BitVec.lt_def.mp hi
    simpa only [slotAt, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hidx, Option.getD_some] using Arr.rd ha0 hidx
  have hslot := plannerObjectOwnedMemory.rd_sw hp0 hok.planner (BitVec.lt_def.mp hi)
  rw [hraw] at hslot
  have ksrc := plannerObjectOwnedMemory.isSome_src hp0
  have hsrc := plannerObjectOwnedMemory.rd_src hp0
  have kslot := plannerObjectOwnedMemory.isSome_sw hp0 hok.planner (BitVec.lt_def.mp hi)
  obtain ⟨_, hdata⟩ := data hc.kb.vmem
  have hdataIdx : i.toNat < (g.data.toList.take g.dataCapacity).length := by
    simp only [List.length_take, Vector.length_toList]
    omega
  have kd : (t.dmem.loadInt (slotAt g.dataPtr i.toNat) 8).isSome = true :=
    Arr.isSome hdata hdataIdx
  let raw := g.p.sw[i.toNat]!
  let g1 : PlannerCallMemory := {g with data := Flat.put g.data i raw}
  let v : MachineData := {t with
    dmem := t.dmem.storeInt (slotAt g.dataPtr i.toNat) 8 raw.toInt}
  have hc1 : AttemptLI P g1 M F s ra lo locals v :=
    hc.storeData hiN hcap raw rfl rfl rfl rfl rfl rfl rfl rfl
  have hok1 : g1.Ok := data_ok hok _
  have hstep := data_copy_step hmodel hi raw hslot
  obtain ⟨_, hp1⟩ := pv hc1.kb.vmem
  have km := plannerObjectOwnedMemory.isSome_m hp1
  have hm := plannerObjectOwnedMemory.rd_m hp1
  have kt : (v.dmem.loadInt (P + 16#64) 8).isSome = true :=
    isSome_of_eq g.p.tgt hp1 (by unfold plannerObjectOwnedMemory; ecancel)
  have kn : (v.dmem.loadInt (P + 24#64) 8).isSome = true :=
    isSome_of_eq g.p.n hp1 (by unfold plannerObjectOwnedMemory; ecancel)
  have ks : (v.dmem.loadInt (P + 32#64) 8).isSome = true :=
    isSome_of_eq g.p.spl hp1 (by unfold plannerObjectOwnedMemory; ecancel)
  have ht : rd v.dmem (P + 16#64) = g.p.tgt := rd_of_eq hp1 (by unfold plannerObjectOwnedMemory; ecancel)
  have hn : rd v.dmem (P + 24#64) = g.p.n := rd_of_eq hp1 (by unfold plannerObjectOwnedMemory; ecancel)
  have hs : rd v.dmem (P + 32#64) = g.p.spl := rd_of_eq hp1 (by unfold plannerObjectOwnedMemory; ecancel)
  have k0 := hc1.headerSome hok1 0 (by decide)
  have k1 := hc1.headerSome hok1 1 (by decide)
  have k2 := hc1.headerSome hok1 2 (by decide)
  have k3 := hc1.headerSome hok1 3 (by decide)
  have k4 := hc1.headerSome hok1 4 (by decide)
  have k5 := hc1.headerSome hok1 5 (by decide)
  have k6 := hc1.headerSome hok1 6 (by decide)
  have ko := hc1.headerOpsSome hok1
  have ho := hc1.headerOpsRead hok1
  have hd := hc1.headerSetup hok1
  simp only [headerWrites, storeLocalWords, List.take, List.foldl_cons, List.foldl_nil,
    Nat.reduceAdd, Nat.reduceMul, g1, v] at k0 k1 k2 k3 k4 k5 k6 ko ho
  have hbx := hc.rbx
  have h14 := hc.r14
  unfold rd at hraw hsrc hm ht hn hs ho
  simp only [g1, v] at km hm kt kn ks ht hn hs
  simp only [i, rax, Reg64s.get64_rax] at hraw kslot kd raw hstep hi
  simp only [i, Reg64s.get64_rax, raw] at km hm kt kn ks ht hn hs k0 k1 k2 k3 k4 k5 k6 kd ko ho
  clear hp0 hp1 ha0 hdata
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hbx, h14, hsrc, slot_addr, hraw, hm, ht, hn, hs, ho] at ⊢
  vc_by_shape
  | load => simp only [ksrc, kslot, kd, km, kt, kn, ks, k0, k1, k2, k3, k4, k5, k6, ko]
  | goto ".LB.Planner.run.24" =>
    rename_i hb
    symexec_norm at hb
    simp only [hbx, h14, hsrc, slot_addr, hraw, hm, Idioms.cf_sub, decide_eq_true_eq] at hb
    have hlt : 1#64 + rax t < g.p.m := hb
    apply hnext g1.data
    · rfl
    refine ⟨lo, locals, hc1.next ?_ rfl rfl rfl rfl rfl rfl rfl, hlt, ?_⟩
    · rfl
    · simpa only [g1, i, rax, Reg64s.get64_rax, BitVec.add_comm 1#64 t.regs.rax.toBitVec] using hstep
  | goto ".LB.Planner.run.26" =>
    rename_i hb af hz
    symexec_norm at hz
    simp only [hbx, h14, hsrc, slot_addr, hraw, hm, BitVec.and_self, BitVec.zero_eq,
      beq_iff_eq] at hz
    have hm0 : g.p.m = 0#64 := hz
    rw [hm0] at hi
    exact False.elim (by bv_omega)
  | other =>
    rename_i hb af hz
    symexec_norm at hb
    simp only [hbx, h14, hsrc, slot_addr, hraw, hm, Idioms.cf_sub,
      decide_eq_false_iff_not] at hb
    have hend : ¬ t.regs.rax.toBitVec + 1#64 < g.p.m := by
      simpa only [BitVec.lt_def, BitVec.add_comm 1#64 t.regs.rax.toBitVec] using hb
    rw [copy_end hend] at hstep
    apply hdone g1.data
    · exact hstep
    refine ⟨lo, headerLocals g1 locals, hd.next ?_ rfl rfl rfl rfl rfl rfl rfl,
      ?_, ?_, ?_, WordPrefix.zero _ _ _⟩
    · simp only [headerWrites, storeLocalWords, List.foldl_cons, List.foldl_nil,
        Nat.reduceMul, BitVec.toInt_zero, g1, v, i, raw, Reg64s.get64_rax]
    · have hmpos : 0#64 < g.p.m := by bv_omega
      exact hmpos
    · rfl
    · rfl

end FlatShuffler.Unit.PlannerRunU
