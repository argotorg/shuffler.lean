import BbuKraken.Unit.Plan.PlannerRunOutputDefs
import BbuKraken.Unit.Run.Load

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

private theorem planned_pos_addr (sp i : Word) :
    sp + i * 8#64 + 8288#64 = sp + BitVec.ofNat 64 (8 * (1036 + i.toNat)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

private theorem sources_addr (p i : Word) : p + i * 8#64 = slotAt p i.toNat := by
  simp only [slotAt, BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

set_option maxRecDepth 4096 in
theorem b_17 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64) (wanted : Vector Word MAX_N)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hnext : ∀ sources u, rdx u = 1#64 + rdx t →
      SourcesHead P {g with sources := sources} M F s ra wanted u → al u = al t →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.17") u)
    (hdone : ∀ sources u, SourcesDone P {g with sources := sources} M F s ra u →
      sources = wanted → al u = al t → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.17" →
      SourcesHead P g M F s ra wanted t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hbp, hi, hmodel⟩
  let i := rdx t
  have hiN : i.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hc.ok.planner.n
  have hidx : 1036 + i.toNat < 4121 := by change i.toNat < 1024 at hiN; omega
  have hr := hc.posRead hiN
  have kp := hc.localSome hidx
  have hp := hc.localRead (i := 2) (by decide)
  have he := hc.sources
  rw [List.getElem?_eq_getElem (by rw [hc.localLength]; decide)] at he
  replace hp := hp.trans (Option.some.inj he)
  have kl := hc.localSome (i := 2) (by decide)
  obtain ⟨_, hsrc⟩ := sources hc.kb.vmem
  have ks : (t.dmem.loadInt (slotAt g.sourcesPtr i.toNat) 8).isSome = true :=
    Arr.isSome hsrc (by simp only [List.length_take, Vector.length_toList]; have him : i.toNat < g.p.n.toNat := BitVec.lt_def.mp hi; omega)
  let g1 : PlannerRunG := {g with sources := put g.sources i (get M.pos i)}
  let v : MachineData := {t with
    dmem := t.dmem.storeInt (slotAt g.sourcesPtr i.toNat) 8 (get M.pos i).toInt}
  have hc1 : PostEmitLI P g1 M F s ra lo locals v :=
    hc.storeSources hiN (BitVec.lt_def.mp hi) _ rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨_, hp1⟩ := pv hc1.kb.vmem
  have kn : (v.dmem.loadInt (P + 24#64) 8).isSome = true :=
    isSome_of_eq g.p.n hp1 (by unfold PView; ecancel)
  have hn : rd v.dmem (P + 24#64) = g.p.n :=
    rd_of_eq hp1 (by unfold PView; ecancel)
  have hstep : Flat.sourcesFrom g.p.n (i + 1#64) M g1.sources = wanted := by
    change Flat.sourcesFrom g.p.n (rdx t + 1) M
      (put g.sources (rdx t) (get M.pos (rdx t))) = wanted
    rw [← sources_next hi]
    exact hmodel
  have hbx := hc.rbx
  simp only [Nat.reduceMul] at hp kl
  simp only [i, rdx, Reg64s.get64_rdx] at hidx hr kp ks hi hstep
  simp only [v, i, Reg64s.get64_rdx] at kn hn
  unfold rd at hr hp hn
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [planned_pos_addr, hr, hp, hbx] at ⊢
  all_goals try simp only [sources_addr, hn] at ⊢
  vc_by_shape
  | load => run_loads [kp, kl, ks, kn]
  | goto ".LB.Planner.run.17" =>
    rename_i hb
    symexec_norm at hb
    simp only [planned_pos_addr, hr, hp, hbx] at hb
    simp only [sources_addr, hn,
      Idioms.cf_sub, decide_eq_true_eq] at hb
    have hlt : 1#64 + rdx t < g.p.n := hb
    apply hnext g1.sources
    · rfl
    · refine ⟨lo, locals, hc1.next ?_ rfl rfl rfl rfl rfl rfl, hbp, hlt, ?_⟩
      · rfl
      · simpa only [g1, i, rdx, Reg64s.get64_rdx,
          BitVec.add_comm 1#64 t.regs.rdx.toBitVec] using hstep
    · rfl
  | other =>
    rename_i hb
    symexec_norm at hb
    simp only [planned_pos_addr, hr, hp, hbx] at hb
    simp only [sources_addr, hn,
      Idioms.cf_sub, decide_eq_false_iff_not] at hb
    have hend : ¬ t.regs.rdx.toBitVec + 1#64 < g.p.n := by
      simpa only [BitVec.lt_def,
        BitVec.add_comm 1#64 t.regs.rdx.toBitVec] using hb
    rw [sources_end hend] at hstep
    apply hdone g1.sources
    · exact ⟨lo, locals, hc1.next rfl rfl rfl rfl rfl rfl rfl, hbp⟩
    · exact hstep
    · rfl

end Bbu.Unit.PlannerRunU
