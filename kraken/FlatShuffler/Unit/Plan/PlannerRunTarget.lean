module

public import FlatShuffler.Unit.Plan.PlannerRunScanDefs
import all FlatShuffler.Unit.Plan.PlannerRunScanDefs
public import FlatShuffler.Unit.Plan.PlannerRunRead
import all FlatShuffler.Unit.Plan.PlannerRunRead
public import FlatShuffler.Unit.Plan.PlannerRunSpecs
import all FlatShuffler.Unit.Plan.PlannerRunSpecs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

private theorem byte_width (x : BitVec 8) : ((x.setWidth 32).setWidth 64).setWidth 8 = x := by
  bv_decide

private theorem zero_lt {w : Word} (h : w ≠ 0#64) : 0#64 < w := by bv_omega

private theorem sub8_zero {x c : BitVec 8}
    (h : x - c = BitVec.zero 8) : x = c := by
  change x - c = 0#8 at h
  bv_omega

private theorem sub8_nonzero {x c : BitVec 8}
    (h : x - c ≠ BitVec.zero 8) : x ≠ c := by
  change x - c ≠ 0#8 at h
  bv_omega

theorem target_generated {x : StackSlot}
    (h : x.kind = 1#8 ∨ x.valueOpcode = 0#8 ∨ x.kind = 2#8) :
    (isJunk x || canBeFreelyGenerated x) = true := by
  rcases h with h | h | h <;>
    simp [isJunk, canBeFreelyGenerated, isLiteralValue, Junk, Const,
      FunctionCallReturnLabel, h]

theorem target_not_generated {x : StackSlot}
    (h1 : x.kind ≠ 1#8) (ho : x.valueOpcode ≠ 0#8) (h2 : x.kind ≠ 2#8) :
    (isJunk x || canBeFreelyGenerated x) = false := by
  simp [isJunk, canBeFreelyGenerated, isLiteralValue, Junk, Const,
    FunctionCallReturnLabel, h1, ho, h2]

set_option maxRecDepth 4096 in
theorem b_1 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s t : MachineData) (ra : Int64) (hok : g.Ok) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rcx u = rcx t → CheckNext P g F s ra u →
      Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E
        (label ".LB.Planner.run.0") u)
    (hmissing : ∀ u, rcx u = rcx t → CheckMissing P g F s ra u →
      Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E
        (label ".LB.Planner.run.3") u)
    (hscan : ∀ u, rcx u = rcx t → rax u = 0#64 → CheckScan P g F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.1" →
      CheckHead P g F s ra t → WP.wp blk.body K
        (Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hi, he⟩
  have hv := hc.kb.mem
  rw [sep_lc] at hv
  obtain ⟨_, hp⟩ := pv hv
  have hkind := plannerObjectOwnedMemory.rdb_kind hp hok.planner (BitVec.lt_def.mp hi)
  have kkind := plannerObjectOwnedMemory.isSome_kind hp hok.planner (BitVec.lt_def.mp hi)
  obtain ⟨_, ho⟩ := target_opcode hv hok hi
  have hop := B8.rdb ho
  have kop := B8.isSome ho
  have hword := plannerObjectOwnedMemory.rd_tw hp hok.planner (BitVec.lt_def.mp hi)
  have kword := plannerObjectOwnedMemory.isSome_tw hp hok.planner (BitVec.lt_def.mp hi)
  have hm := plannerObjectOwnedMemory.rd_sourceSize hp
  have km := plannerObjectOwnedMemory.isSome_sourceSize hp
  have hsrc := plannerObjectOwnedMemory.rd_src hp
  have ksrc := plannerObjectOwnedMemory.isSome_src hp
  simp only [rcx, Reg64s.get64_rcx] at hkind kkind hop kop hword kword
  unfold rdb at hkind hop
  unfold rd at hm hsrc hword
  clear hv hp ho
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hc.r10, hc.rbx, fold_slot, hkind, hop, hm, hsrc] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact kkind
    | with_reducible exact kop
    | with_reducible exact km
    | with_reducible exact ksrc
    | with_reducible exact kword
  | goto ".LB.Planner.run.0" =>
    rename_i hj
    symexec_norm at hj
    simp only [hc.r10, fold_slot, hkind, hop, zext_byte,
      beq_iff_eq] at hj
    have hgen : (isJunk (Flat.get g.p.fl.target (rcx t)) ||
        canBeFreelyGenerated (Flat.get g.p.fl.target (rcx t))) = true := by
      apply target_generated
      first
      | exact Or.inl (sub8_zero hj)
      | exact Or.inr (Or.inl (sub8_zero hj))
      | exact Or.inr (Or.inr (sub8_zero hj))
    apply hnext
    · rfl
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl, hi, ?_⟩
    rw [he]
    apply targets_next hi
    simp only [hgen, Bool.true_or]
  | goto ".LB.Planner.run.3" =>
    rename_i h1 ho h2 af hz
    symexec_norm at h1 ho h2 hz
    simp only [hc.r10, fold_slot, hkind, hop, zext_byte,
      beq_eq_false_iff_ne] at h1 ho h2
    simp only [hc.rbx, hm, BitVec.and_self, beq_iff_eq] at hz
    apply hmissing
    · rfl
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl, hi, he,
      ?_, target_not_generated (sub8_nonzero h1) (sub8_nonzero ho) (sub8_nonzero h2), ?_⟩
    · exact byte_width _
    · exact contains_end (by rw [hz]; exact BitVec.lt_irrefl _)
  | other =>
    rename_i h1 ho h2 af hz
    symexec_norm at h1 ho h2 hz
    simp only [hc.r10, fold_slot, hkind, hop, zext_byte,
      beq_eq_false_iff_ne] at h1 ho h2
    simp only [hc.rbx, hm, BitVec.and_self, beq_eq_false_iff_ne] at hz
    apply hscan
    · rfl
    · rfl
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl, hi, he,
      ?_, target_not_generated (sub8_nonzero h1) (sub8_nonzero ho) (sub8_nonzero h2),
      rfl, rfl, hword, ?_, rfl⟩
    · exact byte_width _
    · exact zero_lt hz

end FlatShuffler.Unit.PlannerRunU
