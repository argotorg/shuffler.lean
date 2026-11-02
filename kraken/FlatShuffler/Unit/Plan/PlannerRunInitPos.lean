module

public import FlatShuffler.Unit.Plan.PlannerRunInitDefs
import all FlatShuffler.Unit.Plan.PlannerRunInitDefs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open Flat

private theorem pos_addr (sp i : Word) : sp + 96#64 + i * 8#64 + 8192#64 =
    sp + BitVec.ofNat 64 (8 * (1036 + i.toNat)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

private theorem pos_end {sp i n : Word} (hi : i < n) (hn : n.toNat ≤ maxStackSize)
    (he : 8#64 + (sp + 96#64 + i * 8#64) = sp + 96#64 + n * 8#64) :
    1#64 + i = n := by
  change n.toNat ≤ 1024 at hn
  bv_omega

set_option maxRecDepth 4096 in
theorem b_8 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s t : MachineData) (ra : Int64) (hok : g.Ok) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hnext : ∀ u, rax u = 8#64 + rax t → InitPosHead P g F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.22") u)
    (hdone : ∀ u, InitDone P g F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.22" →
      InitPosHead P g F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, i, hc, hi, hax, hcx, hdest, hpos⟩
  have hn := hok.planner.targetSizeFitsBuffer
  have hm := hok.planner.sourceSizeFitsBuffer
  have hiN : i.toNat < maxStackSize := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hn
  have hidx : 1036 + i.toNat < 4121 := by change i.toNat < 1024 at hiN; omega
  have hsucc : (1#64 + i).toNat = i.toNat + 1 := by
    change i.toNat < 1024 at hiN
    bv_omega
  have hpos' := hpos.step (by rw [hc.localLength]; exact hidx)
  have hdest' := hdest.set_outside (index := 1036 + i.toNat) (by
    intro j hj
    change g.p.sourceSize.toNat ≤ 1024 at hm
    omega) NONE
  simp only [rax, rcx, Reg64s.get64_rax, Reg64s.get64_rcx] at hax hcx
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load =>
    rw [hax, pos_addr]
    exact hc.localSome hidx
  | goto ".LB.Planner.run.22" =>
    rename_i heq
    symexec_norm at heq
    simp only [sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at heq
    have hne : 1#64 + i ≠ g.p.targetSize := by
      intro he
      apply heq
      rw [hax, hcx, ← he]
      bv_omega
    apply hnext
    · rfl
    refine ⟨lo, locals.set (1036 + i.toNat) NONE, 1#64 + i, ?_,
      succ_lt hi hne, ?_, ?_, hdest', ?_⟩
    · apply hc.storeLocal hidx (by omega) NONE
      · rw [hax, pos_addr]
        rfl
      all_goals rfl
    · simp only [rax, Reg64s.get64_rax, hax]
      bv_omega
    · simp only [rcx, Reg64s.get64_rcx]
      exact hcx
    · rw [hsucc]
      exact hpos'
  | other =>
    rename_i heq
    symexec_norm at heq
    simp only [sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at heq
    have hend : 1#64 + i = g.p.targetSize := pos_end hi hn (by simpa only [hax, hcx] using heq)
    apply hdone
    refine ⟨lo, locals.set (1036 + i.toNat) NONE, ?_, hdest', ?_⟩
    · apply hc.storeLocal hidx (by omega) NONE
      · rw [hax, pos_addr]
        rfl
      all_goals rfl
    · rw [← hend, hsucc]
      exact hpos'
  | closed => decide

end FlatShuffler.Unit.PlannerRunU
