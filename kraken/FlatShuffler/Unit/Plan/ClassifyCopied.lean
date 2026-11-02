module

public import FlatShuffler.Unit.Plan.ClassifyMore
import all FlatShuffler.Unit.Plan.ClassifyMore

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ClassifyU
open FlatShuffler.Sep

theorem code_bool_true (b : Bool) (a : BitVec 8)
    (ha : a = if b then 1#8 else 0#8) (hn : a ≠ 0#8) : b = true := by
  cases b <;> simp_all

theorem code_bool_false (b : Bool) (a : BitVec 8)
    (ha : a = if b then 1#8 else 0#8) (hz : a = 0#8) : b = false := by
  cases b <;> simp_all

theorem not_junk_of_not_free (x : Inputs) (hf : x.free = false) :
    x.slot.kind ≠ Junk := by
  intro hj
  simp [Inputs.free, canBeFreelyGenerated, hj] at hf

theorem pack_fields (w : Word) (x : BitVec 32) (o : BitVec 8)
    (hx : x = (StackSlot.ofWord w).payload)
    (ho : o = (StackSlot.ofWord w).valueOpcode) :
    ((((18446744069414584320#64 &&& w) ||| x.setWidth 64) &&&
        18446463698244468735#64) ||| (o.setWidth 32 |>.setWidth 64).shiftLeft 40) = w := by
  rw [hx, ho]
  dsimp only [StackSlot.ofWord]
  bv_decide

section
variable [Host] [FunDecls] (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_11 (hok : c.Ok) (ha : classifyA c s)
    (hother : VSpec HView HG.Ok Names.hasOtherRetainedCopy hasOtherA 8 hasOtherQ)
    (hdemand : VSpec plannerObjectOwnedMemory PlannerObjectMemory.Ok Names.isDemanded isDemandedA 0 isDemandedQ) :
    classifyAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Planner.classify.11" → Obl P c F s ra blk := by
  simp only [Names.hasOtherRetainedCopy] at hother
  simp only [Names.isDemanded] at hdemand
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨lo, w, q, hli, hr, hf, hs⟩ := ht
  kvcgen64 [hother]
  all_goals try symexec_norm at ⊢
  refine LI.callOther (hli.next rfl rfl rfl rfl rfl rfl rfl rfl) hok ha
    hli.rbx hli.r12 hli.r14 hli.rbp ?_
  intro u lo' w' hli' hal hag
  obtain ⟨_, hm⟩ := hli'.toBd.localWord
  rw [Wd.split34, MProp.sep_assoc] at hm
  have k_pl := B32.isSome hm
  have h_pl := B32.rd hm
  rw [sep_lc, MProp.sep_assoc] at hm
  have k_op := B8.isSome hm
  have h_op := B8.rdb hm
  unfold rdb at h_op
  clear hm
  have hn := not_junk_of_not_free (inp c s) hf
  have hslot := slot_eq c s hok ha
  have hfields := hli'.locals hn
  have hp : q.extractLsb' 32 32 = (StackSlot.ofWord (sw c s)).payload :=
    hfields.1.trans (congrArg StackSlot.payload hslot).symm
  have ho : q.extractLsb' 24 8 = (StackSlot.ofWord (sw c s)).valueOpcode :=
    hfields.2.trans (congrArg StackSlot.valueOpcode hslot).symm
  kvcgen64 [hdemand]
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => first | with_reducible exact k_pl | with_reducible exact k_op
  | closed => decide
  | goto ".LB.Planner.classify.12" =>
    symexec_norm at *
    have hb := code_bool_true (inp c s).other (al u) hal
      (al_ne (by with_reducible assumption))
    cfg_goto
    · exact (hli'.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
      exact ⟨lo', w', q, hli'.toBd.next rfl rfl,
        (hr.trans (copied_other (inp c s) hb)).symm⟩
    · left; simp [V, Names.classify]
  | other =>
    symexec_norm at *
    have hb := code_bool_false (inp c s).other (al u) hal
      (al_zero (by with_reducible assumption))
    refine LI.callDemand (hli'.next rfl rfl rfl rfl rfl rfl rfl rfl) hok hli'.rbx ?_ ?_
    · simp only [rsi, Reg64s.get64_rsi, h_pl, h_op, hli'.r15]
      rw [pack_fields (sw c s) _ _ hp ho]
      exact hslot
    · intro v w'' hli'' hal' hag'
      kvcgen64
      all_goals try symexec_norm at ⊢
      vc_by_shape
      | goto ".LB.Planner.classify.1" =>
        symexec_norm at *
        have hd := code_bool_true (inp c s).demanded (al v) hal'
          (al_ne (by with_reducible assumption))
        cfg_goto
        · exact (hli''.kb.next rfl rfl).stack (by decide)
        · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
          exact ⟨lo', w'', q, hli''.next rfl rfl rfl rfl rfl rfl rfl rfl,
            hr.trans (copied_demanded (inp c s) hb hd)⟩
        · left; simp [V, Names.classify]
      | other =>
        symexec_norm at *
        have hd := code_bool_false (inp c s).demanded (al v) hal'
          (al_zero (by with_reducible assumption))
        first
        | (simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
           exact ⟨lo', w'', q, hli''.toBd.next rfl rfl,
             (hr.trans (copied_undemanded (inp c s) hd)).symm⟩)
        | (left; simp [V, Names.classify])

end
end FlatShuffler.Unit.ClassifyU
