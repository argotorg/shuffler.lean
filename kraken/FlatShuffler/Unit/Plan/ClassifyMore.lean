module

public import FlatShuffler.Unit.Plan.Classify
import all FlatShuffler.Unit.Plan.Classify
public import FlatShuffler.Unit.Plan.ClassifyCalls
import all FlatShuffler.Unit.Plan.ClassifyCalls

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ClassifyU
open FlatShuffler.Sep

theorem rank_nonvalue (x : Inputs) (hf : x.free = false) (hn : x.slot.kind ≠ Value) :
    x.rank = if x.other then 3 else Flat.NOCLASS := by
  simp [Inputs.rank, Inputs.spill, Flat.isVariable, hn, hf]

theorem pack_word (w : Word) :
    ((((w &&& BitVec.ofInt 64 (-4294967296)) ||| (w.extractLsb' 0 32).setWidth 64) &&&
        BitVec.ofInt 64 (-280375465082881)) |||
      ((w.extractLsb' 40 8).setWidth 64 <<< (40 : Nat))) = w := by
  bv_decide

theorem other_class_code (b : Bool) (w : BitVec 32) :
    ((w - w - BitVec.ofNat 32
        ((↑((if b then 1#8 else 0#8) - 1#8).toNat : Int) !=
          (↑(if b then 1#8 else 0#8).toNat - 1 : Int)).toNat ||| 3#32).zeroExtend 64).setWidth 8 =
      (if b then 3#8 else Flat.NOCLASS) := by
  cases b <;> simp [Flat.NOCLASS]

theorem other_class_from_al (a : BitVec 8) (b : Bool) (w : BitVec 32)
    (h : a = if b then 1#8 else 0#8) :
    ((w - w - BitVec.ofNat 32
        ((↑(a - 1#8).toNat : Int) != (↑a.toNat - 1 : Int)).toNat ||| 3#32).zeroExtend 64).setWidth 8 =
      (if b then 3#8 else Flat.NOCLASS) := by
  rw [h]
  exact other_class_code b w

section
variable [Host] [FunDecls] (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_5 (hok : c.Ok) (ha : classifyA c s)
    (hother : VSpec HView HG.Ok Names.hasOtherRetainedCopy hasOtherA 8 hasOtherQ) :
    classifyAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Planner.classify.5" → Obl P c F s ra blk := by
  simp only [Names.hasOtherRetainedCopy] at hother
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨lo, w, q, hli, hr, hf, hn⟩ := ht
  kvcgen64 [hother]
  all_goals try symexec_norm at ⊢
  refine LI.callOther (hli.next rfl rfl rfl rfl rfl rfl rfl rfl) hok ha
    hli.rbx hli.r12 hli.r14 hli.rbp ?_
  intro u lo' w' hli' hal hag
  have hax : u.regs.rax.toBitVec.extractLsb' 0 8 =
      (if (inp c s).other then 1#8 else 0#8) := by
    change (u.regs.rax.toBitVec.setWidth 8) = _ at hal
    rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] at hal
    exact hal
  kvcgen64
  all_goals try symexec_norm at ⊢
  cfg_goto
  · exact (hli'.kb.next rfl rfl).stack (by decide)
  · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
    refine ⟨lo', w', q, hli'.toBd.next rfl rfl, ?_⟩
    exact (other_class_from_al (u.regs.rax.toBitVec.extractLsb' 0 8) (inp c s).other
      (u.regs.rdx.toBitVec.extractLsb' 0 32) hax).trans
        (hr.trans (rank_nonvalue (inp c s) hf hn)).symm
  · left; simp [V, Names.classify]

end
end FlatShuffler.Unit.ClassifyU
