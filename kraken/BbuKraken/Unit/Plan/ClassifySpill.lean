module

public import BbuKraken.Unit.Plan.ClassifyCopied
import all BbuKraken.Unit.Plan.ClassifyCopied

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

theorem variable_of_value (x : Inputs) (hf : x.free = false)
    (hk : x.slot.kind = Value) : Flat.isVariable x.slot = true := by
  have ho : x.slot.valueOpcode ≠ Const := by
    intro ho
    simp [Inputs.free, canBeFreelyGenerated, isLiteralValue, ho] at hf
  simp [Flat.isVariable, isLiteralValue, hk, ho]

theorem spill_nz_flag (x : Inputs) (hv : Flat.isVariable x.slot = true)
    (v : BitVec 8) (h : v = x.spilled) :
    (!(v - 0#8 == BitVec.zero 8)) = x.spill := by
  simp only [h, Inputs.spill, hv, Bool.true_and, BitVec.sub_zero, BitVec.zero_eq]
  rfl

theorem rank_value_without_other (x : Inputs) (hf : x.free = false)
    (hs : x.spill = false) (hv : Flat.isVariable x.slot = true) (ho : x.other = false) :
    x.rank = if x.allowed then Flat.SPILL else Flat.NOCLASS := by
  simp only [Inputs.rank, hf, hs, ho, Bool.false_eq_true, ↓reduceIte, hv, Bool.and_true]

theorem allowed_class_code (a : BitVec 8) (w : BitVec 32) :
    ((w - w - BitVec.ofNat 32
      ((↑(a - 1#8).toNat : Int) != (↑a.toNat - 1 : Int)).toNat ||| 4#32).zeroExtend 64).setWidth 8 =
      (if a != 0#8 then Flat.SPILL else Flat.NOCLASS) := by
  unfold Flat.SPILL Flat.NOCLASS
  rw [Idioms.cf_sub_imm a 1 (by decide)]
  have hz : decide (a.toNat < 1) = (a == 0#8) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, beq_iff_eq]
    bv_omega
  rw [hz]
  bv_decide

section
variable [Host] [FunDecls] (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_3 (hok : c.Ok) (ha : classifyA c s)
    (hother : VSpec HView HG.Ok Names.hasOtherRetainedCopy hasOtherA 8 hasOtherQ) :
    classifyAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Planner.classify.3" → Obl P c F s ra blk := by
  simp only [Names.hasOtherRetainedCopy] at hother
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨lo, w, q, hli, hr, hf, hk⟩ := ht
  have hv := variable_of_value (inp c s) hf hk
  have hn := not_junk_of_not_free (inp c s) hf
  obtain ⟨_, hm⟩ := hli.toBd.localWord
  rw [Wd.split34, MProp.sep_assoc] at hm
  have k_pl := B32.isSome hm
  have h_pl := (B32.rd hm).trans (hli.locals hn).1
  obtain ⟨_, hp⟩ := CView.pv hli.kb.vmem
  obtain ⟨_, hsp⟩ := PView.spills hp
  obtain ⟨_, hs⟩ := CView.spl hli.kb.vmem hok ha hv
  have k_sp := Wd.isSome hsp
  have h_sp := Wd.rd hsp
  have k_b := B8.isSome hs
  have h_b := B8.rdb hs
  rw [BitVec.ofNat_toNat] at k_b h_b
  have hb := hli.rbx
  unfold rd at h_sp
  unfold rdb at h_b
  clear hm hp hsp hs
  kvcgen64 [hother]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hb, h_pl, h_sp] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_pl
    | with_reducible exact k_sp
    | with_reducible exact k_b
  | goto ".LB.Planner.classify.8" =>
    rename_i hj
    symexec_norm at hj
    simp only [hb, h_pl, h_sp] at hj
    have hs : (inp c s).spill = true :=
      (spill_nz_flag (inp c s) hv _ h_b).symm.trans hj
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
      exact ⟨lo, w, q, hli.toBd.next rfl rfl, (hr.trans (rank_spill (inp c s) hf hs)).symm⟩
    · left; simp [V, Names.classify]
  | other =>
    symexec_norm at *
    simp only [hb, h_pl, h_sp] at *
    have hs : (inp c s).spill = false :=
      (spill_nz_flag (inp c s) hv _ h_b).symm.trans (by assumption)
    refine LI.callOther (hli.next rfl rfl rfl rfl rfl rfl rfl rfl) hok ha
      hli.rbx hli.r12 hli.r14 hli.rbp ?_
    intro u lo' w' hli' hal hag
    obtain ⟨_, hp⟩ := CView.pv hli'.kb.vmem
    obtain ⟨_, hm⟩ := PView.allowed hp
    have k_allow := B8.isSome hm
    have h_allow := B8.rdb hm
    have hb' := hli'.rbx
    unfold rdb at h_allow
    clear hp hm
    kvcgen64
    all_goals try symexec_norm at ⊢
    all_goals try simp only [hb'] at ⊢
    vc_by_shape
    | load => exact k_allow
    | goto ".LB.Planner.classify.8" =>
      symexec_norm at *
      first
      | (have ho := code_bool_true (inp c s).other (al u) hal
           (al_ne (by assumption))
         cfg_goto
         · exact (hli'.kb.next rfl rfl).stack (by decide)
         · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
           exact ⟨lo', w', q, hli'.toBd.next rfl rfl,
             (hr.trans (by simp [Inputs.rank, hf, hs, ho])).symm⟩
         · left; simp [V, Names.classify])
      | (have ho := code_bool_false (inp c s).other (al u) hal
           (al_zero (by assumption))
         cfg_goto
         · exact (hli'.kb.next rfl rfl).stack (by decide)
         · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
           refine ⟨lo', w', q, hli'.toBd.next rfl rfl, ?_⟩
           simp only [h_allow]
           exact (allowed_class_code c.h.p.allowed _).trans
             (hr.trans (rank_value_without_other (inp c s) hf hs hv ho)).symm
         · left; simp [V, Names.classify])

end
end Bbu.Unit.ClassifyU
