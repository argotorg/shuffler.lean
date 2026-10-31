import BbuKraken.Unit.Plan.ClassifySpill

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

variable [Host] [FunDecls] (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_4 (hok : c.Ok) (ha : classifyA c s) : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.4" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨⟨lo, w, q, hli, hf⟩, hsi, hcx⟩ := ht
  obtain ⟨_, hm⟩ := CView.map hli.kb.vmem
  obtain ⟨_, hp⟩ := CView.pv hli.kb.vmem
  have hi : (rcx s).toNat < MAX_N := Nat.lt_of_lt_of_le ha.1.2.2 hok.m
  have h_d := MapM.rd_dest hm hi
  have k_d := MapM.isSome_dest hm hi
  have h_t := PView.rd_tgt hp
  have k_t := PView.isSome_tgt hp
  have h_k := PView.rdb_kind hp hok ha.2
  have k_k := PView.isSome_kind hp hok ha.2
  obtain ⟨_, hsp⟩ := PView.spills hp
  have k_sp := Wd.isSome hsp
  have h_sp := Wd.rd hsp
  have hspl (he : (inp c s).slot.kind = Value) :=
    CView.spl hli.kb.vmem hok ha (variable_of_value (inp c s) hf he)
  have k_b (he : (inp c s).slot.kind = Value) := B8.isSome (hspl he).choose_spec
  have h_b (he : (inp c s).slot.kind = Value) := B8.rdb (hspl he).choose_spec
  simp only [BitVec.ofNat_toNat] at k_b h_b
  have hb := hli.rbx
  have hbp := hli.rbp
  have hk := hli.r13
  change t.regs.rsi.toBitVec = c.h.mp at hsi
  change t.regs.rcx.toBitVec.setWidth 32 = (inp c s).slot.payload at hcx
  rw [BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)] at hcx
  unfold rd at h_d h_t h_sp
  unfold rdb at h_k h_b
  clear hm hp hsp
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hb, hsi, hbp, hcx, fold_slot, h_d, h_t, h_sp] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_d
    | with_reducible exact k_t
    | with_reducible exact k_k
    | with_reducible exact k_sp
    | (rename_i hj
       symexec_norm at hj
       have he : (inp c s).slot.kind = Value := by
         simpa only [hk, BitVec.and_self, Bool.not_eq_false', beq_iff_eq,
           BitVec.zero_eq, Value, BitVec.ofNat_eq_ofNat] using hj
       exact k_b he)
  | goto ".LB.Planner.classify.10" =>
    rename_i hj
    symexec_norm at hj
    have hn : (inp c s).slot.kind ≠ Value := by
      simpa only [hk, BitVec.and_self, Bool.not_eq_true', beq_eq_false_iff_ne,
        BitVec.zero_eq, Value, BitVec.ofNat_eq_ofNat] using hj
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      exact ⟨⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl, hf, hn⟩, hsi⟩
    · left; change (12 : Nat) < 16; decide
  | goto ".LB.Planner.classify.9" =>
    rename_i hj hs
    symexec_norm at hj hs
    have he : (inp c s).slot.kind = Value := by
      simpa only [hk, BitVec.and_self, Bool.not_eq_false', beq_iff_eq,
        BitVec.zero_eq, Value, BitVec.ofNat_eq_ofNat] using hj
    simp only [hb, hcx, h_sp] at hs
    have hv := variable_of_value (inp c s) hf he
    have hspill : (inp c s).spill = true :=
      (spill_nz_flag (inp c s) hv _ (h_b he)).symm.trans hs
    have hg : (inp c s).eval = (inp c s).generated :=
      eval_generated (inp c s) hli.nonreturn (by simp [hspill])
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      exact ⟨⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl, hg, hf⟩, hsi⟩
    · left; change (12 : Nat) < 16; decide
  | goto ".LB.Planner.classify.11" =>
    rename_i hj hs htgt
    symexec_norm at hj hs htgt
    have he : (inp c s).slot.kind = Value := by
      simpa only [hk, BitVec.and_self, Bool.not_eq_false', beq_iff_eq,
        BitVec.zero_eq, Value, BitVec.ofNat_eq_ofNat] using hj
    simp only [hb, hsi, hbp, hcx, h_sp, fold_slot, h_d, h_t] at hs htgt
    have hv := variable_of_value (inp c s) hf he
    have hspill : (inp c s).spill = false :=
      (spill_nz_flag (inp c s) hv _ (h_b he)).symm.trans hs
    have ht : (inp c s).targetJunk = true := (DemandU.junk_flag h_k).symm.trans htgt
    have hc := eval_copied (inp c s) hli.nonreturn ht
      (by simp [isJunk, not_junk_of_not_free (inp c s) hf]) hf hspill
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      exact ⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl, hc, hf, hspill⟩
    · left; change (11 : Nat) < 16; decide
  | goto ".LB.Planner.classify.3" =>
    rename_i hj hs htgt
    symexec_norm at hj hs htgt
    have he : (inp c s).slot.kind = Value := by
      simpa only [hk, BitVec.and_self, Bool.not_eq_false', beq_iff_eq,
        BitVec.zero_eq, Value, BitVec.ofNat_eq_ofNat] using hj
    simp only [hb, hsi, hbp, fold_slot, h_d, h_t] at htgt
    have ht : (inp c s).targetJunk = false := (DemandU.junk_flag h_k).symm.trans htgt
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      exact ⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl,
        eval_plain (inp c s) hli.nonreturn ht, hf, he⟩
    · left; change (7 : Nat) < 16; decide

end Bbu.Unit.ClassifyU
