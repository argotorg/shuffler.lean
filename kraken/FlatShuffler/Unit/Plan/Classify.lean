module

public import FlatShuffler.Unit.Plan.ClassifyFrame
import all FlatShuffler.Unit.Plan.ClassifyFrame
public import FlatShuffler.Unit.IsAvailable
import all FlatShuffler.Unit.IsAvailable
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-! Checked blocks of `Planner::classify`. The function theorem is still open:
the entry prologue is not proved here. Other block modules supply the remaining labels. -/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ClassifyU
open FlatShuffler.Sep

theorem low32_low8 (w : Word) : (w.extractLsb' 0 32).setWidth 8 = w.setWidth 8 := by
  bv_decide

theorem kind_lea (w : Word) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (w + BitVec.ofInt 64 (-1)))).extractLsb' 0 8 =
      w.extractLsb' 0 8 - 1#8 := by bv_decide

theorem kind_range (k : BitVec 8) :
    decide ((k - 1#8).toNat ≤ 1) = (k == Junk || k == FunctionCallReturnLabel) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  unfold Junk FunctionCallReturnLabel
  bv_omega

def Body (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (R : Inputs → Prop) (t : MachineData) : Prop :=
  ∃ lo w q, LI P c F s ra lo w q t ∧ R (inp c s)

def Result (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (v : BitVec 8) (t : MachineData) : Prop :=
  ∃ lo w q, Bd P c F s ra lo w q t ∧ v = (inp c s).eval

def Inv (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.classify then t = s.pushRa ra
    else if l = ".LB.Planner.classify.0" then Body P c F s ra (fun x => x.eval = x.generated) t
    else if l = ".LB.Planner.classify.1" then Body P c F s ra (fun x => x.eval = x.rank) t
    else if l = ".LB.Planner.classify.2" then
      Body P c F s ra (fun x => x.eval = x.rank ∧ x.free = false) t
    else if l = ".LB.Planner.classify.3" then
      Body P c F s ra (fun x => x.eval = x.rank ∧ x.free = false ∧ x.slot.kind = Value) t
    else if l = ".LB.Planner.classify.4" then
      Body P c F s ra (fun x => x.free = false) t ∧ rsi t = c.h.mp ∧
        (rcx t).setWidth 32 = (inp c s).slot.payload
    else if l = ".LB.Planner.classify.5" then
      Body P c F s ra (fun x => x.eval = x.rank ∧ x.free = false ∧ x.slot.kind ≠ Value) t
    else if l = ".LB.Planner.classify.6" then
      Body P c F s ra (fun x => x.eval = x.generated ∧ x.free = true) t ∧ rsi t = c.h.mp ∧
        rcx t = rcx s
    else if l = ".LB.Planner.classify.7" then Result P c F s ra 1 t
    else if l = ".LB.Planner.classify.8" then Result P c F s ra ((rdx t).setWidth 8) t
    else if l = ".LB.Planner.classify.9" then
      Body P c F s ra (fun x => x.eval = x.generated ∧ x.free = false) t ∧ rsi t = c.h.mp
    else if l = ".LB.Planner.classify.10" then
      Body P c F s ra (fun x => x.free = false ∧ x.slot.kind ≠ Value) t ∧ rsi t = c.h.mp
    else if l = ".LB.Planner.classify.11" then
      Body P c F s ra (fun x => x.eval = x.copied ∧ x.free = false ∧ x.spill = false) t
    else if l = ".LB.Planner.classify.12" then Result P c F s ra 0 t
    else False

def V (l : Label) (_ : MachineData) : Nat :=
  if l = Names.classify then 20
  else if l = ".LB.Planner.classify.4" then 16
  else if l = ".LB.Planner.classify.9" ∨ l = ".LB.Planner.classify.10" then 12
  else if l = ".LB.Planner.classify.11" then 11
  else if l = ".LB.Planner.classify.0" ∨ l = ".LB.Planner.classify.6" then 10
  else if l = ".LB.Planner.classify.1" then 9
  else if l = ".LB.Planner.classify.2" then 8
  else if l = ".LB.Planner.classify.3" ∨ l = ".LB.Planner.classify.5" then 7
  else if l = ".LB.Planner.classify.7" ∨ l = ".LB.Planner.classify.12" then 1
  else 0

def E (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost CView CG.Ok P F 16 (fun c' t => classifyQ c c' s t) s t
    ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, Inv P c F s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv P c F s ra b u ∧ Program.Decreases V blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels classifyAsm) (s.pushRa ra) I' (E P c F s ra)) t

section
variable [Host] [FunDecls] (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_entry : classifyAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  simpa only [Inv, Names.classify, ↓reduceIte] using ht

theorem b_7 : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.7" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result] at ht
  obtain ⟨lo, w, q, hb, hr⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
    exact ⟨lo, w, q, hb.next rfl rfl, hr⟩
  · left; simp [V, Names.classify]

theorem b_12 : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.12" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result] at ht
  obtain ⟨lo, w, q, hb, hr⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  cfg_goto
  · exact (hb.kb.next rfl rfl).stack (by decide)
  · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
    exact ⟨lo, w, q, hb.next rfl rfl, hr⟩
  · left; simp [V, Names.classify]

theorem b_8 (hok : c.Ok) : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.8" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result] at ht
  obtain ⟨lo, w, q, hb, hr⟩ := ht
  have k0 := hb.popSome 0 (by decide)
  have k1 := hb.popSome 1 (by decide)
  have k2 := hb.popSome 2 (by decide)
  have k3 := hb.popSome 3 (by decide)
  have k4 := hb.popSome 4 (by decide)
  have k5 := hb.popSome 5 (by decide)
  simp only [BitVec.add_comm (8#64) t.regs.rsp.toBitVec, BitVec.add_assoc] at k0 k1 k2 k3 k4 k5
  simp only [Nat.reduceMul, BitVec.reduceAdd] at k0 k1 k2 k3 k4 k5
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load =>
    simp only [BitVec.add_comm (8#64) t.regs.rsp.toBitVec, BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    first
    | with_reducible exact k0
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | with_reducible exact k5
  | retAddr =>
    refine Option.isSome_iff_exists.mpr
      ⟨ra, Kg.retAddr (P := CView P c ∗ F) (s := s) (fr := fr s lo w q) ?_⟩
    exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
  | ret =>
    refine Kg.vret (ok := CG.Ok) (a' := c) (fr := fr s lo w q) ?_ ?_ hok
      fun u _ hax => ⟨rfl, ?_⟩
    · exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
    · simp [fr, saved, hb.len]
    · show (rax u).setWidth 8 = _
      rw [hax]
      simp only [rax, Reg64s.get64_rax]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
      rw [low32_low8]
      exact hr.trans (eval_eq_classify _ _ _ _ _)

theorem b_2 : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.2" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨lo, w, q, hli, hr, hf⟩ := ht
  have hk := hli.r13
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.Planner.classify.5" =>
    rename_i hj
    have hn : (inp c s).slot.kind ≠ Value := by
      symexec_norm at hj
      simpa only [hk, BitVec.and_self, Bool.not_eq_true', beq_eq_false_iff_ne,
        BitVec.zero_eq, Value, BitVec.ofNat_eq_ofNat] using hj
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      exact ⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl, hr, hf, hn⟩
    · left; simp [V, Names.classify]
  | other =>
    rename_i hj
    have he : (inp c s).slot.kind = Value := by
      symexec_norm at hj
      simpa only [hk, BitVec.and_self, Bool.not_eq_false', beq_iff_eq,
        BitVec.zero_eq, Value, BitVec.ofNat_eq_ofNat] using hj
    first
    | (simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
       exact ⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl, hr, hf, he⟩)
    | (left; simp [V, Names.classify])

theorem b_0 (hok : c.Ok) (ha : classifyA c s) : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.0" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨lo, w, q, hli, hr⟩ := ht
  obtain ⟨_, hm⟩ := CView.map hli.kb.vmem
  obtain ⟨_, hp⟩ := CView.pv hli.kb.vmem
  have hi : (rcx s).toNat < MAX_N := Nat.lt_of_lt_of_le ha.1.2.2 hok.m
  have h_d := MapM.rd_dest hm hi
  have k_d := MapM.isSome_dest hm hi
  have h_t := plannerObjectOwnedMemory.rd_tgt hp
  have k_t := plannerObjectOwnedMemory.isSome_tgt hp
  have h_k := plannerObjectOwnedMemory.rdb_kind hp hok ha.2
  have k_k := plannerObjectOwnedMemory.isSome_kind hp hok ha.2
  have hb := hli.rbx
  have h12 := hli.r12
  have hbp := hli.rbp
  unfold rd at h_d h_t
  unfold rdb at h_k
  clear hm hp
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hb, h12, hbp, fold_slot, h_d, h_t] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_d
    | with_reducible exact k_t
    | with_reducible exact k_k
  | goto ".LB.Planner.classify.12" =>
    rename_i hj
    symexec_norm at hj
    simp only [hb, h12, hbp, fold_slot, h_d, h_t] at hj
    have ht : (inp c s).targetJunk = true := (DemandU.junk_flag h_k).symm.trans hj
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
      exact ⟨lo, w, q, hli.toBd.next rfl rfl, (hr.trans (by simp [Inputs.generated, ht])).symm⟩
    · left; simp [V, Names.classify]
  | other =>
    rename_i hj
    symexec_norm at hj
    try simp only [hb, h12, hbp, fold_slot, h_d, h_t] at hj
    have ht : (inp c s).targetJunk = false := (DemandU.junk_flag h_k).symm.trans hj
    first
    | (simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
       exact ⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl,
         hr.trans (by simp [Inputs.generated, ht])⟩)
    | (left; simp [V, Names.classify])

theorem b_9 (hok : c.Ok) (ha : classifyA c s) : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.9" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨⟨lo, w, q, hli, hr, hf⟩, hsi⟩ := ht
  obtain ⟨_, hm⟩ := CView.map hli.kb.vmem
  obtain ⟨_, hp⟩ := CView.pv hli.kb.vmem
  have hi : (rcx s).toNat < MAX_N := Nat.lt_of_lt_of_le ha.1.2.2 hok.m
  have h_d := MapM.rd_dest hm hi
  have k_d := MapM.isSome_dest hm hi
  have h_t := plannerObjectOwnedMemory.rd_tgt hp
  have k_t := plannerObjectOwnedMemory.isSome_tgt hp
  have h_k := plannerObjectOwnedMemory.rdb_kind hp hok ha.2
  have k_k := plannerObjectOwnedMemory.isSome_kind hp hok ha.2
  have hb := hli.rbx
  have hbp := hli.rbp
  change t.regs.rsi.toBitVec = c.h.mp at hsi
  unfold rd at h_d h_t
  unfold rdb at h_k
  clear hm hp
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hb, hsi, hbp, fold_slot, h_d, h_t] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_d
    | with_reducible exact k_t
    | with_reducible exact k_k
  | goto ".LB.Planner.classify.2" =>
    rename_i hj
    symexec_norm at hj
    simp only [hb, hsi, hbp, fold_slot, h_d, h_t, Bool.not_eq_true'] at hj
    have ht : (inp c s).targetJunk = false := (DemandU.junk_flag h_k).symm.trans hj
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      exact ⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl,
        hr.trans (by simp [Inputs.generated, ht]), hf⟩
    · left; simp [V, Names.classify]
  | goto ".LB.Planner.classify.12" =>
    rename_i hj
    symexec_norm at hj
    simp only [hb, hsi, hbp, fold_slot, h_d, h_t, Bool.not_eq_false'] at hj
    have ht : (inp c s).targetJunk = true := (DemandU.junk_flag h_k).symm.trans hj
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
      exact ⟨lo, w, q, hli.toBd.next rfl rfl, (hr.trans (by simp [Inputs.generated, ht])).symm⟩
    · left; simp [V, Names.classify]

theorem b_6 (hok : c.Ok) (ha : classifyA c s) : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.6" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨⟨lo, w, q, hli, hr, hf⟩, hsi, hcx⟩ := ht
  obtain ⟨_, hm⟩ := CView.map hli.kb.vmem
  obtain ⟨_, hp⟩ := CView.pv hli.kb.vmem
  have hi : (rcx s).toNat < MAX_N := Nat.lt_of_lt_of_le ha.1.2.2 hok.m
  have h_d := MapM.rd_dest hm hi
  have k_d := MapM.isSome_dest hm hi
  have h_t := plannerObjectOwnedMemory.rd_tgt hp
  have k_t := plannerObjectOwnedMemory.isSome_tgt hp
  have h_k := plannerObjectOwnedMemory.rdb_kind hp hok ha.2
  have k_k := plannerObjectOwnedMemory.isSome_kind hp hok ha.2
  have hb := hli.rbx
  change t.regs.rsi.toBitVec = c.h.mp at hsi
  change t.regs.rcx.toBitVec = rcx s at hcx
  unfold rd at h_d h_t
  unfold rdb at h_k
  clear hm hp
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hb, hsi, hcx, fold_slot, h_d, h_t] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_d
    | with_reducible exact k_t
    | with_reducible exact k_k
  | goto ".LB.Planner.classify.12" =>
    rename_i hj
    symexec_norm at hj
    simp only [hb, hsi, hcx, fold_slot, h_d, h_t] at hj
    have ht : (inp c s).targetJunk = true := (DemandU.junk_flag h_k).symm.trans hj
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
      exact ⟨lo, w, q, hli.toBd.next rfl rfl, (hr.trans (by simp [Inputs.generated, ht])).symm⟩
    · left; simp [V, Names.classify]
  | other =>
    rename_i hj
    symexec_norm at hj
    try simp only [hb, hsi, hcx, fold_slot, h_d, h_t] at hj
    have ht : (inp c s).targetJunk = false := (DemandU.junk_flag h_k).symm.trans hj
    first
    | (simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
       exact ⟨lo, w, q, hli.toBd.next rfl rfl,
         (hr.trans (by simp [Inputs.generated, ht, rank_free _ hf])).symm⟩)
    | (left; simp [V, Names.classify])

theorem b_10 (hok : c.Ok) (ha : classifyA c s) : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.10" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨⟨lo, w, q, hli, hf, hn⟩, hsi⟩ := ht
  obtain ⟨_, hm⟩ := CView.map hli.kb.vmem
  obtain ⟨_, hp⟩ := CView.pv hli.kb.vmem
  have hi : (rcx s).toNat < MAX_N := Nat.lt_of_lt_of_le ha.1.2.2 hok.m
  have h_d := MapM.rd_dest hm hi
  have k_d := MapM.isSome_dest hm hi
  have h_t := plannerObjectOwnedMemory.rd_tgt hp
  have k_t := plannerObjectOwnedMemory.isSome_tgt hp
  have h_k := plannerObjectOwnedMemory.rdb_kind hp hok ha.2
  have k_k := plannerObjectOwnedMemory.isSome_kind hp hok ha.2
  have hb := hli.rbx
  have hbp := hli.rbp
  have hjunk : isJunk (inp c s).slot = false := by
    have hh := hf
    simp only [Inputs.free, canBeFreelyGenerated, Bool.or_eq_false_iff] at hh
    exact hh.1.2
  have hs : (inp c s).spill = false := by simp [Inputs.spill, Flat.isVariable, hn]
  change t.regs.rsi.toBitVec = c.h.mp at hsi
  unfold rd at h_d h_t
  unfold rdb at h_k
  clear hm hp
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hb, hsi, hbp, fold_slot, h_d, h_t] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_d
    | with_reducible exact k_t
    | with_reducible exact k_k
  | goto ".LB.Planner.classify.5" =>
    rename_i hj
    symexec_norm at hj
    simp only [hb, hsi, hbp, fold_slot, h_d, h_t, Bool.not_eq_true'] at hj
    have ht : (inp c s).targetJunk = false := (DemandU.junk_flag h_k).symm.trans hj
    cfg_goto
    · exact (hli.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
      exact ⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl,
        eval_plain _ hli.nonreturn ht, hf, hn⟩
    · left; simp [V, Names.classify]
  | other =>
    rename_i hj
    symexec_norm at hj
    try simp only [hb, hsi, hbp, fold_slot, h_d, h_t, Bool.not_eq_false'] at hj
    have ht : (inp c s).targetJunk = true := (DemandU.junk_flag h_k).symm.trans hj
    first
    | (simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
       exact ⟨lo, w, q, hli.next rfl rfl rfl rfl rfl rfl rfl rfl,
         eval_copied _ hli.nonreturn ht hjunk hf hs, hf, hs⟩)
    | (left; simp [V, Names.classify])

end
end FlatShuffler.Unit.ClassifyU
