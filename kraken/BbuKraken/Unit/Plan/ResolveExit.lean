module

public import BbuKraken.Unit.Plan.ResolveFrame
import all BbuKraken.Unit.Plan.ResolveFrame
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-! The return blocks of `Planner::resolve`. The phase invariant remains a
parameter so the loop proofs can use these blocks without changing them. -/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU

open Bbu.Sep

def modelQ (r r' : RG) (s : MachineData) (st : Flat.Resolution) : Prop :=
  ∀ u : Flat.ResolveU,
    let q := Flat.resolve r.p.fl r.spills r.dropped r.M (rdx s) (rcx s)
      r.current (r9 s) u
    q.1 = st ∧ r' = { r with spills := q.2.1, dropped := q.2.2 }

theorem model_post {r r' : RG} {s t : MachineData} {st : Flat.Resolution}
    (hm : modelQ r r' s st) (ha : al t = code st) (hst : st ≠ .assertionFailed) :
    resolveQ r r' s t := by
  intro u
  obtain ⟨hres, hout⟩ := hm u
  exact ⟨ha.trans (congrArg code hres).symm, hout, fun he => hst (hres.symm.trans he)⟩

def Return (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (st : Flat.Resolution) (t : MachineData) : Prop :=
  ∃ r' lo loc, Bd P r' F s ra lo loc t ∧ r'.Ok ∧ modelQ r r' s st

def Result (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ r' lo loc st, Bd P r' F s ra lo loc t ∧ r'.Ok ∧ modelQ r r' s st ∧
    al t = code st ∧ st ≠ .assertionFailed

def Inv (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (phase : Label → MachineData → Prop) : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.resolve then t = s.pushRa ra
    else if l = ".LB.Planner.resolve.2" then Return P r F s ra .assertionFailed t
    else if l = ".LB.Planner.resolve.18" then Result P r F s ra t
    else if l = ".LB.Planner.resolve.15" then Return P r F s ra .stuck t
    else if l = ".LB.Planner.resolve.16" then Return P r F s ra .dropped t
    else if l = ".LB.Planner.resolve.17" then Return P r F s ra .stuck t
    else phase l t

def V (phase : Label → MachineData → Nat) (l : Label) (t : MachineData) : Nat :=
  if l = ".LB.Planner.resolve.18" then 0
  else if l = ".LB.Planner.resolve.2" ∨ l = ".LB.Planner.resolve.15" ∨
      l = ".LB.Planner.resolve.16" ∨ l = ".LB.Planner.resolve.17" then 1
  else phase l t + 2

def E [Labels] (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost RView RG.Ok P F resolveD (fun r' t => resolveQ r r' s t) s t
    ∧ Sep.mod.Agree s t
    ∨ a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧
      VPost RView RG.Ok P F resolveD (fun r' t => resolveX r r' s t) s t

def Obl [Host] [FunDecls] (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (phase : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (blk : Program.Block) : Prop :=
  ∀ t, Inv P r F s ra phase blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv P r F s ra phase b u ∧ Program.Decreases (V var) blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels resolveAsm) (s.pushRa ra) I' (E P r F s ra)) t

def labels : List CfgLabel :=
  [.entry, .label Names.resolve,
    .label ".LB.Planner.resolve.0", .label ".LB.Planner.resolve.1",
    .label ".LB.Planner.resolve.2", .label ".LB.Planner.resolve.18",
    .label ".LB.Planner.resolve.3", .label ".LB.Planner.resolve.4",
    .label ".LB.Planner.resolve.5", .label ".LB.Planner.resolve.6",
    .label ".LB.Planner.resolve.7", .label ".LB.Planner.resolve.8",
    .label ".LB.Planner.resolve.9", .label ".LB.Planner.resolve.10",
    .label ".LB.Planner.resolve.11", .label ".LB.Planner.resolve.12",
    .label ".LB.Planner.resolve.13", .label ".LB.Planner.resolve.14",
    .label ".LB.Planner.resolve.15", .label ".LB.Planner.resolve.16",
    .label ".LB.Planner.resolve.17"]

theorem labels_cover : resolveAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.resolve]
  cfg_labels

section
variable [Host] [FunDecls] (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (phase : Label → MachineData → Prop) (var : Label → MachineData → Nat)

theorem b_entry : resolveAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl P r F s ra phase var blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  simpa only [Inv, Names.resolve, ↓reduceIte] using ht

theorem b_2 (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels resolveAsm, label l ≠ label "exit") : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.2" → Obl P r F s ra phase var blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Return] at ht
  obtain ⟨r', lo, loc, hb, hok, hm⟩ := ht
  have he := ProofKit.external_call_spec "exit" hexit
  kvcgen64 [he]
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => exact (hb.exit_mem 0).1
  | jumpOut =>
    refine Or.inr ⟨Or.inr ⟨rfl, rfl, r', hm, hok, (hb.exit_mem _).2⟩, ?_⟩
    intro l hl heq
    exact False.elim (hout l hl heq)

theorem b_18 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.18" → Obl P r F s ra phase var blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Result] at ht
  obtain ⟨r', lo, loc, st, hb, hok, hm, ha, hst⟩ := ht
  have k0 := hb.popSome 0 (by decide)
  have k1 := hb.popSome 1 (by decide)
  have k2 := hb.popSome 2 (by decide)
  have k3 := hb.popSome 3 (by decide)
  have k4 := hb.popSome 4 (by decide)
  have k5 := hb.popSome 5 (by decide)
  simp only [BitVec.add_assoc, Nat.reduceMul, BitVec.reduceAdd, BitVec.add_zero]
    at k0 k1 k2 k3 k4 k5
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load =>
    try simp only [BitVec.add_comm (9272#64) t.regs.rsp.toBitVec,
      BitVec.add_assoc, BitVec.reduceAdd]
    first
    | with_reducible exact k0
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | with_reducible exact k5
  | retAddr =>
    refine Option.isSome_iff_exists.mpr
      ⟨ra, Kg.retAddr (P := RView P r' ∗ F) (s := s) (fr := fr s lo loc) ?_⟩
    exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
  | ret =>
    refine ProofKit.intercept_mono_exit
      (E := fun a t => a = ra ∧
        VPost RView RG.Ok P F resolveD (fun r' t => resolveQ r r' s t) s t ∧
          Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
    refine Kg.vret (ok := RG.Ok) (a' := r') (fr := fr s lo loc) ?_ hb.fr_len hok
      fun u _ hax => ?_
    · exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
    · apply model_post hm
      · exact (congrArg (BitVec.setWidth 8) hax).trans ha
      · exact hst

theorem b_15 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.15" → Obl P r F s ra phase var blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Return] at ht
  obtain ⟨r', lo, loc, hb, hok, hm⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  cfg_goto
  · exact (hb.next rfl rfl).kb.stack (by decide)
  · simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Result]
    exact ⟨r', lo, loc, .stuck, hb.next rfl rfl, hok, hm, rfl, by decide⟩
  · left; simp [V]

theorem b_16 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.16" → Obl P r F s ra phase var blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Return] at ht
  obtain ⟨r', lo, loc, hb, hok, hm⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  cfg_goto
  · exact (hb.next rfl rfl).kb.stack (by decide)
  · simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Result]
    exact ⟨r', lo, loc, .dropped, hb.next rfl rfl, hok, hm, rfl, by decide⟩
  · left; simp [V]

theorem b_17 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.17" → Obl P r F s ra phase var blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Return] at ht
  obtain ⟨r', lo, loc, hb, hok, hm⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  · simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Result]
    exact ⟨r', lo, loc, .stuck, hb.next rfl rfl, hok, hm, rfl, by decide⟩
  · left; simp [V]

end
end Bbu.Unit.ResolveU
