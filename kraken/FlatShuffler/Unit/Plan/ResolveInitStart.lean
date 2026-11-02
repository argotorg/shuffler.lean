module

public import FlatShuffler.Unit.Plan.ResolveInitDefs
import all FlatShuffler.Unit.Plan.ResolveInitDefs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

theorem candidate_initial {P : Addr} {r : RG} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {lo : List Word} {L : Lc}
    (hb : Bd P r F s ra lo L.toList t) (he : L.excess = rcx s)
    (hr : InputRegs P r s t) (hz : ZeroPrefix r.p.m t) (hok : r.Ok) :
    CandidateState P r F s ra lo L ⟨L.droppedNow, L.candidates⟩ 0#64 t := by
  refine ⟨hb, he, hr.r12, hr.r14, hr.r8, hr.r9, by decide,
    ?_, ?_, hb.droppedZero hz hok.planner.m, rfl⟩
  · intro i hi; exact False.elim (by bv_omega)
  · intro i hi; exact False.elim (by bv_omega)

theorem b_1 [Host] [FunDecls]
    (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hok : r.Ok) (ha : resolveA r s) :
    resolveAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.resolve.1" →
      Obl P r F s ra (initFullPhase P r F s ra rest) (initFullVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, initFullPhase, zphase, Names.resolve,
    String.reduceEq, ↓reduceIte, AfterZero] at ht
  obtain ⟨lo, loc, hb, ⟨L, rfl, hL⟩, hr, hz⟩ := ht
  have hc := candidate_initial hb hL hr hz hok
  have hblocked := ha.2.2.2.1
  have hsize := ha.2.2.1
  have hpos : (rdx s + 1#64).toNat ≤ MAX_N := by
    change (rdx s + 1).toNat ≤ MAX_N
    rw [small_succ _ ha.2.2.2.1]
    omega
  have hdx : 1#64 + rdx t = rdx s + 1#64 := by rw [hr.rdx]; bv_omega
  have h9 : t.regs.r9.toBitVec = r9 s := hr.r9
  symexec_norm at hdx hpos h9 hsize
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.Planner.resolve.5" =>
    rename_i hj
    symexec_norm at hj
    have hend : ¬ (rdx s + 1#64) < r9 s := by
      change ¬ (s.regs.rdx.toBitVec + 1#64) < s.regs.r9.toBitVec
      have hh := hj
      idioms at hh
      rw [h9, hdx] at hh
      bv_omega
    cfg_goto
    · exact hb.kb.stack (by decide)
    · simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
        String.reduceEq, ↓reduceIte, CandidatesDone]
      refine ⟨lo, L, ⟨L.droppedNow, L.candidates⟩, 0#64,
        hc.next rfl rfl rfl rfl rfl rfl, rfl, ?_⟩
      exact candidates_done hend
    · left
      simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
      decide
  | goto ".LB.Planner.resolve.4" =>
    rename_i hj
    symexec_norm at hj
    have hlt : (rdx s + 1#64) < r9 s := by
      change (s.regs.rdx.toBitVec + 1#64) < s.regs.r9.toBitVec
      have hh := hj
      idioms at hh
      rw [h9, hdx] at hh
      bv_omega
    cfg_goto
    · exact hb.kb.stack (by decide)
    · simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
        String.reduceEq, ↓reduceIte, Scan, Bool.false_eq_true]
      symexec_norm at ⊢
      refine ⟨lo, L, ⟨L.droppedNow, L.candidates⟩, 0#64,
        hc.next rfl rfl rfl rfl rfl rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [hdx]; exact hlt
      · bv_omega
      · simpa only [hdx] using hpos
      · simp only [candidateStart, hdx]; rfl
    · left
      simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
      symexec_norm at ⊢
      rw [hdx]
      have hlt' : s.regs.rdx.toBitVec + 1#64 < s.regs.r9.toBitVec := hlt
      change s.regs.r9.toBitVec.toNat ≤ 1024 at hsize
      have hbound : (s.regs.r9.toBitVec - (s.regs.rdx.toBitVec + 1#64)).toNat ≤ 1024 := by bv_omega
      omega

end FlatShuffler.Unit.ResolveU
