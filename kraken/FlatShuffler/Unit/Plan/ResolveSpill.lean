module

public import FlatShuffler.Unit.Plan.ResolveSpillCall
import all FlatShuffler.Unit.Plan.ResolveSpillCall
public import FlatShuffler.Unit.Plan.ResolveDropDefs
import all FlatShuffler.Unit.Plan.ResolveDropDefs
public import FlatShuffler.Unit.Run.Load
import all FlatShuffler.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

theorem spill_failed_unchanged (sp : BitVec 32 → BitVec 8) (x : StackSlot)
    (h : (Flat.spillAdd sp x).1 ≠ .done) : (Flat.spillAdd sp x).2 = sp := by
  unfold Flat.spillAdd at h ⊢
  split
  · rfl
  · split
    · rfl
    · simp_all

set_option maxRecDepth 4096 in
theorem b_14 [Host] [FunDecls]
    (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels resolveAsm, label l ≠ label "exit")
    (hok : r.Ok) (hadd : VSpecWithExit AddView AddG.Ok Names.spillSetAdd addA 2 addQ addX) :
    resolveAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.resolve.14" →
      Obl P r F s ra (loopPhase P r F s ra (dropPhase P r F s ra rest))
        (loopVar s var) blk := by
  simp only [Names.spillSetAdd] at hadd
  cfg_block [Obl]
  intro t ht
  simp only [Inv, loopPhase, dropPhase, Names.resolve,
    String.reduceEq, ↓reduceIte, SpillReady] at ht
  obtain ⟨w, lo, L, h, hm, h15, hcls, hbest, hspill⟩ := ht
  have hv := (picked_valid r.p.fl r.M w.candidates w.count w.state
    h.ok.bounded h.ok.live).resolve_left hbest
  have ho : (w.pick r).1.toNat < r.p.sourceSize.toNat := BitVec.lt_def.mp hv.1
  have hmem := h.bd.kb.mem
  rw [sep_lc] at hmem
  obtain ⟨_, hp⟩ := RView.pv hmem
  have ksrc := plannerObjectOwnedMemory.isSome_src hp
  have rsrc := plannerObjectOwnedMemory.rd_src hp
  have kword := plannerObjectOwnedMemory.isSome_sw hp hok.planner ho
  have rword := plannerObjectOwnedMemory.rd_sw hp hok.planner ho
  unfold rd at rsrc rword
  kvcgen64 [hadd]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [h.r14, rsrc, h15, fold_slot] at ⊢
  vc_by_shape
  | load => run_loads [ksrc, kword]
  | other =>
    refine h.callAdd hok rfl rfl rfl rfl rfl rfl ?_ ho ?_ ?normal ?abort
    · simp only [rdi, Reg64s.get64_rdi]
    · simp only [rsi, Reg64s.get64_rsi]
      exact rword
    case normal =>
      intro u lo' hu hal h15u
      have hbase : loopBase s u = loopBase s t := hu.base.trans h.base.symm
      rw [h15] at h15u
      have hal' := hal
      change u.regs.rax.toBitVec.setWidth 8 = _ at hal'
      rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] at hal'
      have he := ProofKit.external_call_spec "exit" hexit
      kvcgen64 [he]
      all_goals try symexec_norm at ⊢
      vc_by_shape
      | goto ".LB.Planner.resolve.13" =>
        rename_i hj
        have hd : (Flat.spillAdd w.spills (Flat.get r.p.fl.source (w.pick r).1)).1 = .done := by
          symexec_norm at hj
          simp only [BitVec.and_self, hal', beq_iff_eq, BitVec.zero_eq] at hj
          exact code_eq_zero hj
        cfg_goto
        · exact hu.bd.kb.stack (by decide)
        · simp only [Inv, loopPhase, dropPhase, Names.resolve,
            String.reduceEq, ↓reduceIte, DropReady]
          refine ⟨_, lo', L, (w.pick r).1, ?_, h15u, hv.1,
            Work.spill_model h.ok hm hbest hspill hd⟩
          apply hu.next <;> rfl
        · left
          simp only [V, loopVar, String.reduceEq, ↓reduceIte, false_or, loopBase]
          change loopBase s u + 4 + 2 < loopBase s t + 6 + 2
          rw [hbase]
          omega
      | load => exact (hu.bd.exit_mem 0).1
      | jumpOut =>
        rename_i af hj exitra
        have hd : (Flat.spillAdd w.spills (Flat.get r.p.fl.source (w.pick r).1)).1 ≠ .done := by
          symexec_norm at hj
          simp only [BitVec.and_self, hal', beq_eq_false_iff_ne, BitVec.zero_eq] at hj
          exact code_ne_zero hj
        have hs := spill_failed_unchanged w.spills (Flat.get r.p.fl.source (w.pick r).1) hd
        have hb := hu.bd
        rw [hs] at hb
        refine Or.inr ⟨Or.inr ⟨rfl, rfl, w.ghost r,
          Work.spill_fail h.ok hm hbest hspill hd, update_ok hok _ _,
          (hb.exit_mem _).2⟩, ?_⟩
        intro l hl heq
        exact False.elim (hout l hl heq)
    case abort =>
      intro u lo' hlen hmem hf harg
      have hd : (Flat.spillAdd w.spills (Flat.get r.p.fl.source (w.pick r).1)).1 ≠ .done := by
        rw [hf]
        change Flat.Status.assertionFailed ≠ Flat.Status.done
        decide
      have hmodel := Work.spill_fail h.ok hm hbest hspill hd
      refine Or.inr ⟨Or.inr ⟨rfl, harg, ?_⟩, ?_⟩
      · refine ⟨w.ghost r, hmodel, update_ok hok _ _, fr s lo' L.toList,
          ra.toBitVec, ?_, ?_⟩
        · simp only [fr, List.length_append, hlen, L.length, saved,
            List.length_cons, List.length_nil, resolveD]
        · simpa only [MProp.sep_assoc] using hmem
      · intro l hl ha
        exact False.elim (hout l hl ha)

end FlatShuffler.Unit.ResolveU
