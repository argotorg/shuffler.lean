module

public import FlatShuffler.Unit.Plan.ResolveDropDefs
import all FlatShuffler.Unit.Plan.ResolveDropDefs
public import FlatShuffler.Unit.Plan.ResolveClassByte
import all FlatShuffler.Unit.Plan.ResolveClassByte

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

theorem b_12 [Host] [FunDecls]
    (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hok : r.Ok) :
    resolveAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.resolve.12" →
      Obl P r F s ra (loopPhase P r F s ra (dropPhase P r F s ra rest)) (loopVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte, PickEnd] at ht
  obtain ⟨w, lo, L, h, hm, h15, hcls⟩ := ht
  have kc := h.bd.classSome
  have hr := h.bd.classRead
  rw [hcls] at hr
  unfold rdb at hr
  have hv := picked_valid r.p.fl r.M w.candidates w.count w.state h.ok.bounded h.ok.live
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => exact kc
  | goto ".LB.Planner.resolve.17" =>
    rename_i hj
    symexec_norm at hj
    simp only [h15, Idioms.sub_beq_zero, beq_iff_eq, BitVec.zero_eq] at hj
    have hb : (w.pick r).1 = Flat.NONE := hj
    cfg_goto
    · exact h.bd.kb.stack (by decide)
    · simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Return]
      exact ⟨w.ghost r, lo, L.toList, h.bd.next rfl rfl,
        update_ok hok _ _, Work.no_best h.ok hm hb⟩
    · left
      simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte]
      omega
  | goto ".LB.Planner.resolve.14" =>
    rename_i hb hc
    symexec_norm at hb hc
    simp only [h15, Idioms.sub_beq_zero, beq_eq_false_iff_ne, BitVec.zero_eq] at hb
    simp only [hr, Idioms.sub_beq_zero, beq_iff_eq, BitVec.zero_eq] at hc
    have hbest : (w.pick r).1 ≠ Flat.NONE := hb
    have hspill : (w.pick r).2 = Flat.SPILL := hc
    cfg_goto
    · exact h.bd.kb.stack (by decide)
    · simp only [Inv, loopPhase, dropPhase, Names.resolve, String.reduceEq,
        ↓reduceIte, SpillReady]
      exact ⟨w, lo, L, h.next rfl rfl rfl rfl rfl, hm, h15, hcls, hbest, hspill⟩
    · left
      simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
      symexec_norm at ⊢
      omega
  | other =>
    rename_i hb hc
    symexec_norm at hb hc
    simp only [h15, Idioms.sub_beq_zero, beq_eq_false_iff_ne, BitVec.zero_eq] at hb
    simp only [hr, Idioms.sub_beq_zero, beq_eq_false_iff_ne, BitVec.zero_eq] at hc
    have hbest : (w.pick r).1 ≠ Flat.NONE := hb
    have hnspill : (w.pick r).2 ≠ Flat.SPILL := hc
    first
    | (simp only [Inv, loopPhase, dropPhase, Names.resolve, String.reduceEq,
         ↓reduceIte, DropReady]
       exact ⟨w, lo, L, (w.pick r).1, h.next rfl rfl rfl rfl rfl, h15,
         (hv.resolve_left hbest).1, Work.drop_model h.ok hm hbest hnspill⟩)
    | (left
       simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
       symexec_norm at ⊢
       omega)

end FlatShuffler.Unit.ResolveU
