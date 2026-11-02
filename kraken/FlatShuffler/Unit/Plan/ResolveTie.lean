module

public import FlatShuffler.Kit
import all FlatShuffler.Kit
public import FlatShuffler.Unit.Plan.ResolveChoose
import all FlatShuffler.Unit.Plan.ResolveChoose

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

def tieBest (M : Flat.Mapping) (off best : Word) : Word :=
  if Flat.get M.dest best < Flat.get M.dest off then off else best

theorem slotAt_mul (a : Addr) (o : Word) : slotAt a o.toNat = a + o * 8#64 := by
  simp only [slotAt, BitVec.ofNat_mul, BitVec.ofNat_toNat]
  bv_omega

theorem low8_movl (x : Word) :
    ((x.extractLsb' 0 32).setWidth 64).setWidth 8 = x.setWidth 8 := by
  bv_decide

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {w : Work} {lo : List Word} {L : Lc} {i best : Word} {cls : BitVec 8}

theorem tie_model (h : PickAt P r F s ra w lo L i best cls t)
    (heq : PickEq r w i best cls) (hb : best ≠ Flat.NONE)
    (hd : Flat.get w.droppedNow (Flat.get w.candidates i) = 0#8)
    (hc : Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i) = cls)
    (hn : cls ≠ Flat.NOCLASS) :
    let next := tieBest r.M (Flat.get w.candidates i) best
    BestValid r.p.fl w.spills r.M w.droppedNow next cls ∧
      PickEq r w (i + 1) next cls := by
  dsimp only
  have hcn : Flat.classify r.p.fl w.spills r.M w.droppedNow
      (Flat.get w.candidates i) ≠ Flat.NOCLASS := by rw [hc]; exact hn
  by_cases ht : Flat.get r.M.dest best < Flat.get r.M.dest (Flat.get w.candidates i)
  · rw [tieBest, ite_eq_left ht]
    refine ⟨Or.inr ⟨h.ok.bounded i h.index, h.ok.live i h.index, hc.symm, hn⟩, ?_⟩
    have hbetter : better r.M (Flat.get w.candidates i) best
        (Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i)) cls = true := by
      rw [hc, better_tie (Flat.get w.candidates i) best cls hb]
      simp only [gt_iff_lt, ht, decide_true]
    have hs := pick_take h.index hd hcn hbetter
    rw [hc] at hs
    exact heq.trans hs
  · rw [tieBest, ite_eq_right ht]
    refine ⟨h.bestValid, ?_⟩
    have hbetter : better r.M (Flat.get w.candidates i) best
        (Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i)) cls = false := by
      rw [hc, better_tie (Flat.get w.candidates i) best cls hb]
      simp only [gt_iff_lt, ht, decide_false]
    exact heq.trans (pick_keep h.index hd hcn hbetter)

theorem tie_commit (h : PickAt P r F s ra w lo L i best cls t)
    (hm : w.Model r s) (heq : PickEq r w i best cls) (hb : best ≠ Flat.NONE)
    (hd : Flat.get w.droppedNow (Flat.get w.candidates i) = 0#8)
    (hc : Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i) = cls)
    (hn : cls ≠ Flat.NOCLASS)
    (hmem : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8
      (tieBest r.M (Flat.get w.candidates i) best).toInt)
    (hsp : u.regs.rsp = t.regs.rsp) (h12 : u.regs.r12 = t.regs.r12)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13)
    (hbx : u.regs.rbx = t.regs.rbx) (ha : al u = cls) : Pending P r F s ra u := by
  let next := tieBest r.M (Flat.get w.candidates i) best
  have hbu := h.bd.storeLocal (i := 1) (by simp) next hmem hsp
  rw [Lc.set_pending] at hbu
  have hnext := tie_model h heq hb hd hc hn
  refine ⟨w, lo, { L with pending := next }, i, next, cls,
    h.toCore.withPending hbu hsp h12 h14 h13, h.index, ?_, rfl, ha,
    hnext.1, hm, hnext.2⟩
  rw [hbx, hsp]
  exact h.rbx

end

section
variable [Host] [FunDecls]
  (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
  (hok : r.Ok)

include hok

theorem b_8 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.8" →
      Obl P r F s ra (loopPhase P r F s ra rest) (loopVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte, Tie] at ht
  obtain ⟨w, lo, L, i, best, cls, h, hm, heq, hb, hbp, hpend, hsi, hd, hc, hn⟩ := ht
  have hoff : (Flat.get w.candidates i).toNat < MAX_N :=
    Nat.lt_of_lt_of_le (BitVec.lt_def.mp (h.ok.bounded i h.index)) hok.planner.m
  have hbest : best.toNat < MAX_N :=
    Nat.lt_of_lt_of_le (BitVec.lt_def.mp ((h.bestValid.resolve_left hb).1)) hok.planner.m
  obtain ⟨R, hmp⟩ := RView.plan h.bd.kb.vmem
  have hso := MapM.isSome_dest hmp hoff
  have hsb := MapM.isSome_dest hmp hbest
  have hro := MapM.rd_dest hmp hoff
  have hrb := MapM.rd_dest hmp hbest
  change rd t.dmem (slotAt r.mp (Flat.get w.candidates i).toNat) =
    Flat.get r.M.dest (Flat.get w.candidates i) at hro
  change rd t.dmem (slotAt r.mp best.toNat) = Flat.get r.M.dest best at hrb
  have hao : t.regs.r12.toBitVec + t.regs.rbp.toBitVec * 8#64 =
      slotAt r.mp (Flat.get w.candidates i).toNat := by rw [h.r12, hbp, slotAt_mul]
  have hab : t.regs.r12.toBitVec + t.regs.r15.toBitVec * 8#64 =
      slotAt r.mp best.toNat := by rw [h.r12, h.r15, slotAt_mul]
  have hchoose :
      (if ((↑(rd t.dmem (t.regs.r12.toBitVec + t.regs.r15.toBitVec * 8#64) -
          rd t.dmem (t.regs.r12.toBitVec + t.regs.rbp.toBitVec * 8#64)).toNat : Int) !=
        (↑(rd t.dmem (t.regs.r12.toBitVec + t.regs.r15.toBitVec * 8#64)).toNat : Int) -
          ↑(rd t.dmem (t.regs.r12.toBitVec + t.regs.rbp.toBitVec * 8#64)).toNat) = true then
        t.regs.rbp.toBitVec else t.regs.r15.toBitVec) =
      tieBest r.M (Flat.get w.candidates i) best := by
    rw [hao, hab, hro, hrb, hbp, h.r15]
    simp only [bne_iff_ne, borrow_iff, ← BitVec.lt_def]
    rfl
  obtain ⟨Q, hml⟩ := h.bd.typedWord 1 (by decide)
  have hsl := Wd.isSome hml
  simp only [rd] at hchoose
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load =>
    first
    | (rw [hao]; exact hso)
    | (rw [hab]; exact hsb)
    | with_reducible exact hsl
  | other =>
    first
    | (simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
       apply tie_commit h hm heq hb hd hc hn
       · change t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 _ = _
         exact congrArg (fun x : Word => t.dmem.storeInt
           (t.regs.rsp.toBitVec + 8#64) 8 x.toInt) hchoose
       · rfl
       · rfl
       · rfl
       · rfl
       · rfl
       · change ((t.regs.rsi.toBitVec.extractLsb' 0 32).setWidth 64).setWidth 8 = cls
         simp only [Reg64s.get64_rsi] at hsi
         rw [low8_movl]
         exact hsi)
    | (left
       simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
       symexec_norm at ⊢
       rw [rd_store_other _ (by bv_omega)]
       omega)

end
end FlatShuffler.Unit.ResolveU
