module

public import FlatShuffler.Unit.Plan.ResolveLoopDefs
import all FlatShuffler.Unit.Plan.ResolveLoopDefs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

theorem cursor_distance (a : Addr) (count i : Word)
    (hc : count.toNat ≤ MAX_N) (hi : i ≤ count) :
    ((a + 48#64 + 8#64 * count) - (a + 48#64 + 8#64 * i)).toNat =
      8 * (count.toNat - i.toNat) := by
  change count.toNat ≤ 1024 at hc
  bv_omega

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {w : Work} {lo : List Word} {L : Lc} {i best : Word} {cls : BitVec 8}

theorem pick_advance (h : PickAt P r F s ra w lo L i best cls t)
    (hm : w.Model r s) (heq : PickEq r w (i + 1) best cls)
    (hi : i + 1 < w.count)
    (hmem : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (h15 : u.regs.r15 = t.regs.r15)
    (hbx : u.regs.rbx.toBitVec = 8#64 + t.regs.rbx.toBitVec) : Pick P r F s ra u := by
  refine ⟨w, lo, L, i + 1, best, cls,
    ⟨h.toCore.next hmem hsp h12 h14 h13, hi, ?_, h15 ▸ h.r15,
      h.bestClass, h.bestValid⟩, hm, heq⟩
  rw [hbx, h.rbx, hsp]
  bv_omega

theorem pick_finish (h : PickAt P r F s ra w lo L i best cls t)
    (hm : w.Model r s) (heq : PickEq r w (i + 1) best cls)
    (hi : i + 1 = w.count)
    (hmem : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (h15 : u.regs.r15 = t.regs.r15) :
    PickEnd P r F s ra u := by
  have he : w.pick r = (best, cls) := by
    rw [PickEq, hi, pick_done (by bv_omega)] at heq
    exact heq
  exact ⟨w, lo, L, h.toCore.next hmem hsp h12 h14 h13, hm,
    (h15 ▸ h.r15).trans (congrArg Prod.fst he).symm,
    h.bestClass.trans (congrArg Prod.snd he).symm⟩

end

section
variable [Host] [FunDecls]
  (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)

theorem b_10 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.10" →
      Obl P r F s ra (loopPhase P r F s ra rest) (loopVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte, PickNext] at ht
  obtain ⟨w, lo, L, i, best, cls, h, hm, heq⟩ := ht
  have hc := h.ok.count
  have hi0 := h.index
  have hi0N := BitVec.lt_def.mp hi0
  change w.count.toNat ≤ 1024 at hc
  have hiN : (i + 1).toNat = i.toNat + 1 :=
    small_succ i (Nat.lt_of_lt_of_le (BitVec.lt_def.mp h.index) h.ok.count)
  have hi : i + 1 ≤ w.count := by bv_omega
  have hd0 := cursor_distance t.regs.rsp.toBitVec w.count i h.ok.count (by bv_omega)
  have hd1 := cursor_distance t.regs.rsp.toBitVec w.count (i + 1) h.ok.count hi
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.Planner.resolve.12" =>
    rename_i hj
    symexec_norm at hj
    have he : i + 1 = w.count := by
      have hh : 8#64 + t.regs.rbx.toBitVec = t.regs.r13.toBitVec := by
        exact (show t.regs.r13.toBitVec = 8#64 + t.regs.rbx.toBitVec from by
          simpa only [sub_beq_zero, beq_iff_eq] using hj).symm
      rw [h.rbx, h.r13] at hh
      bv_omega
    cfg_goto
    · exact h.bd.kb.stack (by decide)
    · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
      exact pick_finish h hm heq he rfl rfl rfl rfl rfl rfl
    · left
      simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
      symexec_norm at ⊢
      rw [h.r13, h.rbx, hd0]
      omega
  | other =>
    rename_i hj
    symexec_norm at hj
    have hn : i + 1 ≠ w.count := by
      intro he
      have hh : 8#64 + t.regs.rbx.toBitVec = t.regs.r13.toBitVec := by
        rw [h.rbx, h.r13, ← he]
        bv_omega
      simp only [hh, BitVec.sub_self] at hj
      change true = false at hj
      cases hj
    first
    | (simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte]
       exact pick_advance h hm heq (by bv_omega) rfl rfl rfl rfl rfl rfl rfl)
    | (left
       simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte, loopBase]
       symexec_norm at ⊢
       have he : t.regs.r13.toBitVec - (8#64 + t.regs.rbx.toBitVec) =
           (t.regs.rsp.toBitVec + 48#64 + 8#64 * w.count) -
             (t.regs.rsp.toBitVec + 48#64 + 8#64 * (i + 1)) := by
         rw [h.r13, h.rbx]
         bv_omega
       rw [he, h.r13, h.rbx, hd0, hd1]
       omega)

end
end FlatShuffler.Unit.ResolveU
