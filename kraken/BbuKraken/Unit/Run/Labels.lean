module

public import BbuKraken.Unit.Run.Scan
import all BbuKraken.Unit.Run.Scan
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.RunU
open Bbu.Sep

theorem eq_of_z8 {a b : BitVec 8} (h : (a - b == BitVec.zero 8) = true) : a = b := by
  have he := beq_iff_eq.mp h
  change a - b = 0#8 at he
  bv_omega

theorem ne_of_z8 {a b : BitVec 8} (h : (a - b == BitVec.zero 8) = false) : a ≠ b := by
  have he := beq_eq_false_iff_ne.mp h
  change a - b ≠ 0#8 at he
  bv_omega

section
variable [Host] [FunDecls] (S PM : Addr) (planned : Vector Word MAX_N)
    (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_5 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.5" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hdx, hi, hsize, hcount, havail, hscan⟩ := ht
  have hiM : t.regs.rax.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hi h.ok.n
  have hpos := h.bd.rd_pos h.ok hi
  have hkind := h.bd.kind h.ok hi
  unfold rd at hpos
  unfold rdb at hkind
  have lm0 := View.isSome_pos h.bd.mem hiM
  obtain ⟨_, hbyte⟩ := View.b8_tgt h.bd.mem hi (j := 4) (by decide)
  have lm1 := B8.isSome hbyte
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [h.bx, hdx, Fld.fold_mapping_positionOf] at ⊢
  all_goals try simp only [fold_slot, hpos, hkind, neg_one_eq_none] at ⊢
  vc_by_shape
  | load => run_loads [lm0, lm1]
  | goto ".LB.Emission.run.4" =>
    rename_i hj
    simp only [h.bx, hdx, Fld.fold_mapping_positionOf] at hj
    simp only [fold_slot, hpos, hkind, neg_one_eq_none] at hj
    have hpass : (Flat.get (flat a).target t.regs.rax.toBitVec).kind ≠ FunctionReturnLabel ∨
        Flat.get (flat a).pos t.regs.rax.toBitVec ≠ Flat.NONE := by
      first
      | (left
         change (Flat.get (flat a).target t.regs.rax.toBitVec).kind ≠ 3#8
         apply ne_of_z8
         rw [← Bool.not_eq_true']
         with_reducible assumption)
      | (right
         apply Generate.ne_of_z
         rw [← Bool.not_eq_true']
         with_reducible assumption)
    cfg_goto
    · exact (h.bd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, l, lo, w, ?_, h12, hdx, hi, hsize, hcount, havail,
        (labels_pass (st := flat a) hi hpass).symm.trans hscan⟩
      apply h.next <;> rfl
    · simp [V, Names.run]
  | goto ".LB.Emission.run.0" =>
    rename_i hjkind hjpos
    simp only [h.bx, hdx, Fld.fold_mapping_positionOf] at hjkind hjpos
    simp only [fold_slot, hpos, hkind, neg_one_eq_none] at hjkind hjpos
    have hk : (Flat.get (flat a).target t.regs.rax.toBitVec).kind = FunctionReturnLabel := by
      change (Flat.get (flat a).target t.regs.rax.toBitVec).kind = 3#8
      apply eq_of_z8
      rw [← Bool.not_eq_false']
      with_reducible assumption
    have hp : Flat.get (flat a).pos t.regs.rax.toBitVec = Flat.NONE := by
      apply Generate.eq_of_z
      rw [← Bool.not_eq_false']
      with_reducible assumption
    have hfail : Flat.labelsFrom (flat a) 0#64 = false :=
      hscan.symm.trans (labels_fail (st := flat a) hi hk hp)
    cfg_goto
    · exact (h.bd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, lo, w, ?_, h.ok, h.result (finish_labels hfail) rfl⟩
      apply h.bd.next <;> rfl
    · simp [V, Names.run]
      omega

theorem b_4 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.4" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hdx, hi, hsize, hcount, havail, hscan⟩ := ht
  have hin : t.regs.rax.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hi h.ok.n
  have hn := succ_nat hi
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.run.8" =>
    rename_i hj
    have he : a.h.n = t.regs.rax.toBitVec + 1#64 := by
      apply Generate.eq_of_z
      simpa only [h12, BitVec.add_comm 1#64] using hj
    have hl : Flat.labelsFrom (flat a) 0#64 = true := by
      have hend := labels_end (flat a)
      change Flat.labelsFrom (flat a) a.h.n = true at hend
      rw [he] at hend
      exact hscan.symm.trans hend
    cfg_goto
    · exact (h.bd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, l, lo, w, ?_, hsize, hcount, havail, hl⟩
      apply h.next <;> rfl
    · simp [V, Names.run]
      omega
  | other =>
    rename_i hj
    have he : a.h.n ≠ t.regs.rax.toBitVec + 1#64 := by
      apply Generate.ne_of_z
      simpa only [h12, BitVec.add_comm 1#64] using hj
    first
    | (left
       simp only [V, Names.run, String.reduceEq, ↓reduceIte]
       rw [BitVec.add_comm 1#64, hn]
       omega)
    | (simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
       refine ⟨a, l, lo, w, ?_, h12, hdx, ?_, hsize, hcount, havail, ?_⟩
       · apply h.next <;> rfl
       · simpa only [BitVec.add_comm 1#64] using succ_lt hi he
       · simpa only [BitVec.add_comm 1#64] using hscan)

end
end Bbu.Unit.RunU
