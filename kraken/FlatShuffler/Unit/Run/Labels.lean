module

public import FlatShuffler.Unit.Run.Scan
import all FlatShuffler.Unit.Run.Scan
public import FlatShuffler.Unit.Run.Load
import all FlatShuffler.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.RunU
open FlatShuffler.Sep

theorem eq_of_z8 {a b : BitVec 8} (h : (a - b == BitVec.zero 8) = true) : a = b := by
  have he := beq_iff_eq.mp h
  change a - b = 0#8 at he
  bv_omega

theorem ne_of_z8 {a b : BitVec 8} (h : (a - b == BitVec.zero 8) = false) : a ≠ b := by
  have he := beq_eq_false_iff_ne.mp h
  change a - b ≠ 0#8 at he
  bv_omega

section
variable [Host] [FunDecls] (S PM : Addr) (planned : Vector Word maxStackSize)
    (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_5 (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels runAsm, label l ≠ label "exit") : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.8" → Obl S PM planned g F s ra blk := by
  have he := ProofKit.external_call_spec "exit" hexit
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hdx, hi, hsize, hcount, havail, hscan⟩ := ht
  have hiM : t.regs.rax.toBitVec.toNat < maxStackSize := Nat.lt_of_lt_of_le hi h.ok.n
  have hpos := h.bd.rd_pos h.ok hi
  have hkind := h.bd.kind h.ok hi
  unfold rd at hpos
  unfold rdb at hkind
  have lm0 := View.isSome_pos h.bd.mem hiM
  obtain ⟨_, hbyte⟩ := View.b8_tgt h.bd.mem hi (j := 4) (by decide)
  have lm1 := B8.isSome hbyte
  kvcgen64 [he]
  all_goals try symexec_norm
  all_goals try simp only [h.bp, hdx, Fld.fold_mapping_positionOf] at ⊢
  all_goals try simp only [fold_slot, hpos, hkind, neg_one_eq_none] at ⊢
  vc_by_shape
  | load => first | run_loads [lm0, lm1] | exact h.bd.isSome_exit
  | goto ".LB.Emission.run.7" =>
    rename_i hj
    simp only [h.bp, hdx, Fld.fold_mapping_positionOf] at hj
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
  | jumpOut =>
    rename_i exitra hkindFlag hposFlag
    simp only [h.bp, hdx, Fld.fold_mapping_positionOf] at hkindFlag hposFlag
    simp only [fold_slot, hpos, hkind, neg_one_eq_none] at hkindFlag hposFlag
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
    apply ProofKit.intercept_exit (E := E S PM planned g F s ra) hout
    refine Or.inr ⟨rfl, rfl, h.bd.exitPost h.ok exitra rfl ?_⟩
    exact h.exit (finish_labels hfail)

theorem b_4 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.7" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hdx, hi, hsize, hcount, havail, hscan⟩ := ht
  have hin : t.regs.rax.toBitVec.toNat < maxStackSize := Nat.lt_of_lt_of_le hi h.ok.n
  have hn := succ_nat hi
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.run.9" =>
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
end FlatShuffler.Unit.RunU
