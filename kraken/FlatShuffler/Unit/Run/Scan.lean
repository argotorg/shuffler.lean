module

public import FlatShuffler.Unit.Run.Return
import all FlatShuffler.Unit.Run.Return

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.RunU
open FlatShuffler.Sep

theorem succ_nat {i n : Word} (h : i < n) : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
theorem succ_lt {i n : Word} (h : i < n) (hne : n ≠ i + 1#64) : i + 1#64 < n := by bv_omega

section
variable [Host] [FunDecls] (S PM : Addr) (planned : Vector Word maxStackSize)
    (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_3 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.5" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hcx, hi, hsize, hscan⟩ := ht
  have hiM : t.regs.rax.toBitVec.toNat < maxStackSize := Nat.lt_of_lt_of_le hi h.ok.n
  have hpos := h.bd.rd_pos h.ok hi
  unfold rd at hpos
  have lm := View.isSome_pos h.bd.mem hiM
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [h.bp, Fld.fold_mapping_positionOf, hpos, neg_one_eq_none] at *
  vc_by_shape
  | load => exact lm
  | goto ".LB.Emission.run.4" =>
    have hstep := (unmapped_step (st := flat a) hi (c := t.regs.rdx.toBitVec)).symm.trans hscan
    cfg_goto
    · exact (h.bd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, l, lo, w, ?_, h12, hcx, hi, hsize, ?_⟩
      · apply h.next <;> rfl
      · first
        | (rw [ite_eq_right ?_] at hstep
           · simpa only [BitVec.add_comm 1#64] using hstep
           · apply Generate.ne_of_z
             rw [← Bool.not_eq_true']
             with_reducible assumption)
        | (rw [ite_eq_left ?_] at hstep
           · simpa only [BitVec.add_comm 1#64] using hstep
           · apply Generate.eq_of_z
             rw [← Bool.not_eq_false']
             with_reducible assumption)
    · simp only [V, Names.run, String.reduceEq, ↓reduceIte]
      omega

theorem b_2 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.4" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hcx, hi, hsize, hscan⟩ := ht
  have hin : t.regs.rax.toBitVec.toNat < maxStackSize := Nat.lt_of_lt_of_le hi h.ok.n
  have hn := succ_nat hi
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.run.10" =>
    rename_i hj
    have he : a.h.n = t.regs.rax.toBitVec + 1#64 := by
      apply Generate.eq_of_z
      simpa only [h12, BitVec.add_comm 1#64] using hj
    have hs : t.regs.rdx.toBitVec = Flat.unmappedFrom (flat a) 0#64 0#64 := by
      have hend := unmapped_end (st := flat a) (c := t.regs.rdx.toBitVec)
      change Flat.unmappedFrom (flat a) a.h.n t.regs.rdx.toBitVec = _ at hend
      rw [he] at hend
      exact hend.symm.trans hscan
    cfg_goto
    · exact (h.bd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, l, lo, w, ?_, h12, hcx, ?_, hsize, hs⟩
      · apply h.next <;> rfl
      · intro hz
        have hh := BitVec.lt_def.mp hi
        rw [hz] at hh
        exact Nat.not_lt_zero _ hh
    · simp only [V, Names.run, String.reduceEq, ↓reduceIte]
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
       refine ⟨a, l, lo, w, ?_, h12, hcx, ?_, hsize, ?_⟩
       · apply h.next <;> rfl
       · simpa only [BitVec.add_comm 1#64] using succ_lt hi he
       · simpa only [BitVec.add_comm 1#64] using hscan)

end
end FlatShuffler.Unit.RunU
