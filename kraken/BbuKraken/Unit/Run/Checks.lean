module

public import BbuKraken.Unit.Run.Return
import all BbuKraken.Unit.Run.Return

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.RunU
open Bbu.Sep

section
variable [Host] [FunDecls] (S PM : Addr) (planned : Vector Word MAX_N)
    (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_7 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.7" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, hcx, hn, hsize⟩ := ht
  have hm : Flat.unmappedFrom (flat a) 0#64 0#64 = 0#64 := by
    rw [show 0#64 = (flat a).targetSize from hn.symm, unmapped_end]
  have ha : Flat.availableFrom (flat a) 0#64 = true := by
    rw [show 0#64 = (flat a).targetSize from hn.symm, available_end]
  have hl : Flat.labelsFrom (flat a) 0#64 = true := by
    rw [show 0#64 = (flat a).targetSize from hn.symm, labels_end]
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.run.0" =>
    have hne : t.regs.rcx.toBitVec ≠ 0#64 := by
      apply ShallowestCopy.zf_false
      rw [← Bool.not_eq_true']
      with_reducible assumption
    have hfail : Flat.unmappedFrom (flat a) 0#64 0#64 ≠ a.h.pend := by
      rw [hm]
      exact fun he => hne (hcx.trans he.symm)
    cfg_goto
    · exact (h.bd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, lo, w, ?_, h.ok, h.result (finish_unmapped hfail) rfl⟩
      apply h.bd.next <;> rfl
    · simp [V, Names.run]
  | other =>
    have hz : t.regs.rcx.toBitVec = 0#64 := by
      apply ShallowestCopy.zf_true
      rw [← Bool.not_eq_false']
      with_reducible assumption
    first
    | (left; simp [V, Names.run])
    | (simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
       refine ⟨a, l, lo, w, ?_, hsize, ?_, ha, hl⟩
       · apply h.next <;> rfl
       · exact hm.trans (hz.symm.trans hcx))

theorem b_9 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.9" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hcx, hn, hsize, hcount⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.run.0" =>
    have hne : t.regs.rcx.toBitVec ≠ t.regs.rdx.toBitVec := by
      apply Generate.ne_of_z
      rw [← Bool.not_eq_true']
      with_reducible assumption
    have hfail : Flat.unmappedFrom (flat a) 0#64 0#64 ≠ a.h.pend := by
      rw [← hcount, ← hcx]
      exact Ne.symm hne
    cfg_goto
    · exact (h.bd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, lo, w, ?_, h.ok, h.result (finish_unmapped hfail) rfl⟩
      apply h.bd.next <;> rfl
    · simp [V, Names.run]
  | other =>
    have he : t.regs.rcx.toBitVec = t.regs.rdx.toBitVec := by
      apply Generate.eq_of_z
      rw [← Bool.not_eq_false']
      with_reducible assumption
    first
    | (left; simp [V, Names.run, MAX_N])
    | (simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
       refine ⟨a, l, lo, w, ?_, h12, ?_, hsize, ?_, by trivial⟩
       · apply h.next <;> rfl
       · show 0#64 < a.h.n
         bv_omega
       · exact hcount.symm.trans (he.symm.trans hcx))

end
end Bbu.Unit.RunU
