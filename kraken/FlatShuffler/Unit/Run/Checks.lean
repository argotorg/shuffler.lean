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

section
variable [Host] [FunDecls] (S PM : Addr) (planned : Vector Word maxStackSize)
    (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_9 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.10" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hcx, hn, hsize, hcount⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.run.2" =>
    have hne : t.regs.rcx.toBitVec ≠ t.regs.rdx.toBitVec := by
      apply Generate.ne_of_z
      rw [← Bool.not_eq_true']
      with_reducible assumption
    have hfail : Flat.unmappedFrom (flat a) 0#64 0#64 ≠ a.h.pend := by
      rw [← hcount, ← hcx]
      exact Ne.symm hne
    cfg_goto
    · exact (h.bd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Failed, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, lo, w, ?_, h.ok, h.exit (finish_unmapped hfail)⟩
      apply h.bd.next <;> rfl
    · simp [V, Names.run]
  | other =>
    have he : t.regs.rcx.toBitVec = t.regs.rdx.toBitVec := by
      apply Generate.eq_of_z
      rw [← Bool.not_eq_false']
      with_reducible assumption
    first
    | (left; simp [V, Names.run, maxStackSize])
    | (simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
       refine ⟨a, l, lo, w, ?_, h12, ?_, hsize, ?_, by trivial⟩
       · apply h.next <;> rfl
       · show 0#64 < a.h.n
         bv_omega
       · exact hcount.symm.trans (he.symm.trans hcx))

end
end FlatShuffler.Unit.RunU
