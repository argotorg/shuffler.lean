import BbuKraken.Unit.Run.Scan

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.RunU
open Bbu.Sep

section
variable [Host] [FunDecls] (S PM : Addr) (planned : Vector Word MAX_N)
    (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_10
    (hav : VSpec (RunView PM planned) G.Ok Names.isAvailable isAvailableA 3 isAvailableQ) :
    runAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.run.10" → Obl S PM planned g F s ra blk := by
  simp only [Names.isAvailable] at hav
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, h12, hi, hsize, hcount, hscan⟩ := ht
  have hin : t.regs.rbp.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hi h.ok.n
  have hsuc := succ_nat hi
  kvcgen64 [hav]
  all_goals try symexec_norm at ⊢
  refine Bd.call (h.bd.next rfl rfl rfl rfl rfl) (by decide) h.bx h.ok hi ?_
  intro u a' lo' w' hbd hq hok hag
  obtain ⟨he, hq⟩ := hq
  subst a'
  have hq' : al u = if Flat.isAvailable (flat a) t.regs.rbp.toBitVec then 1#8 else 0#8 := hq
  have hbp : u.regs.rbp.toBitVec = t.regs.rbp.toBitVec := by
    rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]
  have h12' : u.regs.r12.toBitVec = a.h.n := by
    rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]
    exact h12
  have hbx : u.regs.rbx.toBitVec = S := by
    rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]
    exact h.bx
  have hu : Phase S PM planned g a F s ra l lo' w' u :=
    ⟨hbd, hbx, hok, h.keep, h.model⟩
  have hrd : rd u.dmem S = a.h.tgt := rd_of_eq hbd.mem (by unfold View Em; ecancel)
  have lm : (u.dmem.loadInt S 8).isSome = true :=
    isSome_of_eq a.h.tgt hbd.mem (by unfold View Em; ecancel)
  unfold rd at hrd
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hbp, h12', hbx, hrd] at ⊢
  vc_by_shape
  | load => exact lm
  | goto ".LB.Emission.run.6" =>
    have hz : al u = 0#8 := by
      apply al_zero
      rw [Bool.not_eq_false']
      with_reducible assumption
    have hfalse := bit_zero hq' hz
    have hfail : Flat.availableFrom (flat a) 0#64 = false := by
      rw [available_step hi, hfalse, Bool.false_and] at hscan
      exact hscan.symm
    cfg_goto
    · exact (hbd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, l, lo', w', ?_, hfail⟩
      apply hu.next <;> rfl
    · simp [V, Names.run]
      omega
  | goto ".LB.Emission.run.10" =>
    rename_i hjal hjn
    simp only [hbp, h12', BitVec.add_comm 1#64] at hjn
    have hz : al u ≠ 0#8 := by
      apply al_ne
      rw [Bool.not_eq_true']
      with_reducible assumption
    have htrue := bit_ne_zero hq' hz
    have hrest : Flat.availableFrom (flat a) (t.regs.rbp.toBitVec + 1#64) =
        Flat.availableFrom (flat a) 0#64 := by
      rw [available_step hi, htrue, Bool.true_and] at hscan
      exact hscan
    have hne : a.h.n ≠ t.regs.rbp.toBitVec + 1#64 := by
      apply Generate.ne_of_z
      rw [← Bool.not_eq_true']
      with_reducible assumption
    cfg_goto
    · exact (hbd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, l, lo', w', ?_, h12', ?_, hsize, hcount, ?_⟩
      · apply hu.next <;> rfl
      · simpa only [hbp, BitVec.add_comm 1#64] using succ_lt hi hne
      · simpa only [hbp, BitVec.add_comm 1#64] using hrest
    · left
      simp only [V, Names.run, String.reduceEq, ↓reduceIte]
      rw [BitVec.add_comm 1#64, hsuc]
      omega
  | goto ".LB.Emission.run.5" =>
    rename_i hjal hjn
    simp only [hbp, h12', BitVec.add_comm 1#64] at hjn
    have hz : al u ≠ 0#8 := by
      apply al_ne
      rw [Bool.not_eq_true']
      with_reducible assumption
    have htrue := bit_ne_zero hq' hz
    have hrest : Flat.availableFrom (flat a) (t.regs.rbp.toBitVec + 1#64) =
        Flat.availableFrom (flat a) 0#64 := by
      rw [available_step hi, htrue, Bool.true_and] at hscan
      exact hscan
    have he : a.h.n = t.regs.rbp.toBitVec + 1#64 := by
      apply Generate.eq_of_z
      rw [← Bool.not_eq_false']
      with_reducible assumption
    have hpassed : Flat.availableFrom (flat a) 0#64 = true := by
      have hend := available_end (flat a)
      change Flat.availableFrom (flat a) a.h.n = true at hend
      rw [he] at hend
      exact hrest.symm.trans hend
    cfg_goto
    · exact (hbd.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a, l, lo', w', ?_, h12', by trivial, ?_, hsize, hcount, hpassed, by trivial⟩
      · apply hu.next <;> rfl
      · show 0#64 < a.h.n
        bv_omega
    · simp [V, Names.run, MAX_N]
      omega

end
end Bbu.Unit.RunU
