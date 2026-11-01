module

public import BbuKraken.Unit.Run.Calls
import all BbuKraken.Unit.Run.Calls

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

theorem b_1 (hs : Safe planned (flat g) g.xo)
    (hlow : VSpec (RunView PM planned) G.Ok Names.permuteAtLowestHeight
      (lowestA planned) lowestD (lowestQ planned)) :
    runAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.run.1" → Obl S PM planned g F s ra blk := by
  simp only [Names.permuteAtLowestHeight] at hlow
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, lo, w, hbd, hbx, hok, hkeep, hremove⟩ := ht
  kvcgen64 [hlow]
  all_goals try symexec_norm at ⊢
  refine Bd.call (hbd.next rfl rfl rfl rfl rfl) (Nat.le_refl _) hbx hok
    (lowest_pre hok hkeep hs hremove) ?_
  intro u a' lo' w' hbd' hq hok' hag
  obtain ⟨l, hk, hf, hal⟩ := hq
  have hkeep' : Keep g a' := ProduceProof.Keep.trans hkeep hk
  have hbx' : u.regs.rbx.toBitVec = S := by
    rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]
    exact hbx
  have hphase (hd : (Flat.permuteAtLowestHeight planned l (flat a)).1 = .done) :
      Phase S PM planned g a' F s ra l lo' w' u := by
    refine ⟨hbd', hbx', hok', hkeep', ?_, ?_⟩
    · exact congrArg Prod.fst hremove
    · rw [hremove]
      exact Prod.ext hd hf.symm
  have hp : rd u.dmem (S + 16440#64) = a'.h.pend :=
    rd_of_eq hbd'.mem (by unfold View Em; ecancel)
  have hn : rd u.dmem (S + 8#64) = a'.h.n :=
    rd_of_eq hbd'.mem (by unfold View Em; ecancel)
  have hlen : rd u.dmem (S + 32#64) = a'.h.len :=
    rd_of_eq hbd'.mem (by unfold View Em; ecancel)
  have lm0 : (u.dmem.loadInt (S + 16440#64) 8).isSome = true :=
    isSome_of_eq a'.h.pend hbd'.mem (by unfold View Em; ecancel)
  have lm1 : (u.dmem.loadInt (S + 8#64) 8).isSome = true :=
    isSome_of_eq a'.h.n hbd'.mem (by unfold View Em; ecancel)
  have lm2 : (u.dmem.loadInt (S + 32#64) 8).isSome = true :=
    isSome_of_eq a'.h.len hbd'.mem (by unfold View Em; ecancel)
  unfold rd at hp hn hlen
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hbx', hp, hn, hlen] at *
  vc_by_shape
  | load => run_loads [lm0, lm1, lm2]
  | goto ".LB.Emission.run.0" =>
    by_cases hd : (Flat.permuteAtLowestHeight planned l (flat a)).1 = .done
    · have hz : al u = 0#8 := by
        change BitVec.setWidth 8 u.regs.rax.toBitVec = 0#8
        rw [hal, hd]
        rfl
      first
      | (exfalso
         apply al_ne ?_ hz
         with_reducible assumption)
      | (have hne : a'.h.len + a'.h.pend ≠ a'.h.n := by
           apply Generate.ne_of_z
           rw [← Bool.not_eq_true']
           with_reducible assumption
         have hfail : (flat a').size + (flat a').pend ≠ (flat a').targetSize := by
           simpa only [flat, BitVec.add_comm] using hne
         cfg_goto
         · exact (hbd'.kb.next rfl rfl).stack (by decide)
         · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
           refine ⟨a', lo', w', ?_, hok', (hphase hd).result (finish_size hfail) rfl⟩
           apply hbd'.next <;> rfl
         · simp [V, Names.run])
    · first
      | (exfalso
         apply hd
         apply code_eq_zero
         apply Eq.trans hal.symm
         apply al_zero
         with_reducible assumption)
      | (have he : Flat.emissionRun planned l (flat g) =
             Flat.permuteAtLowestHeight planned l (flat a) := by
           rw [emission_lowest hremove, ite_eq_left hd]
         cfg_goto
         · exact (hbd'.kb.next rfl rfl).stack (by decide)
         · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
           refine ⟨a', lo', w', ?_, hok', l, hkeep', ?_, ?_⟩
           · apply hbd'.next <;> rfl
           · rw [he]; exact hf
           · rw [he]; exact hal
         · simp [V, Names.run])
  | goto ".LB.Emission.run.7" =>
    have hd := code_eq_zero (hal.symm.trans (al_zero (by with_reducible assumption)))
    have hn0 : a'.h.n = 0#64 := by
      apply ShallowestCopy.zf_true
      with_reducible assumption
    have he : a'.h.len + a'.h.pend = a'.h.n := by
      apply Generate.eq_of_z
      rw [← Bool.not_eq_false']
      with_reducible assumption
    cfg_goto
    · exact (hbd'.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a', l, lo', w', ?_, by trivial, hn0, ?_⟩
      · apply (hphase hd).next <;> rfl
      · simpa only [BitVec.add_comm] using he
    · simp [V, Names.run]
  | goto ".LB.Emission.run.3" =>
    have hd := code_eq_zero (hal.symm.trans (al_zero (by with_reducible assumption)))
    have hn0 : a'.h.n ≠ 0#64 := by
      apply ShallowestCopy.zf_false
      with_reducible assumption
    have he : a'.h.len + a'.h.pend = a'.h.n := by
      apply Generate.eq_of_z
      rw [← Bool.not_eq_false']
      with_reducible assumption
    cfg_goto
    · exact (hbd'.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a', l, lo', w', ?_, by trivial, by trivial, ?_, ?_, by trivial⟩
      · apply (hphase hd).next <;> rfl
      · show 0#64 < a'.h.n
        bv_omega
      · simpa only [BitVec.add_comm] using he
    · simp [V, Names.run, MAX_N]

end
end Bbu.Unit.RunU
