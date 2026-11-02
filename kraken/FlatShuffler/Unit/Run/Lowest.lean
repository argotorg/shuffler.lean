module

public import FlatShuffler.Unit.Run.Calls
import all FlatShuffler.Unit.Run.Calls

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

theorem b_1 (hs : Safe planned (flat g) g.xo)
    (hout : ∀ l ∈ Program.labels runAsm, label l ≠ label "exit")
    (hlow : VSpecWithExit (RunView PM planned) G.Ok Names.permuteAtLowestHeight
      (lowestA planned) lowestD (lowestQ planned) (lowestX planned)) :
    runAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.run.1" → Obl S PM planned g F s ra blk := by
  simp only [Names.permuteAtLowestHeight] at hlow
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, lo, w, hbd, hbx, hok, hkeep, hremove⟩ := ht
  kvcgen64 [hlow]
  all_goals try symexec_norm at ⊢
  refine Bd.callWithExit (k := lowestD) (A := lowestA planned)
    (Q := lowestQ planned) (X := lowestX planned)
    (t := { t with regs := { t.regs with rdi := t.regs.rbp } })
    (hbd.next rfl rfl rfl rfl rfl) (Nat.le_refl _) hbx hok
    (lowest_pre hok hkeep hs hremove) ?_ (by
      intro tx hp harg
      apply ProofKit.intercept_exit (E := E S PM planned g F s ra) hout
      refine Or.inr ⟨rfl, harg, post_imp hp ?_⟩
      intro a' hx
      obtain ⟨l, hk, hf, hfail⟩ := hx
      have he : Flat.emissionRun planned l (flat g) =
          Flat.permuteAtLowestHeight planned l (flat a) := by
        rw [emission_lowest hremove, ite_eq_left (by rw [hfail]; decide)]
      refine ⟨l, ProduceProof.Keep.trans hkeep hk, ?_, ?_⟩
      · rw [he]; exact hf
      · rw [he]; exact hfail)
  intro u a' lo' w' hbd' hq hok' hag
  obtain ⟨l, hk, hf, hal⟩ := hq
  have hkeep' : Keep g a' := ProduceProof.Keep.trans hkeep hk
  have hbx' : u.regs.rbp.toBitVec = S := by
    rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]
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
    have hd : (Flat.permuteAtLowestHeight planned l (flat a)).1 ≠ .done :=
      code_ne_zero (fun he => al_ne (by with_reducible assumption) (Option.some.inj (hal.trans he)))
    have he : Flat.emissionRun planned l (flat g) =
        Flat.permuteAtLowestHeight planned l (flat a) := by
      rw [emission_lowest hremove, ite_eq_left hd]
    cfg_goto
    · exact (hbd'.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a', lo', w', ?_, hok', l, hkeep', ?_, ?_⟩
      · apply hbd'.next <;> rfl
      · rw [he]; exact hf
      · rw [he]; exact hal
    · simp [V, Names.run]
  | goto ".LB.Emission.run.3" =>
    have hd := code_eq_zero (hal.symm.trans (congrArg some (al_zero (by with_reducible assumption))))
    have hne : a'.h.len + a'.h.pend ≠ a'.h.n := by
      apply Generate.ne_of_z
      rw [← Bool.not_eq_true']
      with_reducible assumption
    have hfail : (flat a').size + (flat a').pend ≠ (flat a').targetSize := by
      simpa only [flat, BitVec.add_comm] using hne
    cfg_goto
    · exact (hbd'.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Failed, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a', lo', w', ?_, hok', (hphase hd).exit (finish_size hfail)⟩
      apply hbd'.next <;> rfl
    · simp [V, Names.run]
  | goto ".LB.Emission.run.5" =>
    have hd := code_eq_zero (hal.symm.trans (congrArg some (al_zero (by with_reducible assumption))))
    have hn0 : a'.h.n ≠ 0#64 := by
      apply ShallowestCopy.zf_false
      rw [← Bool.not_eq_true']
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
    · simp [V, Names.run, maxStackSize]
  | goto ".LB.Emission.run.9" =>
    have hd := code_eq_zero (hal.symm.trans (congrArg some (al_zero (by with_reducible assumption))))
    have hn0 : a'.h.n = 0#64 := by
      apply ShallowestCopy.zf_true
      rw [← Bool.not_eq_false']
      with_reducible assumption
    have hp0 : a'.h.pend = 0#64 := by
      apply ShallowestCopy.zf_true
      with_reducible assumption
    have hsize : a'.h.len + a'.h.pend = a'.h.n := by
      apply Generate.eq_of_z
      rw [← Bool.not_eq_false']
      with_reducible assumption
    have hm : Flat.unmappedFrom (flat a') 0#64 0#64 = 0#64 := by
      rw [show 0#64 = (flat a').targetSize from hn0.symm, unmapped_end]
    have ha : Flat.availableFrom (flat a') 0#64 = true := by
      rw [show 0#64 = (flat a').targetSize from hn0.symm, available_end]
    have hl : Flat.labelsFrom (flat a') 0#64 = true := by
      rw [show 0#64 = (flat a').targetSize from hn0.symm, labels_end]
    cfg_goto
    · exact (hbd'.kb.next rfl rfl).stack (by decide)
    · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a', l, lo', w', ?_, hsize, hm.trans hp0.symm, ha, hl⟩
      apply (hphase hd).next <;> rfl
    · simp [V, Names.run]
  | closed => simp [V, Names.run]
  | other =>
    first
    | (left; simp [V, Names.run])
    | have hd := code_eq_zero (hal.symm.trans (congrArg some (al_zero (by with_reducible assumption))))
      have hn0 : a'.h.n = 0#64 := by
        apply ShallowestCopy.zf_true
        rw [← Bool.not_eq_false']
        with_reducible assumption
      have hp0 : a'.h.pend ≠ 0#64 := by
        apply ShallowestCopy.zf_false
        with_reducible assumption
      have hm : Flat.unmappedFrom (flat a') 0#64 0#64 = 0#64 := by
        rw [show 0#64 = (flat a').targetSize from hn0.symm, unmapped_end]
      have hfail : Flat.unmappedFrom (flat a') 0#64 0#64 ≠ a'.h.pend := by
        rw [hm]
        exact Ne.symm hp0
      simp only [Inv, Failed, Names.run, String.reduceEq, ↓reduceIte]
      refine ⟨a', lo', w', ?_, hok', (hphase hd).exit (finish_unmapped hfail)⟩
      apply hbd'.next <;> rfl

end
end FlatShuffler.Unit.RunU
