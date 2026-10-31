import BbuKraken.Unit.Run.Inv

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.RunU
open Bbu.Sep

section
variable [Host] [FunDecls] (S PM : Addr) (planned : Vector Word MAX_N)
    (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_entry : runAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  simp only [Inv, Names.run, ↓reduceIte]
  exact ht

theorem b_0 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.0" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, lo, w, hbd, hok, hq⟩ := ht
  have hkb : Kb (RunView PM planned S a ∗ F) s ra ((lo ++ [w]) ++ saved s) 24#64 t := by
    simpa only [fr, List.append_assoc, List.singleton_append] using hbd.kb
  have hp := fun i (hi : i < 3) =>
    hkb.isSome_hi (lo := lo ++ [w]) (hi := saved s) rfl (i := i)
      (by simpa [saved] using hi)
  have hp0 := hp 0 (by decide)
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero] at hp0 hp1
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => first
    | exact hp0
    | exact hp1
    | simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp2
  | retAddr =>
    apply Option.isSome_iff_exists.mpr
    refine ⟨ra, ?_⟩
    apply Kg.retAddr
    apply hbd.pop <;> rfl
  | ret =>
    refine Kg.vret (ok := G.Ok) (a' := a) (fr := fr s lo w) ?_
      (fr_length hbd.len) hok ?_
    · apply hbd.pop <;> rfl
    · intro u _ hax
      obtain ⟨l, hk, hf, hal⟩ := hq
      exact ⟨l, hk, hf, by show (rax u).setWidth 8 = _; rw [hax]; exact hal⟩

theorem b_6 : runAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Emission.run.6" → Obl S PM planned g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, ha⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  cfg_goto
  · exact (h.bd.kb.next rfl rfl).stack (by decide)
  · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
    refine ⟨a, lo, w, ?_, h.ok, h.result (finish_available ha) rfl⟩
    apply h.bd.next <;> rfl
  · simp [V, Names.run]

theorem b_8 (hs : Safe planned (flat g) g.xo)
    (hloop : VSpec (RunView PM planned) G.Ok Names.buildBottomUp loopA 2068 loopQ) :
    runAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.run.8" → Obl S PM planned g F s ra blk := by
  simp only [Names.buildBottomUp] at hloop
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.run, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨a, l, lo, w, h, hc⟩ := ht
  kvcgen64 [hloop]
  all_goals try symexec_norm at ⊢
  refine Bd.call (h.bd.next rfl rfl rfl rfl rfl) (by decide) h.bx h.ok
    (h.loopA hs hc) ?_
  intro u a' lo' w' hbd hq hok hag
  obtain ⟨hk, hf, hal⟩ := hq
  have he : Flat.emissionRun planned l (flat g) = Flat.buildBottomUp (flat a) :=
    (emission_finish h.model).trans (finish_success hc)
  kvcgen64
  all_goals try symexec_norm at ⊢
  cfg_goto
  · exact (hbd.kb.next rfl rfl).stack (by decide)
  · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
    refine ⟨a', lo', w', ?_, hok, l, ?_, ?_, ?_⟩
    · apply hbd.next <;> rfl
    · exact ⟨hk.tgtp.trans h.keep.tgtp, hk.n.trans h.keep.n,
        hk.splp.trans h.keep.splp, hk.data.trans h.keep.data, hk.ops.trans h.keep.ops,
        hk.xs.trans h.keep.xs, hk.xo.trans h.keep.xo, hk.tgt.trans h.keep.tgt,
        hk.spl.trans h.keep.spl⟩
    · rw [he]; exact hf
    · rw [he]; exact hal
  · simp [V, Names.run]

end
end Bbu.Unit.RunU
