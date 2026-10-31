import BbuKraken.Unit.Lowest.Fill

/-!
# `permuteAtLowestHeight`: the call of `permute` and the return

The blocks `.4` (the call of `permute`), `.5` (an assertion fails) and `.6` (the epilogue).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Lowest
open Permute

-- The address of the array `permutation`.
theorem perm_base (sp : Word) : sp - 24592#64 + 16384#64 = sp - 8208#64 := by
  bv_omega

theorem b_4 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s)
    (hperm : ∀ p, Sep.SpecW Names.permute permW (permuteA p) 1034 (permuteQ p)) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.4" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, sc, ⟨lo, w, hM, hdi⟩, hs, heq, hpe⟩ := ht
  have hperm := hperm L.perm
  simp only [Names.permute] at hperm
  kvcgen64 [hperm]
  all_goals try symexec_norm
  have hL := len_le hpre.ok
  have hlow : Flat.permuteAtLowestHeight planned l0 (flat g) = Flat.permute (flat g) L.perm :=
    (Flat.lowest_eq hs heq).trans (by rw [hpe]; rfl)
  refine Mid.callW (hM.next rfl rfl) hdi ?_ hpre.ok ⟨hpre.args.1, hpre.args.2.1, ?_, ?_⟩ ?_
  · show t.regs.rsp.toBitVec + 16384#64 = _
    rw [hM.sp]; exact perm_base _
  · rw [hpe]; exact hpre.args.2.2 l0 sc hs heq
  · intro i hi
    have hiM : i < MAX_N := by show i < 1024; omega
    have hiw : (BitVec.ofNat 64 i).toNat < MAX_N := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hiM
    show rd t.dmem (t.regs.rsp.toBitVec + 16384#64 + BitVec.ofNat 64 (8 * i)) = _
    rw [hM.rdPerm hiM (by rw [hM.sp, perm_base]), get_eq _ _ hiw]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  · intro t2 g'' L' lo' w' hmid hQ hok'
    obtain ⟨hk2, hfl, hal⟩ := hQ
    kvcgen64
    all_goals try symexec_norm
    cfg_goto
    · exact (hmid.next rfl rfl).stack
    · simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
      refine ⟨g'', L', lo', w', hmid.next rfl rfl, hok', l0, hk2, ?_, ?_⟩
      · rw [hlow]; exact hfl
      · rw [hlow]; exact hal
    · lowest_dec

theorem b_5 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.5" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, l0, ⟨lo, w, hM, _⟩, hs⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte]
  refine ⟨g, L, lo, w, hM.next rfl rfl, hpre.ok, l0, Keep.refl g, ?_, ?_⟩
  · rw [Flat.lowest_none hs]
  · rw [Flat.lowest_none hs]; rfl
  · lowest_dec

theorem b_6 [Host] [FunDecls] (S PM planned g F0 s ra) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.6" → Obl S PM planned g F0 s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, lo, w, hM, hok, l, hk, hf, ha⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  · refine (congrArg Option.isSome (hM.pop ?_ ?_).retAddr).trans rfl
    all_goals rfl
  · refine Kp.ret (hM.pop ?_ ?_) (words_length lo w L hM.len) hok fun t' _ hax =>
      ⟨l, hk, hf, by show (rax t').setWidth 8 = _; rw [hax]; exact ha⟩
    all_goals rfl

end Lowest
end Bbu.Unit
