module

public import FlatShuffler.Unit.Lowest.Fill
import all FlatShuffler.Unit.Lowest.Fill

@[expose] public section

set_option experimental.vcgen true

/-!
# `permuteAtLowestHeight`: the call of `permute` and the return

The block `.5` calls `permute` and returns. The blocks `.6` and `.7` call `exit(1)`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Lowest
open Permute

-- The address of the array `permutation`.
theorem perm_base (sp : Word) : sp - 24592#64 + 16384#64 = sp - 8208#64 := by
  bv_omega

theorem b_4 [Host] [FunDecls] (S PM planned g F0 s ra)
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s)
    (hout : ∀ l ∈ Program.labels permuteAtLowestHeightAsm, label l ≠ label "exit")
    (hperm : ∀ p, Sep.SpecWWithExit Names.permute permW (permuteA p) 1034 (permuteQ p) (permuteX p)) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label ".LB.Emission.permuteAtLowestHeight.5" → Obl S PM planned g F0 s ra blk := by
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
  refine Mid.callWWithExit (hM.next rfl rfl) hdi ?_ hpre.ok
    ⟨hpre.args.1, hpre.args.2.1, ?_, ?_⟩ ?_ ?_
  · show t.regs.rsp.toBitVec + 16384#64 = _
    rw [hM.sp]; exact perm_base _
  · rw [hpe]; exact hpre.args.2.2 l0 sc hs heq
  · intro i hi
    have hiM : i < maxStackSize := by show i < 1024; omega
    have hiw : (BitVec.ofNat 64 i).toNat < maxStackSize := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hiM
    show rd t.dmem (t.regs.rsp.toBitVec + 16384#64 + BitVec.ofNat 64 (8 * i)) = _
    rw [hM.rdPerm hiM (by rw [hM.sp, perm_base]), get_eq _ _ hiw]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  · intro t2 g'' L' lo' w' hmid hQ hok'
    obtain ⟨⟨hk2, hfl, hal⟩, hnormal⟩ := hQ
    kvcgen64
    all_goals symexec_norm
    vc_by_shape
    | retAddr =>
      refine (congrArg Option.isSome (hmid.pop ?_ ?_).retAddr).trans rfl
      all_goals rfl
    | ret =>
      refine intercept_mono_exit
        (E := fun a t => a = ra ∧ Sep.Post S (Planned S PM planned ∗ F0) lowestD
          (fun g' t => lowestQ planned g g' s t) s t ∧ Sep.mod.Agree s t) ?_ Or.inl
      refine Kp.ret (hmid.pop ?_ ?_) (words_length lo' w' L' hmid.len) hok'
        fun t' _ hax => ⟨l0, ⟨hk2, ?_, ?_⟩, ?_⟩
      · rfl
      · rfl
      · rw [hlow]; exact hfl
      · show (rax t').setWidth 8 = _
        rw [hax, hlow]; exact hal
      · show (rax t').setWidth 8 ≠ _
        rw [hax]; exact hnormal
  · intro t2 g'' L' lo' w' hm hl hX hok' harg
    refine Or.inr ⟨Or.inr ⟨rfl, harg, ?_⟩, ?_⟩
    · refine frame_post hm hl hok' ⟨l0, ?_⟩
      dsimp only [permuteX, ExitRes] at hX
      dsimp only [ExitRes]
      rw [hlow]
      exact hX
    · intro l hl ha
      exact False.elim (hout l hl ha)

theorem b_fail [Host] [FunDecls] (S PM planned g F0 s ra)
    (l : Label)
    (hl : l = ".LB.Emission.permuteAtLowestHeight.6" ∨
      l = ".LB.Emission.permuteAtLowestHeight.7")
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels permuteAtLowestHeightAsm, label l ≠ label "exit")
    (hpre : Sep.Pre S g (Planned S PM planned ∗ F0) (lowestA planned) lowestD s) :
    Program.ForallBlocks permuteAtLowestHeightAsm fun blk =>
      blk.label = .label l → Obl S PM planned g F0 s ra blk := by
  rcases hl with rfl | rfl
  all_goals
    cfg_block [Obl]
    intro t ht
    simp only [LInv, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨L, l0, ⟨lo, w, hM, _⟩, hfail⟩ := ht
    have he := external_call_spec "exit" hexit
    kvcgen64 [he]
    all_goals symexec_norm
    vc_by_shape
    | load =>
      rw [hM.sp]
      exact isSome_of_eq w hM.mem (by unfold Stk; ecancel)
    | jumpOut =>
      exact exit_intercept hout (hM.next rfl rfl) hpre.ok l0 hfail rfl

end Lowest
end FlatShuffler.Unit
