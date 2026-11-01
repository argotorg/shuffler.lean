module

public import ProofKit.CfgBlock
import all ProofKit.CfgBlock
public import ProofKitTest.Cfg
import all ProofKitTest.Cfg

@[expose] public section

/-! # Tests: `forallBlocks_cases`, `cfg_labels`, `cfg_block`

The proof of `ProofKitTest.Cfg.loop_ok` again, with one lemma for each block. -/

open Std.WP Lean.Order
open scoped Program.WP
set_option experimental.vcgen true
open ProofKit
open ProofKitTest.Cfg (loop loopInv)

namespace ProofKitTest.CfgBlock

/-! ## `cfg_labels` -/

example : Program.ForallBlocks loop fun blk => blk.label ∈ [.entry, .label "f", .label ".L2"] := by
  cfg_labels

-- The order of the list does not matter, and the list can have more labels.
example : Program.ForallBlocks loop fun blk => blk.label ∈ [.label ".L2", .label ".L9", .entry, .label "f"] := by
  cfg_labels

-- A list without the label `.L2` fails.
example : True := by
  fail_if_success
    have : Program.ForallBlocks loop fun blk => blk.label ∈ [.entry, .label "f"] := by cfg_labels
  trivial

-- A list without `.entry` fails.
example : True := by
  fail_if_success
    have : Program.ForallBlocks loop fun blk => blk.label ∈ [.label "f", .label ".L2"] := by cfg_labels
  trivial

/-! ## `cfg_block` -/

-- The block of `.L2`: its body has 4 directives, its index is 2, and it falls through to the
-- exit. `cfg_block` decides the index and the next label; the length of the body stays.
example : Program.ForallBlocks loop fun blk => blk.label = .label ".L2" →
    blk.body.length = 4 ∧ blk.idx = 2 ∧ blk.next = .exit := by
  cfg_block
  rfl

-- The block of `f`: no directives in the entry block, so `f` is block 1, and it falls through
-- to `.L2`.
example : Program.ForallBlocks loop fun blk => blk.label = .label "f" →
    blk.body.length = 1 ∧ blk.idx = 1 ∧ blk.next = .label ".L2" := by
  cfg_block
  rfl

-- A label that is not in the program: no goal stays.
example : Program.ForallBlocks loop fun blk => blk.label = .label ".L7" → False := by
  cfg_block

-- `cfg_block` leaves the goal of the block, and a false goal stays false.
example : True := by
  fail_if_success
    have : Program.ForallBlocks loop fun blk => blk.label = .label ".L2" → blk.idx = 1 := by
      cfg_block
      rfl
  trivial

-- A false next label stays false.
example : True := by
  fail_if_success
    have : Program.ForallBlocks loop fun blk => blk.label = .label ".L2" →
        blk.next = .label ".L2" := by
      cfg_block
  trivial

-- The simp lemmas unfold the predicate of the block.
def Small (blk : Program.Block) : Prop := blk.idx < 3

example : Program.ForallBlocks loop fun blk => blk.label = .label ".L2" → Small blk := by
  cfg_block [Small]
  decide

/-! ## `forallBlocks_cases`: `loop_ok` with one lemma for each block -/

def loopVar : Label → MachineData → Nat
  | "f", t => t.regs.rcx.toBitVec.toNat
  | ".L2", t => t.regs.rcx.toBitVec.toNat
  | _, _ => 0

/-- The obligation of `Program.WP.cfg` for the block `blk` of `loop`. -/
def Obl [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) (blk : Program.Block) : Prop :=
  ∀ t, loopInv s₀ blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      loopInv s₀ b u ∧ Program.Decreases loopVar blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels loop) s₀ I'
        (fun a t => a = ra ∧ t.regs.rax.toBitVec = s₀.regs.rcx.toBitVec)) t

theorem blk_entry [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) :
    Program.ForallBlocks loop fun blk => blk.label = .entry → Obl s₀ ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [loopInv] at ht
  kvcgen64
  vc_by_shape
    | other => exact ht

theorem blk_f [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) (hn : s₀.regs.rcx.toBitVec ≠ 0) :
    Program.ForallBlocks loop fun blk => blk.label = .label "f" → Obl s₀ ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [loopInv] at ht
  subst ht
  kvcgen64
  vc_by_shape
    | other =>
      first
        | (right; exact ⟨rfl, by decide⟩)
        | (simp only [loopInv]; refine ⟨?_, ?_, hn, ?_⟩ <;> first | trivial | bv_omega)

theorem blk_L2 [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) (hra : s₀.retAddr = some ra) :
    Program.ForallBlocks loop fun blk => blk.label = .label ".L2" → Obl s₀ ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [loopInv] at ht
  obtain ⟨hsp, hm, hpos, hsum⟩ := ht
  kvcgen64
  all_goals (rename_i hc; revert hc; symexec_norm; intro hc)
  vc_by_shape
    | goto ".L2" =>
      have hc' : t.regs.rcx.toBitVec ≠ 1#64 := by intro h; simp [h] at hc
      cfg_goto
      · exact MachineData.stackAtOrBelow_of_rsp_eq (by simp [hsp])
      · simp only [loopInv]
        refine ⟨hsp, hm, ?_, ?_⟩ <;> bv_omega
      · left
        show (t.regs.rcx.toBitVec - 1#64).toNat < t.regs.rcx.toBitVec.toNat
        bv_omega
    | retAddr =>
      rw [ProofKitTest.Shape.retAddr_congr (s := s₀) ?_ ?_, hra]
        <;> first | rfl | exact hsp | exact hm
    | ret =>
      have hc' : t.regs.rcx.toBitVec - 1#64 = 0#64 := by simpa using hc
      refine Program.Intercept.intro
        (Or.inr ⟨⟨?_, ?_⟩, fun _ _ _ => MachineData.stackBelow_of_add_eight ?_⟩)
      · rw [ProofKitTest.Shape.retAddr_congr (s := s₀) ?_ ?_, hra]
          <;> first | rfl | exact hsp | exact hm
      · show 1#64 + t.regs.rax.toBitVec = s₀.regs.rcx.toBitVec
        bv_omega
      · simp [hsp]

-- `loop_ok` from the three block lemmas.
theorem loop_ok' [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) (hn : s₀.regs.rcx.toBitVec ≠ 0)
    (hra : s₀.retAddr = some ra) :
    WP.wp loop (fun _ _ => False)
      (fun a t => a = ra ∧ t.regs.rax.toBitVec = s₀.regs.rcx.toBitVec) s₀ := by
  refine Program.WP.cfg (loopInv s₀) loopVar ?_ rfl
  refine forallBlocks_cases [.entry, .label "f", .label ".L2"] (by cfg_labels) ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨blk_entry s₀ ra, blk_f s₀ ra hn, blk_L2 s₀ ra hra⟩

-- Without the label `.L2` in the list, the label goal does not close.
-- `fail_if_success` rolls back the uses of `ra` and `hn`.
set_option linter.unusedVariables false in
example [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) (hn : s₀.regs.rcx.toBitVec ≠ 0) :
    True := by
  fail_if_success
    have : WP.wp loop (fun _ _ => False)
        (fun a t => a = ra ∧ t.regs.rax.toBitVec = s₀.regs.rcx.toBitVec) s₀ := by
      refine Program.WP.cfg (loopInv s₀) loopVar ?_ rfl
      refine forallBlocks_cases [.entry, .label "f"] ?_ ?_
      · cfg_labels
      · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨blk_entry s₀ ra, blk_f s₀ ra hn⟩
  trivial

end ProofKitTest.CfgBlock
