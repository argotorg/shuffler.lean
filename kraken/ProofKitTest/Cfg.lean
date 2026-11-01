module

public import ProofKit.Cfg
import all ProofKit.Cfg
public import PermuteKraken.Asm
import all PermuteKraken.Asm
public import PermuteKraken.Specs
import all PermuteKraken.Specs
public import Kraken.X64.Parser
import all Kraken.X64.Parser
public import ProofKitTest.Shape
import all ProofKitTest.Shape

@[expose] public section

/-! # Tests: `#cfg_skeleton`, `cfg_blocks`, `cfg_goto`, `cfg_stk`

`#cfg_skeleton` on small parsed programs and on `permute`; the printed
skeleton elaborates; a full proof of a loop from the skeleton. -/

open Std.WP Lean.Order
open scoped Program.WP
set_option experimental.vcgen true
open ProofKit

namespace ProofKitTest.Cfg

/-- A loop: `rax` counts up while `rcx` counts down to 0. -/
def loop := parse("
f:
  movq $0, %rax
.L2:
  addq $1, %rax
  decq %rcx
  jnz .L2
  ret
")

/-! ## `#cfg_skeleton` -/

-- `.L2` is on a cycle; `f` falls through into it, so its variant must be at
-- least the variant of `.L2`: both get a hole.
/--
info: Try this:
refine Program.WP.cfg (fun
    | .entry, t => sorry
    | .label "f", t => sorry
    | .label ".L2", t => sorry
    | _, _ => False)
  (fun
    | "f", _ => sorry
    | ".L2", _ => sorry
    | _, _ => 0) ?_ sorry
cfg_blocks
case «entry» t ht => sorry -- 0 directives, jumps to []
case «f» t ht => sorry -- 1 directives, jumps to []
case «.L2» t ht => sorry -- 4 directives, jumps to [".L2"]
-/
#guard_msgs in
#cfg_skeleton loop

-- The printed skeleton elaborates as it is.
#guard_msgs (info, error, drop warning) in
example [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) :
    WP.wp loop (fun _ _ => False) (fun a _ => a = ra) s₀ := by
  refine Program.WP.cfg (fun
      | .entry, t => sorry
      | .label "f", t => sorry
      | .label ".L2", t => sorry
      | _, _ => False)
    (fun
      | "f", _ => sorry
      | ".L2", _ => sorry
      | _, _ => 0) ?_ sorry
  cfg_blocks
  case «entry» t ht => sorry
  case «f» t ht => sorry
  case «.L2» t ht => sorry

-- No cycle and no jump back: no variant hole.
/--
info: Try this:
refine Program.WP.cfg (fun
    | .entry, t => sorry
    | .label "f", t => sorry
    | .label ".L1", t => sorry
    | _, _ => False)
  (fun
    | _, _ => 0) ?_ sorry
cfg_blocks
case «entry» t ht => sorry -- 0 directives, jumps to []
case «f» t ht => sorry -- 4 directives, jumps to [".L1"]
case «.L1» t ht => sorry -- 1 directives, jumps to []
-/
#guard_msgs in
#cfg_skeleton ProofKitTest.Shape.k

def back := parse("
f:
  jmp .L2
.L1:
  ret
.L2:
  jmp .L1
")

-- No cycle, but `.L2` jumps back to `.L1`: the variant of `.L2` must be
-- above the variant of `.L1`, so `.L2`, and `f` before it, get a hole.
/--
info: Try this:
refine Program.WP.cfg (fun
    | .entry, t => sorry
    | .label "f", t => sorry
    | .label ".L1", t => sorry
    | .label ".L2", t => sorry
    | _, _ => False)
  (fun
    | "f", _ => sorry
    | ".L1", _ => sorry
    | ".L2", _ => sorry
    | _, _ => 0) ?_ sorry
cfg_blocks
case «entry» t ht => sorry -- 0 directives, jumps to []
case «f» t ht => sorry -- 1 directives, jumps to [".L2"]
case «.L1» t ht => sorry -- 1 directives, jumps to []
case «.L2» t ht => sorry -- 1 directives, jumps to [".L1"]
-/
#guard_msgs in
#cfg_skeleton back

-- `permute`: the loops are `.L3`/`.L7` and `.L5`/`.L13`; `permute` jumps into
-- them (as in `PermuteKraken.Var`). `.L12` and `.L1` reach no loop.
/--
info: Try this:
refine Program.WP.cfg (fun
    | .entry, t => sorry
    | .label "permute", t => sorry
    | .label ".L13", t => sorry
    | .label ".L3", t => sorry
    | .label ".L7", t => sorry
    | .label ".L5", t => sorry
    | .label ".L12", t => sorry
    | .label ".L1", t => sorry
    | _, _ => False)
  (fun
    | "permute", _ => sorry
    | ".L13", _ => sorry
    | ".L3", _ => sorry
    | ".L7", _ => sorry
    | ".L5", _ => sorry
    | _, _ => 0) ?_ sorry
cfg_blocks
case «entry» t ht => sorry -- 0 directives, jumps to []
case «permute» t ht => sorry -- 10 directives, jumps to [".L1", ".L7"]
case «.L13» t ht => sorry -- 3 directives, jumps to [".L1"]
case «.L3» t ht => sorry -- 11 directives, jumps to [".L12"]
case «.L7» t ht => sorry -- 7 directives, jumps to [".L3", ".L1"]
case «.L5» t ht => sorry -- 7 directives, jumps to [".L5", ".L13"]
case «.L12» t ht => sorry -- 4 directives, jumps to []
case «.L1» t ht => sorry -- 3 directives, jumps to []
-/
#guard_msgs in
#cfg_skeleton State.permuteAsm

/-! ## A full proof: `cfg_blocks`, `case`, `cfg_goto`, `vc_by_shape` -/

/-- The invariant of `loop`: at `.L2`, `rax + rcx` is the start `rcx`, and `rcx ≠ 0`. -/
def loopInv (s₀ : MachineData) : CfgLabel → MachineData → Prop
  | .entry, t | .label "f", t => t = s₀
  | .label ".L2", t => t.regs.rsp = s₀.regs.rsp ∧ t.dmem = s₀.dmem ∧ t.regs.rcx.toBitVec ≠ 0
      ∧ t.regs.rax.toBitVec + t.regs.rcx.toBitVec = s₀.regs.rcx.toBitVec
  | _, _ => False

/-- `loop` returns the start `rcx` in `rax`. The proof has the shape of the
skeleton of `loop`. -/
theorem loop_ok [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) (hn : s₀.regs.rcx.toBitVec ≠ 0)
    (hra : s₀.retAddr = some ra) :
    WP.wp loop (fun _ _ => False)
      (fun a t => a = ra ∧ t.regs.rax.toBitVec = s₀.regs.rcx.toBitVec) s₀ := by
  refine Program.WP.cfg (loopInv s₀)
    (fun
      | "f", t => t.regs.rcx.toBitVec.toNat
      | ".L2", t => t.regs.rcx.toBitVec.toNat
      | _, _ => 0) ?_ rfl
  cfg_blocks
  case «entry» t ht =>
    simp only [loopInv] at ht
    kvcgen64
    vc_by_shape
      | other => exact ht
  case «f» t ht =>
    simp only [loopInv] at ht
    subst ht
    kvcgen64
    -- the invariant of `.L2`, then the variant
    vc_by_shape
      | other =>
        first
          | (right; exact ⟨rfl, by decide⟩)
          | (simp only [loopInv]; refine ⟨?_, ?_, hn, ?_⟩ <;> first | trivial | bv_omega)
  case «.L2» t ht =>
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

/-! ## `cfg_stk`: a jump with `rsp` below the entry `rsp` -/

def stk := parse("
f:
  subq $8, %rsp
  jmp .L1
.L1:
  addq $8, %rsp
  ret
")

example [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) (hra : s₀.retAddr = some ra) :
    WP.wp stk (fun _ _ => False) (fun a _ => a = ra) s₀ := by
  refine Program.WP.cfg (fun
      | .entry, t | .label "f", t => t = s₀
      | .label ".L1", t => t.regs.rsp.toBitVec = s₀.regs.rsp.toBitVec - 8#64 ∧ t.dmem = s₀.dmem
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case «entry» t ht => kvcgen64; exact ht
  case «f» t ht =>
    subst ht
    kvcgen64
    vc_by_shape
      | goto ".L1" =>
        cfg_goto
        · cfg_stk
        · exact ⟨rfl, rfl⟩
        · simp
  case «.L1» t ht =>
    obtain ⟨hsp, hm⟩ := ht
    kvcgen64
    -- `addq $8, %rsp` gives `8 + rsp`
    all_goals have h1 : ({ toBitVec := 8#64 + t.regs.rsp.toBitVec } : UInt64) = s₀.regs.rsp :=
        UInt64.toBitVec_inj.mp (by show 8#64 + _ = _; rw [hsp]; bv_omega)
    vc_by_shape
      | retAddr =>
        rw [ProofKitTest.Shape.retAddr_congr (s := s₀) ?_ ?_, hra]
          <;> first | rfl | exact h1 | exact hm
      | ret =>
        refine Program.Intercept.intro (Or.inr ⟨?_, fun _ _ _ => MachineData.stackBelow_of_add_eight ?_⟩)
        · rw [ProofKitTest.Shape.retAddr_congr (s := s₀) ?_ ?_, hra]
            <;> first | rfl | exact h1 | exact hm
        · simp [h1]

-- `cfg_stk` fails when `rsp` is above the entry `rsp` (then its `toNat` goal is false).
example (s₀ t : MachineData) (_h : t.regs.rsp.toBitVec = s₀.regs.rsp.toBitVec + 8#64)
    (hs : t.StackAtOrBelow s₀) : t.StackAtOrBelow s₀ := by
  fail_if_success cfg_stk
  exact hs

end ProofKitTest.Cfg
