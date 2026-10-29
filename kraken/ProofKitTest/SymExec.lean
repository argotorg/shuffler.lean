import ProofKit.SymExec
import PermuteKraken.Specs
import Kraken.X64.Parser

/-! # Tests: `#symexec`

Each test runs `#symexec` on one block of a small parsed program, then checks
the defs that the command adds: their values (`rfl`), their meaning (`simp`),
and that they are the exit states of the VCs of the block (a proof of the wp
of the block from the defs).

The file does not open `Std.WP`: the command must not need it. -/

open scoped Program.WP
set_option experimental.vcgen true

namespace ProofKitTest.SymExec

/-- Block `f`: 2 exits (`je` and the fall-through). Block `.L1`: `ret`.
Block `.L2`: a `mov` and the fall-through. -/
def sx := parse("
f:
  cmpq $5, %rax
  je .L1
  addq $1, %rax
.L1:
  ret
.L2:
  movq $4, %rbx
")

/-- The body of block `f`, for the wp check. -/
def sxF := parse("
  cmpq $5, %rax
  je .L1
  addq $1, %rax
")

#guard_msgs (drop info) in
#symexec sx from "f"

-- The command opens the `vcgen` instances for itself only: they stay closed here.
/--
error: failed to synthesize
  Lean.Order.CompleteLattice Prop

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Lean.Order.CompleteLattice Prop

/-! Exit 1: the jump to `.L1`. The path condition is `zf` of `rax - 5`. -/

example (s : MachineData) :
    sx.f.x1.cond s = ((s.regs.rax.toBitVec - 5#64 == BitVec.zero 64) = true) := rfl

example (s : MachineData) : sx.f.x1.cond s ↔ s.regs.rax.toBitVec = 5#64 := by
  simp only [sx.f.x1.cond, beq_iff_eq]
  bv_decide

example (s : MachineData) : (sx.f.x1.st s).regs = s.regs := rfl
example (s : MachineData) : (sx.f.x1.st s).dmem = s.dmem := rfl
example (s : MachineData) :
    (sx.f.x1.st s).status.zf = (s.regs.rax.toBitVec - 5#64 == BitVec.zero 64) := rfl

/-! Exit 2: the fall-through. The path condition is `¬ zf`; `rax` is `rax + 1`. -/

example (s : MachineData) :
    sx.f.x2.cond s = ((s.regs.rax.toBitVec - 5#64 == BitVec.zero 64) = false) := rfl

example (s : MachineData) :
    (sx.f.x2.st s).regs.rax.toBitVec = s.regs.rax.toBitVec + 1#64 := by
  simp only [sx.f.x2.st]
  exact BitVec.add_comm _ _

example (s : MachineData) : (sx.f.x2.st s).regs.rbx = s.regs.rbx := rfl
example (s : MachineData) : (sx.f.x2.st s).dmem = s.dmem := rfl

/-- The command adds `x1`, `x2` and nothing more. -/
def hasDecl (n : Lean.Name) : Lean.MetaM Bool := return (← Lean.getEnv).contains n

run_meta do
  guard (← hasDecl `ProofKitTest.SymExec.sx.f.x1.cond)
  guard (← hasDecl `ProofKitTest.SymExec.sx.f.x2.cond)
  guard !(← hasDecl `ProofKitTest.SymExec.sx.f.x3.st)
  guard !(← hasDecl `ProofKitTest.SymExec.sx.f.x3.cond)

open Std.WP Lean.Order in
/-- The defs are the exit states of the VCs of the block, after `symexec_norm`:
the wp of the block follows from the exits, each by `exact`. -/
theorem sxF_wp [Host] [FunDecls] (s : MachineData) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (h1 : sx.f.x1.cond s → E (label ".L1") (sx.f.x1.st s))
    (h2 : sx.f.x2.cond s → Q (sx.f.x2.st s)) :
    WP.wp sxF (fun _ => Q) E s := by
  kvcgen64 [sxF]
  · rename_i hc
    revert hc
    symexec_norm
    exact h1
  · rename_i hc
    revert hc
    symexec_norm
    exact h2

/-! Block `.L1`: one `ret` exit, one `retAddr` side goal. -/

/--
info: Try this:
-- #symexec ProofKitTest.SymExec.sx from ".L1": 1 instructions, 1 exits, side goals [(retAddr, 1)]

-- exit 1: ret
def ProofKitTest.SymExec.sx.L1.x1.st (s : MachineData) : MachineData :=
  { regs := s.regs.set64 Reg64.rsp (s.regs.rsp.toBitVec + 8#64), zmms := s.zmms, status := s.status, dmem := s.dmem :
    MachineData }
---
info: symexec: the command defines these terms. The printed text elaborates back to: [ProofKitTest.SymExec.sx.L1.x1.st: exact]
-/
#guard_msgs in
#symexec sx from ".L1"

example (s : MachineData) :
    sx.L1.x1.st s = { s with regs := s.regs.set64 .rsp (s.regs.rsp.toBitVec + 8#64) } := rfl

/-! Block `.L2`: the norm tactic has nothing to rewrite on the exit. -/

#guard_msgs (drop info) in
#symexec sx from ".L2"

example (s : MachineData) : (sx.L2.x1.st s).regs.rbx.toBitVec = 4#64 := by
  simp [sx.L2.x1.st]
example (s : MachineData) : (sx.L2.x1.st s).regs.rax = s.regs.rax := rfl

/-! The entry segment of `sx` is empty: one exit, the start state. -/

#guard_msgs (drop info) in
#symexec sx from "entry"

example (s : MachineData) : sx.entry.x1.st s = s := rfl

/-! A dead exit: `jne` after `cmp` of equal constants. With `using simp`, the
path condition of the jump is `False`, so the norm tactic closes that exit; the
command gives it no defs. The norm tactic also removes the path condition of
the fall-through (it is `True`). -/

def dead := parse("
f:
  movq $0, %rax
  cmpq $0, %rax
  jne .L1
  movq $3, %rbx
.L1:
  ret
")

#guard_msgs (drop info) in
#symexec dead from "f" using simp

run_meta do
  guard !(← hasDecl `ProofKitTest.SymExec.dead.f.x1.st)
  guard !(← hasDecl `ProofKitTest.SymExec.dead.f.x1.cond)
  guard (← hasDecl `ProofKitTest.SymExec.dead.f.x2.st)
  guard !(← hasDecl `ProofKitTest.SymExec.dead.f.x2.cond)

example (s : MachineData) : (dead.f.x2.st s).regs.rbx.toBitVec = 3#64 := by
  simp [dead.f.x2.st]

/-! Errors. -/

/-- error: symexec: no block .L9 -/
#guard_msgs in
#symexec sx from ".L9"

end ProofKitTest.SymExec
