module

public import ProofKit.Cfg
import all ProofKit.Cfg
public import PermuteKraken.Specs
import all PermuteKraken.Specs
public import Kraken.X64.Parser
import all Kraken.X64.Parser

@[expose] public section

/-! # Tests: `vcKind`, `vc_shapes`, `vc_by_shape`

The kinds come from the VCs that `kvcgen64` gives for small parsed programs
under `Program.WP.cfg` (`load`, `goto`, `jumpOut`, `retAddr`, `ret`, `closed`,
`other`), and from hand-written targets (`fall`, which `kvcgen64` splits). -/

open Std.WP Lean.Order
open scoped Program.WP
set_option experimental.vcgen true
open ProofKit

namespace ProofKitTest.Shape

/-! ## Hand-written targets -/

/--
info: refine_1: closed | 0 < 0 ∨ 0 = 0 ∧ 0 + 1 < 0 + 1 + 1
---
info: refine_2: closed | 1 = 1 ∧ 2 = 2
---
info: refine_3: other | x = 1
---
info: refine_4: other | x = 1 ∧ 2 = 2
---
info: refine_5: other | True ∧ x = 1
-/
#guard_msgs in
example (x : Nat) (h : x = 1) :
    (0 < 0 ∨ 0 = 0 ∧ 0 + 1 < 0 + 1 + 1) ∧ (1 = 1 ∧ 2 = 2) ∧ x = 1 ∧ (x = 1 ∧ 2 = 2)
      ∧ (True ∧ x = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals vc_shapes
  all_goals first | decide | exact h | exact ⟨h, rfl⟩ | exact ⟨trivial, h⟩

/-- `fall`: the invariant and the variant of a fall-through, before `kvcgen64` splits them. -/
example (var : Label → MachineData → Nat) (I : MachineData → Prop) (t : MachineData) (h : I t) :
    I t ∧ Program.Decreases var (.label "a") 1 t (.label "a") 2 t := by
  run_tac do
    let k ← vcKind (← Lean.Elab.Tactic.getMainGoal)
    unless k == .fall do throwError "expected fall, got {k.name}"
  vc_by_shape
    | fall => exact ⟨h, Or.inr ⟨rfl, by decide⟩⟩

/-! ## `k`: a load, a jump to a label, a return -/

def k := parse("
f:
  movzwl (%rdi), %eax
  cmpq $0, %rax
  je .L1
  movq $1, %rax
.L1:
  ret
")

/-- The invariant of `k`: `.L1` keeps the stack and the memory of the start. -/
def kInv (s₀ : MachineData) : CfgLabel → MachineData → Prop
  | .entry, t | .label "f", t => t = s₀
  | .label ".L1", t => t.regs.rsp = s₀.regs.rsp ∧ t.dmem = s₀.dmem
  | _, _ => False

theorem retAddr_congr {t s : MachineData} (h1 : t.regs.rsp = s.regs.rsp) (h2 : t.dmem = s.dmem) :
    t.retAddr = s.retAddr := by
  simp only [MachineData.retAddr, Reg64s.get64_rsp, h1, h2]

-- The kinds of the VCs of each block. No `False` in the context: `kvcgen64` would close all goals.
/--
info: vc1: other | kInv s₀ (CfgLabel.label "f") t
---
info: vc1: load | (Mem.loadInt t.dmem (t.regs.get64 Reg64.rdi + BitVec.ofInt 64 (Int64.toInt 0)) 2).isSome = …
---
info: vc2: goto .L1 | Program.Intercept ["f", ".L1"] t   (fun b j x s =>     kInv t b s ∧       match CfgLabel.l …
---
info: vc3: other | kInv t (CfgLabel.label ".L1")   {     regs :=       { rax := { toBitVec := 1#64 }, rbx :=  …
---
info: vc4: closed | 0 < 0 ∨ 0 = 0 ∧ 0 + 1 < 0 + 1 + 1
---
info: vc1: retAddr | t.retAddr.isSome = true
---
info: vc2: ret | Program.Intercept ["f", ".L1"] s₀   (fun b j x s =>     kInv s₀ b s ∧       match CfgLabel …
-/
#guard_msgs (info, error, drop warning) in
example [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) :
    WP.wp k (fun _ _ => False) (fun a _ => a = ra) s₀ := by
  refine Program.WP.cfg (kInv s₀) (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht => simp only [kInv] at ht; kvcgen64; vc_shapes; all_goals sorry
  case «f» t ht => simp only [kInv] at ht; subst ht; kvcgen64; vc_shapes; all_goals sorry
  case «.L1» t ht => kvcgen64; vc_shapes; all_goals sorry

/-- `vc_by_shape` closes every VC of `k`, one arm for each kind. -/
theorem k_ok [Host] [FunDecls] (s₀ : MachineData) (ra : Int64)
    (hm : (Mem.loadInt s₀.dmem s₀.regs.rdi.toBitVec 2).isSome = true)
    (hra : s₀.retAddr = some ra) :
    WP.wp k (fun _ _ => False) (fun a _ => a = ra) s₀ := by
  refine Program.WP.cfg (kInv s₀) (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht =>
    simp only [kInv] at ht
    kvcgen64
    vc_by_shape
      | other => exact ht
  case «f» t ht =>
    simp only [kInv] at ht
    subst ht
    kvcgen64
    vc_by_shape
      | load => simpa using hm
      | goto ".L1" =>
        cfg_goto
        · exact MachineData.stackAtOrBelow_of_rsp_eq rfl
        · exact ⟨rfl, rfl⟩
        · simp
      | other => exact ⟨rfl, rfl⟩
      | closed => decide
  case «.L1» t ht =>
    simp only [kInv] at ht
    kvcgen64
    vc_by_shape
      | retAddr => rw [retAddr_congr ht.1 ht.2, hra]; rfl
      | ret =>
        refine Program.Intercept.intro (Or.inr ⟨?_, fun _ _ _ => MachineData.stackBelow_of_add_eight ?_⟩)
        · rw [retAddr_congr ht.1 ht.2, hra]; rfl
        · simp [ht.1]

/-! ## The goals that no arm matches stay, in order -/

-- `goto ".L9"` and `ret` match no goal of block `f`; `closed` matches one.
/--
info: vc1: load | (Mem.loadInt t.dmem (t.regs.get64 Reg64.rdi + BitVec.ofInt 64 (Int64.toInt 0)) 2).isSome = …
---
info: vc2: goto .L1 | Program.Intercept ["f", ".L1"] t   (fun b j x s =>     kInv t b s ∧       match CfgLabel.l …
---
info: vc3: other | kInv t (CfgLabel.label ".L1")   {     regs :=       { rax := { toBitVec := 1#64 }, rbx :=  …
-/
#guard_msgs (info, error, drop warning) in
example [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) :
    WP.wp k (fun _ _ => False) (fun a _ => a = ra) s₀ := by
  refine Program.WP.cfg (kInv s₀) (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case «f» t ht =>
    simp only [kInv] at ht
    subst ht
    kvcgen64
    vc_by_shape
      | goto ".L9" => fail "goto .L9"
      | ret => fail "ret"
      | closed => decide
    vc_shapes
    all_goals sorry
  all_goals sorry

/-! ## Errors -/

-- The tactic of an arm fails: the error names the kind and the tag.
/--
error: vc_by_shape: the tactic for the load goal vc1 fails:
no load proof
-/
#guard_msgs (info, error, drop warning) in
example [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) :
    WP.wp k (fun _ _ => False) (fun a _ => a = ra) s₀ := by
  refine Program.WP.cfg (kInv s₀) (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case «f» t ht =>
    simp only [kInv] at ht
    subst ht
    kvcgen64
    vc_by_shape
      | load => run_tac (throwError "no load proof" : Lean.Elab.Tactic.TacticM Unit)
  all_goals sorry

/--
error: vc_by_shape: the tactic for the goto .L1 goal vc2 fails:
no goto proof
-/
#guard_msgs (info, error, drop warning) in
example [Host] [FunDecls] (s₀ : MachineData) (ra : Int64) :
    WP.wp k (fun _ _ => False) (fun a _ => a = ra) s₀ := by
  refine Program.WP.cfg (kInv s₀) (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case «f» t ht =>
    simp only [kInv] at ht
    subst ht
    kvcgen64
    vc_by_shape
      | load => sorry
      | goto => run_tac (throwError "no goto proof" : Lean.Elab.Tactic.TacticM Unit)
  all_goals sorry

/-- error: vc_by_shape: unknown kind jump -/
#guard_msgs in
example (hF : False) : False := by
  vc_by_shape
    | jump => exact hF

-- A tactic that logs its error and then aborts (as `run_tac` does after an
-- elaboration error): the logged error stays, as with no `vc_by_shape`, and
-- there is no "internal exception" error.
/--
error: no proof
---
error: unsolved goals
⊢ 1 = 1
-/
#guard_msgs in
example : 1 = 1 := by
  vc_by_shape
    | closed => run_tac do
        Lean.logError "no proof"
        (Lean.Elab.throwAbortTactic : Lean.Elab.Tactic.TacticM Unit)

/-! ## `kj`: a jump out of the cfg -/

def kj := parse("
f:
  cmpq $0, %rax
  je .L1
  jmp g
.L1:
  ret
")

-- `jmp g`: `g` is not a label of `kj`, so the VC is `jumpOut`, not `goto`.
/--
info: vc1: goto .L1 | Program.Intercept ["f", ".L1"] t   (fun b j x s =>     (match b, s with       | CfgLabel.e …
---
info: vc2: jumpOut | Program.Intercept ["f", ".L1"] t   (fun b j x s =>     (match b, s with       | CfgLabel.e …
-/
#guard_msgs (info, error, drop warning) in
example [Host] [FunDecls] (s₀ : MachineData) :
    WP.wp kj (fun _ _ => False) (fun _ _ => True) s₀ := by
  refine Program.WP.cfg (fun | .entry, t | .label "f", t => t = s₀ | .label ".L1", _ => True | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case «f» t ht =>
    subst ht
    kvcgen64
    vc_shapes
    all_goals sorry
  all_goals sorry

end ProofKitTest.Shape
