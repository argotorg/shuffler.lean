import BbuKraken.Layout
import BbuKraken.ModelLemmas

/-!
The spec of each function of `c/build_bottom_up.c` but `build_bottom_up`: the
frame size `F`, the further precondition `A` and the result `R`. A function
spec is `Spec name`; the proof of a caller takes the `Spec` of each callee as a
hypothesis. `st` and `e` are the model state and environment at the call.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

abbrev st (s : MachineData) : St := stOf s.dmem (rdi s)
abbrev env (s : MachineData) : Env := envOf s.dmem (rdi s)
abbrev cap (s : MachineData) : Nat := 6 * nOf s.dmem (rdi s)

-- The model state in `t`, for the struct of the call `s`.
abbrev st' (s t : MachineData) : St := stOf t.dmem (rdi s)

-- A function that returns `ok a` in the model: `rax` is `enc a` and the state is `f a`.
abbrev Ok {α : Type} (s t : MachineData) (enc : α → Word) (f : α → St) (a : α) : Prop :=
  rax t = enc a ∧ st' s t = f a

/-! ## Contracts -/

-- `isSpilled(e, _slot)`, for `_slot` in the target.
def isSpilledF : Nat := 8
def isSpilledA (s : MachineData) : Prop :=
  ∃ offset < (env s).n, (env s).target[offset]! = rsi s
def isSpilledR (s t : MachineData) : Prop :=
  rax t = BitVec.ofNat 64 (isSpilled (env s) (rsi s)).toNat ∧ st' s t = st s

-- `positionOf(e, _destination)`
def positionOfF : Nat := 8
def positionOfA (_ : MachineData) : Prop := True
def positionOfR (s t : MachineData) : Prop :=
  rax t = encOpt (positionOf (st s) (rsi s).toNat) ∧ st' s t = st s

-- `shallowestCopyPosition(e, _slot)`
def shallowestCopyF : Nat := 8
def shallowestCopyA (_ : MachineData) : Prop := True
def shallowestCopyR (s t : MachineData) : Prop :=
  rax t = encOpt (shallowestCopyPosition (st s) (rsi s)) ∧ st' s t = st s

-- `swapWith(e, _pos)`
def swapWithF : Nat := 8
def swapWithA (s : MachineData) : Prop := (st s).trace.length < cap s
def swapWithR (s t : MachineData) : Prop :=
  Res (rdi s) (swapWith (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t

-- `push(e, _slot, _destination)`
def pushF : Nat := 40
def pushA (s : MachineData) : Prop := (st s).len < MAX_N ∧ (st s).trace.length < cap s
def pushR (s t : MachineData) : Prop :=
  Res (rdi s) (add (st s) (rsi s) (rdx s).toNat (.push (rsi s))) (Ok s t (fun _ => 0#64) id) t

-- `dup(e, _copy, _destination)`
def dupF : Nat := 40
def dupA (s : MachineData) : Prop :=
  (rsi s).toNat < (st s).len ∧ (st s).len < MAX_N ∧ (st s).trace.length < cap s
def dupR (s t : MachineData) : Prop :=
  Res (rdi s) (add (st s) ((st s).val (rsi s).toNat) (rdx s).toNat
    (.dup ((st s).len - (rsi s).toNat))) (Ok s t (fun _ => 0#64) id) t

-- `produce(e, _targetOffset)`
def produceF : Nat := 80
def produceA (s : MachineData) : Prop :=
  (rsi s).toNat < (env s).n ∧ (st s).len < MAX_N ∧ (st s).trace.length < cap s
def produceR (s t : MachineData) : Prop :=
  Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t

-- `generate(e, _targetOffset)`
def generateF : Nat := 104
def generateA (s : MachineData) : Prop := (st s).len < MAX_N ∧ (st s).trace.length + 2 ≤ cap s
def generateR (s t : MachineData) : Prop :=
  Res (rdi s) (generate (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t

-- `permuteDestinations(e)`, for a permutation of the destinations
-- The locals of `permuteDestinations` from `rsp` after `subq`: `blocked` at 12,
-- `swaps` at 16, then `permutation` at `finishPerm`.
def finishPerm : Nat := 16 + 2 * MAX_N
def finishLocals : Nat := finishPerm + 2 * MAX_N
-- The return address, `pushq %rbx`, the locals and the frame of `permute`.
def finishF : Nat := 8 + 8 + finishLocals + 16
theorem finishF_eq : finishF = 4144 := rfl
def finishA (s : MachineData) : Prop :=
  IsPerm ((st s).slots.map Slot.dest) ∧ (st s).trace.length + 2 * (st s).len ≤ cap s
def finishR (s t : MachineData) : Prop :=
  Res (rdi s) (finish (st s)) (fun ops => rax t = 0#64 ∧ (st' s t).trace = ops) t

-- `buildBottomUp(e)`: `loop` from offset 0
-- The return address, six `pushq`, `subq $24` and the frame of `permuteDestinations`.
def loopF : Nat := 8 + 48 + 24 + finishF
theorem loopF_eq : loopF = 4224 := rfl
def loopA (s : MachineData) : Prop := Inv (env s) (st s) 0
def loopR (s t : MachineData) : Prop :=
  Res (rdi s) (loop (env s) (st s) 0) (fun ops => rax t = 0#64 ∧ (st' s t).trace = ops) t

/-! ## Specs -/

-- The spec of the function `f` with frame size `F`.
abbrev Spec [Host] [FunDecls] (f : Label) (F : Nat) (A : MachineData → Prop)
    (R : MachineData → MachineData → Prop) : Prop :=
  Program.WP.CallSpec f (Pre F A) (Post F R) (mod F)

-- The body triple of the function `prog` that gives `Spec` with `callSpec_of_triple`.
abbrev Body [Host] [FunDecls] (prog : Program) (F : Nat) (A : MachineData → Prop)
    (R : MachineData → MachineData → Prop) : Prop :=
  ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ Pre F A s ⦄ prog
    ⦃ (fun _ _ => False); fun a t => a = ra ∧ Post F R s t ∧ (mod F s).Agree s t ⦄

end Bbu
