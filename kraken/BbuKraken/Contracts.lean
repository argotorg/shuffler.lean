import BbuKraken.Layout
import BbuKraken.ModelLemmas

/-!
The spec of each member function of `Emission` in `c/build_bottom_up.cpp`: the
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

-- A function that returns `ok a` in the model: the `Status` is `Done` and the state is `f a`.
abbrev Ok {α : Type} (s t : MachineData) (f : α → St) (a : α) : Prop :=
  al t = DONE ∧ st' s t = f a

/-! ## Contracts -/

-- The slot in `rsi`.
abbrev slot (s : MachineData) : StackSlot := StackSlot.ofWord (rsi s)

-- `isSpilled(e, _slot)`, for `_slot` in the target.
def isSpilledF : Nat := 8
def isSpilledA (s : MachineData) : Prop :=
  ∃ offset < (env s).n, (env s).target[offset]! = slot s
def isSpilledR (s t : MachineData) : Prop :=
  al t = BitVec.ofNat 8 (isSpilled (env s) (slot s)).toNat ∧ st' s t = st s

-- `shallowestCopyPosition(e, _slot)`
def shallowestCopyF : Nat := 8
def shallowestCopyA (_ : MachineData) : Prop := True
def shallowestCopyR (s t : MachineData) : Prop :=
  rax t = encOpt (shallowestCopyPosition (st s) (slot s)) ∧ st' s t = st s

-- `swapWith(e, _pos)`
def swapWithF : Nat := 8
def swapWithA (s : MachineData) : Prop := Pos (env s).n (st s) ∧ (st s).trace.length < cap s
def swapWithR (s t : MachineData) : Prop :=
  Res (rdi s) (swapWith (st s) (rsi s).toNat) (Ok s t id) t

-- `push(e, _slot, _destination)`
def pushF : Nat := 8
def pushA (s : MachineData) : Prop :=
  (rdx s).toNat < (env s).n ∧ (st s).len < (env s).n ∧ (st s).trace.length < cap s
def pushR (s t : MachineData) : Prop :=
  Res (rdi s) (add (st s) (slot s) (rdx s).toNat (.push (slot s))) (Ok s t id) t

-- `dup(e, _copy, _destination)`
def dupF : Nat := 8
def dupA (s : MachineData) : Prop :=
  (rsi s).toNat < (st s).len ∧ (rdx s).toNat < (env s).n ∧ (st s).len < (env s).n
    ∧ (st s).trace.length < cap s
def dupR (s t : MachineData) : Prop :=
  Res (rdi s) (add (st s) ((st s).val (rsi s).toNat) (rdx s).toNat
    (.dup ((st s).len - (rsi s).toNat))) (Ok s t id) t

-- `produce(e, _targetOffset)`. The return address, six `pushq`, `subq $8` and the
-- frame of a callee. `produce` decrements `m_pendingGenerations` with no check (`subq`),
-- so the count must be positive. The model uses `sizeDec` (the size_t wrap).
def produceF : Nat := 8 + 48 + 8 + 8
def produceA (s : MachineData) : Prop :=
  (rsi s).toNat < (env s).n ∧ (st s).len < (env s).n ∧ (st s).trace.length < cap s
    ∧ 0 < (st s).pendingGenerations
def produceR (s t : MachineData) : Prop :=
  Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t id) t

-- `generate(e, _targetOffset)`. The return address, two `pushq` and the frame of `produce`.
def generateF : Nat := 8 + 16 + produceF
theorem generateF_eq : generateF = 96 := rfl
def generateA (s : MachineData) : Prop :=
  Pos (env s).n (st s) ∧ (st s).len < (env s).n ∧ (st s).trace.length + 2 ≤ cap s
    ∧ 0 < (st s).pendingGenerations
def generateR (s t : MachineData) : Prop :=
  Res (rdi s) (generate (env s) (st s) (rsi s).toNat) (Ok s t id) t

-- `permuteDestinations(e)`, for a permutation of the destinations
-- The locals of `permuteDestinations` from `rsp` after `subq`: `blocked` at 12,
-- `swapDepths` at 16, `permutation` at `finishPerm`, then 8 bytes of padding.
def finishPerm : Nat := 16 + 2 * MAX_N
def finishLocals : Nat := finishPerm + 2 * MAX_N + 8
-- The return address, `pushq %rbp`, `pushq %rbx`, the locals and the frame of `permute`.
def finishF : Nat := 8 + 16 + finishLocals + 16
theorem finishF_eq : finishF = 4160 := rfl
def finishA (s : MachineData) : Prop :=
  IsPerm ((st s).slots.map Slot.dest) ∧ (st s).trace.length + 2 * (st s).len ≤ cap s
def finishR (s t : MachineData) : Prop :=
  Res (rdi s) (finish (st s)) (Ok s t id) t

-- `buildBottomUp(e)`: `loop` from offset 0
-- The return address, six `pushq`, `subq $24` and the frame of `permuteDestinations`.
def loopF : Nat := 8 + 48 + 24 + finishF
theorem loopF_eq : loopF = 4240 := rfl
def loopA (s : MachineData) : Prop := Inv (env s) (st s) 0
def loopR (s t : MachineData) : Prop :=
  Res (rdi s) (loop (env s) (st s) 0) (Ok s t id) t

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
