import BbuKraken.Layout

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

-- `is_spilled(s, v)`, for `v` in the target.
def isSpilledF : Nat := 8
def isSpilledA (s : MachineData) : Prop := ∃ d < (env s).n, (env s).target[d]! = rsi s
def isSpilledR (s t : MachineData) : Prop :=
  rax t = BitVec.ofNat 64 (isSpilled (env s) (rsi s)).toNat ∧ st' s t = st s

-- `position_of(s, d)`
def positionOfF : Nat := 8
def positionOfA (_ : MachineData) : Prop := True
def positionOfR (s t : MachineData) : Prop :=
  rax t = encOpt (positionOf (st s) (rsi s).toNat) ∧ st' s t = st s

-- `shallowest_copy(s, v)`
def shallowestCopyF : Nat := 8
def shallowestCopyA (_ : MachineData) : Prop := True
def shallowestCopyR (s t : MachineData) : Prop :=
  rax t = encOpt (shallowestCopy (st s) (rsi s)) ∧ st' s t = st s

-- `swap_with(s, pos)`
def swapWithF : Nat := 8
def swapWithA (s : MachineData) : Prop := (st s).ops.length < cap s
def swapWithR (s t : MachineData) : Prop :=
  Res (rdi s) (swapWith (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t

-- `add(s, v, d, kind, arg)`
def addF : Nat := 56
def addA (s : MachineData) : Prop := (st s).len < 256 ∧ (st s).ops.length < cap s
def addR (s t : MachineData) : Prop :=
  Res (rdi s) (add (st s) (rsi s) (rdx s).toNat ⟨rcx s, r8 s⟩) (Ok s t (fun _ => 0#64) id) t

-- `produce(s, d)`
def produceF : Nat := 96
def produceA (s : MachineData) : Prop :=
  (rsi s).toNat < (env s).n ∧ (st s).len < 256 ∧ (st s).ops.length < cap s
def produceR (s t : MachineData) : Prop :=
  Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t

-- `generate(s, d)`
def generateF : Nat := 120
def generateA (s : MachineData) : Prop := (st s).len < 256 ∧ (st s).ops.length + 2 ≤ cap s
def generateR (s t : MachineData) : Prop :=
  Res (rdi s) (generate (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t

-- `urgent(s, t)`
def urgentF : Nat := 64
def urgentA (_ : MachineData) : Prop := True
def urgentR (s t : MachineData) : Prop :=
  Res (rdi s) (urgent (env s) (st s) (rsi s).toNat)
    (Ok s t (fun u => BitVec.ofNat 64 u) (fun _ => st s)) t

-- `take_bound(s, t, b)`, for the slot `b` bound for `t`
def takeBoundF : Nat := 16
def takeBoundA (s : MachineData) : Prop :=
  (rdx s).toNat < (st s).len ∧ (st s).ops.length < cap s
def takeBoundR (s t : MachineData) : Prop :=
  Res (rdi s) (takeBound (st s) (rsi s).toNat (rdx s).toNat)
    (Ok s t (fun r => if r.2 then 0#64 else 1#64) Prod.fst) t

def encNext : Next → Word
  | .next t => BitVec.ofNat 64 t
  | .finish => -3#64

-- `step(s, t)`
def stepF : Nat := 152
def stepA (s : MachineData) : Prop :=
  (rsi s).toNat < (env s).n ∧ (st s).len + (st s).pending ≤ (env s).n
    ∧ (st s).ops.length + 3 ≤ cap s
def stepR (s t : MachineData) : Prop :=
  Res (rdi s) (step (env s) (st s) (rsi s).toNat) (Ok s t (fun r => encNext r.2) Prod.fst) t

-- `finish(s)`, for a permutation of the destinations
def finishF : Nat := 816
def finishA (s : MachineData) : Prop :=
  IsPerm ((st s).slots.map Slot.dest) ∧ (st s).ops.length + 2 * (st s).len ≤ cap s
def finishR (s t : MachineData) : Prop :=
  Res (rdi s) (finish (st s)) (fun ops => rax t = BitVec.ofNat 64 ops.length ∧ (st' s t).ops = ops) t

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
