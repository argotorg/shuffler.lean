import Lift.Pilot.Call
import Lift.Spike.SumStatement
import Lift.Pilot.AlignmentStatement
import Lift.Level2z.Args8Statement
import Lift.Level3.L1
import Lift.Sem.Model
import Lift.Sem.Bridge

/-! The synthetic statements of the suite `genfinal` (task FINAL-LINK): one for each call form or result form that no real
statement with an upper chain has. The suite reads their shapes with `#stmt_shape` (`Skel.Toy.Held.stmtShapeText`).

- `B.SumB`: `toySum` in the call form `Fn.CallB` (the objects, the arguments and `post` of `SumStatement`). The upper chain of the
  suite is generated (`generateUpper`).
- `W8.Stmt`: `workspaceAlignment` (room 8) in the call form `Call8` of `Args8Statement`, with the six register arguments
  `a` to `f`, the stack arguments `g` and `h`, and no object. The plan refuses `Call8` on this branch, so `l3` is written here as the relation text of
  L2-NORUN writes it: the stack words are the last conjunct of `rep`.
- `R.Stmt`: `workspaceAlignment` in the call form `Fn.Call` with a result term and no `run` (the result form of L2-NORUN): `post`
  is `Encode.encode (g + h) = [r]`, and `run3` is `some` of the term. `l3` is written as the relation text of L2-NORUN writes it.

The statements are not true of the code: the suite checks only the text of the last step, with the row `contract` as a
hypothesis. -/

namespace Skel.Test.FinalSpec

open Lift.P2.Total Lift.Sem Lift.Trusted Lift.Sem.Bridge

namespace B

/-- `toySum` with `Fn.CallB`. -/
def SumB : Prop :=
  ∀ xs, Lift.Spike.SumSpec.C xs → ∀ p : BitVec 64,
    Lift.Spike.SumStatement.toySum.CallB [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 xs.length⟩]
      (Lift.Spike.SumStatement.objects xs p) (Lift.Spike.SumStatement.post xs)

end B

namespace W8

def C (_ _ _ _ _ _ _ _ : BitVec 64) : Prop := True

def run (a b c d e f g h : BitVec 64) : Option (BitVec 64) := some (a + b + c + d + e + f + g + h)

def objects : List Object := []

def post (a b c d e f g h : BitVec 64) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run a b c d e f g h = some y ∧ Encode.encode y = [r]

/-- `workspaceAlignment` with six register arguments and two stack arguments. -/
def Stmt : Prop :=
  ∀ a b c d e f g h, C a b c d e f g h →
    Lift.Level2z.Args8Statement.Call8 Lift.Pilot.AlignmentStatement.workspaceAlignment
      (Lift.Level2z.Args8Statement.args a b c d e f) g h objects (post a b c d e f g h)

def objsP (_ _ _ _ _ _ _ _ : BitVec 64) : Heap := (Skel.Test.FinalSpec.W8.objects).map toObj

def l3 (frame : Heap) (a b c d e f g h : BitVec 64) : Model Unit (BitVec 64) where
  rep policy _ s := Heap.Holds policy (objsP a b c d e f g h ++ frame) s.data.dmem ∧
    C a b c d e f g h ∧
    SysV.Entry policy Lift.Level3.workspaceAlignmentPC Lift.Level3.pilotEndPC Lift.Level3.workspaceAlignmentPC s ∧
    s.data.regs.rdi.toBitVec = a ∧ s.data.regs.rsi.toBitVec = b ∧ s.data.regs.rdx.toBitVec = c ∧
    s.data.regs.rcx.toBitVec = d ∧ s.data.regs.r8.toBitVec = e ∧ s.data.regs.r9.toBitVec = f ∧
    SysV.StackRoom policy s 8 ∧
    Lift.Trusted.Mem.has policy s.data.dmem ⟨s.data.regs.rsp.toBitVec + 8, [⟨.W64, g⟩, ⟨.W64, h⟩], false⟩
  returns _ y := Skel.Test.FinalSpec.W8.run (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) (g := g) (h := h) = some y
  post _ y s t := SysV.Exit s t ∧ SysV.Outside s 8 t.data.dmem ∧ t.data.regs.rax.toBitVec = y

end W8

namespace W8B

def C (_ _ _ _ _ _ _ _ : BitVec 64) : Prop := True

def run (a b c d e f g h : BitVec 64) : Option (BitVec 64) := W8.run a b c d e f g h

def objects : List Object := []

def post (a b c d e f g h : BitVec 64) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run a b c d e f g h = some y ∧ Encode.encode y = [r]

/-- The byte-range call form with six register arguments and two stack arguments. -/
def Stmt : Prop :=
  ∀ a b c d e f g h, C a b c d e f g h →
    Lift.Pilot.AlignmentStatement.workspaceAlignment.Call8B
      (Lift.Level2z.Args8Statement.args a b c d e f) g h objects (post a b c d e f g h)

def objsP (_ _ _ _ _ _ _ _ : BitVec 64) : Heap := (Skel.Test.FinalSpec.W8B.objects).map toObj

def l3 (frame : Heap) (a b c d e f g h : BitVec 64) : Model Unit (BitVec 64) where
  rep policy _ s := Heap.Holds policy (objsP a b c d e f g h ++ frame) s.data.dmem ∧
    Heap.Permits policy (objsP a b c d e f g h ++ frame) ∧ C a b c d e f g h ∧
    SysV.Entry policy Lift.Level3.workspaceAlignmentPC Lift.Level3.pilotEndPC Lift.Level3.workspaceAlignmentPC s ∧
    s.data.regs.rdi.toBitVec = a ∧ s.data.regs.rsi.toBitVec = b ∧ s.data.regs.rdx.toBitVec = c ∧
    s.data.regs.rcx.toBitVec = d ∧ s.data.regs.r8.toBitVec = e ∧ s.data.regs.r9.toBitVec = f ∧
    SysV.StackRoom policy s 8 ∧
    Lift.Trusted.Mem.has policy s.data.dmem ⟨s.data.regs.rsp.toBitVec + 8, [⟨.W64, g⟩, ⟨.W64, h⟩], false⟩
  returns _ y := Skel.Test.FinalSpec.W8B.run (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) (g := g) (h := h) = some y
  post _ y s t := SysV.Exit s t ∧ SysV.Outside s 8 t.data.dmem ∧ t.data.regs.rax.toBitVec = y

end W8B

namespace R

def objects : List Object := []

def post (g h : BitVec 64) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop := Encode.encode (g + h) = [r]

/-- `workspaceAlignment` with a result term. -/
def Stmt : Prop :=
  ∀ g h : BitVec 64, Lift.Pilot.AlignmentStatement.workspaceAlignment.Call [] objects (post g h)

def run3 (g h : BitVec 64) := some (g + h)

def objsP (g h : BitVec 64) : Heap := (Skel.Test.FinalSpec.R.objects).map toObj

def l3 (frame : Heap) (g h : BitVec 64) : Model Unit (BitVec 64) where
  rep policy _ s := Heap.Holds policy (objsP g h ++ frame) s.data.dmem ∧
    SysV.Entry policy Lift.Level3.workspaceAlignmentPC Lift.Level3.pilotEndPC Lift.Level3.workspaceAlignmentPC s ∧
    SysV.StackRoom policy s 8
  returns _ y := run3 (g := g) (h := h) = some y
  post _ y s t := SysV.Exit s t ∧ SysV.Outside s 8 t.data.dmem ∧ t.data.regs.rax.toBitVec = y

end R

/-! The statements with a `Nat` argument `BitVec.ofNat 64 t` (task FINAL-BOUND). `workspaceAlignment` stands for the code, as in `R`. The
object is the array `xs` of words at `p`. The suite checks the text of the last step with the row `contract` as a hypothesis.
- `N`: the contract is `xs = [] ∨ t < xs.length` and the result does not depend on `t` when `xs = []`. The bound of `t` is in the
  second case, from the array of the object (`Mem.has`); the first case needs `t % 2 ^ 64`.
- `M1`: the contract is `True` and the result depends on `t` (`t / 2 ^ 64`, not only on `t % 2 ^ 64`): no bound, and no way to drop `t`.
- `P`: the contract is `True` and the result is `BitVec.ofNat 64 t`: it depends on `t % 2 ^ 64` only, so the statement for `t` is the statement
  for `t % 2 ^ 64` and there is no bound to prove.
- `M2`: the contract is as of `N`, but the result depends on `t` also when `xs = []`: the first case has no bound. -/

namespace N

def C (xs : List (BitVec 64)) (t : Nat) : Prop := xs = [] ∨ t < xs.length

def run (xs : List (BitVec 64)) (t : Nat) : Option (BitVec 64) :=
  if xs = [] then some 0 else some (BitVec.ofNat 64 t)

def objects (xs : List (BitVec 64)) (p : BitVec 64) : List Object := [⟨p, Encode.encode xs, false⟩]

def post (xs : List (BitVec 64)) (t : Nat) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run xs t = some y ∧ Encode.encode y = [r]

def Stmt : Prop :=
  ∀ (xs : List (BitVec 64)) (t : Nat), C xs t → ∀ p : BitVec 64,
    Lift.Pilot.AlignmentStatement.workspaceAlignment.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 t⟩] (objects xs p) (post xs t)

def objsP (p : BitVec 64) (xs : List (BitVec 64)) (_ : Nat) : Heap := (objects xs p).map toObj

def l3 (p : BitVec 64) (frame : Heap) (xs : List (BitVec 64)) (t : Nat) : Model Unit (BitVec 64) where
  rep policy _ s := Heap.Holds policy (objsP p xs t ++ frame) s.data.dmem ∧ C xs t ∧
    SysV.Entry policy Lift.Level3.workspaceAlignmentPC Lift.Level3.pilotEndPC Lift.Level3.workspaceAlignmentPC s ∧
    s.data.regs.rdi.toBitVec = p ∧ s.data.regs.rsi.toNat = t ∧ SysV.StackRoom policy s 8
  returns _ y := Skel.Test.FinalSpec.N.run (xs := xs) (t := t) = some y
  post _ y s t' := SysV.Exit s t' ∧ SysV.Outside s 8 t'.data.dmem ∧ t'.data.regs.rax.toBitVec = y

end N

namespace M1

def C (_ : List (BitVec 64)) (_ : Nat) : Prop := True

def run (xs : List (BitVec 64)) (t : Nat) : Option (BitVec 64) := some (BitVec.ofNat 64 (t / 2 ^ 64))

def objects (xs : List (BitVec 64)) (p : BitVec 64) : List Object := [⟨p, Encode.encode xs, false⟩]

def post (xs : List (BitVec 64)) (t : Nat) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run xs t = some y ∧ Encode.encode y = [r]

def Stmt : Prop :=
  ∀ (xs : List (BitVec 64)) (t : Nat), C xs t → ∀ p : BitVec 64,
    Lift.Pilot.AlignmentStatement.workspaceAlignment.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 t⟩] (objects xs p) (post xs t)

def objsP (p : BitVec 64) (xs : List (BitVec 64)) (_ : Nat) : Heap := (objects xs p).map toObj

def l3 (p : BitVec 64) (frame : Heap) (xs : List (BitVec 64)) (t : Nat) : Model Unit (BitVec 64) where
  rep policy _ s := Heap.Holds policy (objsP p xs t ++ frame) s.data.dmem ∧ C xs t ∧
    SysV.Entry policy Lift.Level3.workspaceAlignmentPC Lift.Level3.pilotEndPC Lift.Level3.workspaceAlignmentPC s ∧
    s.data.regs.rdi.toBitVec = p ∧ s.data.regs.rsi.toNat = t ∧ SysV.StackRoom policy s 8
  returns _ y := Skel.Test.FinalSpec.M1.run (xs := xs) (t := t) = some y
  post _ y s t' := SysV.Exit s t' ∧ SysV.Outside s 8 t'.data.dmem ∧ t'.data.regs.rax.toBitVec = y

end M1

namespace P

def C (_ : List (BitVec 64)) (_ : Nat) : Prop := True

def run (xs : List (BitVec 64)) (t : Nat) : Option (BitVec 64) := some (BitVec.ofNat 64 (t))

def objects (xs : List (BitVec 64)) (p : BitVec 64) : List Object := [⟨p, Encode.encode xs, false⟩]

def post (xs : List (BitVec 64)) (t : Nat) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run xs t = some y ∧ Encode.encode y = [r]

def Stmt : Prop :=
  ∀ (xs : List (BitVec 64)) (t : Nat), C xs t → ∀ p : BitVec 64,
    Lift.Pilot.AlignmentStatement.workspaceAlignment.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 t⟩] (objects xs p) (post xs t)

def objsP (p : BitVec 64) (xs : List (BitVec 64)) (_ : Nat) : Heap := (objects xs p).map toObj

def l3 (p : BitVec 64) (frame : Heap) (xs : List (BitVec 64)) (t : Nat) : Model Unit (BitVec 64) where
  rep policy _ s := Heap.Holds policy (objsP p xs t ++ frame) s.data.dmem ∧ C xs t ∧
    SysV.Entry policy Lift.Level3.workspaceAlignmentPC Lift.Level3.pilotEndPC Lift.Level3.workspaceAlignmentPC s ∧
    s.data.regs.rdi.toBitVec = p ∧ s.data.regs.rsi.toNat = t ∧ SysV.StackRoom policy s 8
  returns _ y := Skel.Test.FinalSpec.P.run (xs := xs) (t := t) = some y
  post _ y s t' := SysV.Exit s t' ∧ SysV.Outside s 8 t'.data.dmem ∧ t'.data.regs.rax.toBitVec = y

end P

namespace M2

def C (xs : List (BitVec 64)) (t : Nat) : Prop := xs = [] ∨ t < xs.length

def run (xs : List (BitVec 64)) (t : Nat) : Option (BitVec 64) := some (BitVec.ofNat 64 (t / 2 ^ 64))

def objects (xs : List (BitVec 64)) (p : BitVec 64) : List Object := [⟨p, Encode.encode xs, false⟩]

def post (xs : List (BitVec 64)) (t : Nat) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run xs t = some y ∧ Encode.encode y = [r]

def Stmt : Prop :=
  ∀ (xs : List (BitVec 64)) (t : Nat), C xs t → ∀ p : BitVec 64,
    Lift.Pilot.AlignmentStatement.workspaceAlignment.Call [⟨.W64, p⟩, ⟨.W64, BitVec.ofNat 64 t⟩] (objects xs p) (post xs t)

def objsP (p : BitVec 64) (xs : List (BitVec 64)) (_ : Nat) : Heap := (objects xs p).map toObj

def l3 (p : BitVec 64) (frame : Heap) (xs : List (BitVec 64)) (t : Nat) : Model Unit (BitVec 64) where
  rep policy _ s := Heap.Holds policy (objsP p xs t ++ frame) s.data.dmem ∧ C xs t ∧
    SysV.Entry policy Lift.Level3.workspaceAlignmentPC Lift.Level3.pilotEndPC Lift.Level3.workspaceAlignmentPC s ∧
    s.data.regs.rdi.toBitVec = p ∧ s.data.regs.rsi.toNat = t ∧ SysV.StackRoom policy s 8
  returns _ y := Skel.Test.FinalSpec.M2.run (xs := xs) (t := t) = some y
  post _ y s t' := SysV.Exit s t' ∧ SysV.Outside s 8 t'.data.dmem ∧ t'.data.regs.rax.toBitVec = y

end M2

end Skel.Test.FinalSpec
