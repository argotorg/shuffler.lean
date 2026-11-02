module

public import FlatShuffler.FlatRel
import all FlatShuffler.FlatRel
public import FlatShuffler.Unit.LoopInv
import all FlatShuffler.Unit.LoopInv
public import FlatShuffler.Sep.Contract
import all FlatShuffler.Sep.Contract
public import FlatShuffler.Asm
import all FlatShuffler.Asm
public import FlatShuffler.Names
import all FlatShuffler.Names

@[expose] public section

/-!
# The unit contracts

Each unit theorem (`Unit/*.lean`) is a `UnitThm`: the asm of one C++ function, started in a
state that satisfies the separation contract `Sep.Pre S g F A d` for a ghost `g`, returns in a
state with a ghost `g'` that satisfies `Q g g' s t` (`Sep.Post`). The callers use the callee
theorems through `Sep.spec_of_body`.

For status-returning methods that write the struct, the normal result uses
`NormalResult f`. It requires the state and status comparison in `Res f` and
excludes assertion failure. The return byte is 0 for Done or 1 for Blocked.
`Res f` alone is a model relation; it can also describe a failed assertion.
The native assertion outcome uses a separate exit contract, defined in `ExitDefs.lean`.

`flat g` reads only the low 6 bytes of each slot word (`StackSlot.ofWord`), because the C++
compares and copies these bytes only: `swapWith` copies 6 bytes into the top slot, and `push`
stores the 8 bytes of its argument.
-/

namespace FlatShuffler.Unit

open FlatShuffler.Sep (G)

-- A buffer of `maxStackSize` elements that holds `l` from offset 0, and `default` above it.
def vec {α : Type} [Inhabited α] (l : List α) : Vector α maxStackSize :=
  Vector.ofFn fun i => l[i.val]?.getD default

-- The flat state of the ghost `g`. The trace is the records below `m_traceSize`.
def flat (g : G) : Flat.St where
  target := vec (g.tgt.toList.map StackSlot.ofWord)
  targetSize := g.h.n
  spills := g.spl
  data := vec (g.stk.toList.map StackSlot.ofWord)
  size := g.h.len
  trace := (g.ops.toList.take g.h.nops.toNat).map Sep.OpR.op
  dest := g.h.dest
  pos := g.h.pos
  pend := g.h.pend
  blockedOffset := g.h.blkOff
  blockedExcess := g.h.blkExc

-- The members that no function writes: the pointers, `m_targetSize`, the target and the
-- spilled bytes.
structure Keep (g g' : G) : Prop where
  tgtp : g'.h.tgt = g.h.tgt
  n : g'.h.n = g.h.n
  splp : g'.h.spl = g.h.spl
  data : g'.h.data = g.h.data
  ops : g'.h.ops = g.h.ops
  xs : g'.xs = g.xs
  xo : g'.xo = g.xo
  tgt : g'.tgt.toList = g.tgt.toList
  spl : g'.spl = g.spl

-- `G.Ok` of `g'`: `G.Ok.n` and `G.Ok.spl` read only the members that `Keep` keeps.
theorem Keep.ok {g g' : G} (hk : Keep g g') (h : g.Ok)
    (hl : g'.h.len.toNat ≤ g'.h.n.toNat + g'.xs)
    (hn : g'.h.nops.toNat ≤ 6 * g'.h.n.toNat + g'.xo) : g'.Ok where
  len := hl
  n := by rw [hk.n]; exact h.n
  xs := by rw [hk.n, hk.xs]; exact h.xs
  xo := by rw [hk.xo]; exact h.xo
  nops := hn
  spl i hi k hk' j hj ha := by
    have hkn : k < g.h.n.toNat := by rw [← hk.n]; exact hk'
    have e : g'.tgt[k] = g.tgt[k] := by
      rw [← Vector.getElem_toList (by simpa using hk'),
        ← Vector.getElem_toList (by simpa using hkn)]
      exact List.getElem_of_eq hk.tgt _
    rw [hk.spl, e]
    exact h.spl i (hk.tgt ▸ hi) k hkn j hj (hk.splp ▸ hk.tgtp ▸ ha)

-- The byte `al` of a `Status`.
def code : Flat.Status → BitVec 8
  | .done => DONE
  | .blocked => BLOCKED
  | .assertionFailed => ASSERTION_FAILED

-- The result of a function that writes the struct: the flat model function `f`.
def Res (f : Flat.St → Flat.Status × Flat.St) (g g' : G) (t : MachineData) : Prop :=
  Keep g g' ∧ flat g' = (f (flat g)).2 ∧ al t = code (f (flat g)).1

/-- Compare the state and status with the flat model, and exclude assertion failure on return. -/
def NormalResult (f : Flat.St → Flat.Status × Flat.St) (g g' : G) (t : MachineData) : Prop :=
  Res f g g' t ∧ al t ≠ ASSERTION_FAILED

theorem NormalResult.of_returnRegister_eq
    {f : Flat.St → Flat.Status × Flat.St} {g g' : G} {before after : MachineData}
    (result : NormalResult f g g' before) (sameReturnRegister : rax after = rax before) :
    NormalResult f g g' after := by
  have sameReturnByte : al after = al before :=
    congrArg (fun value : Word => value.setWidth 8) sameReturnRegister
  exact ⟨⟨result.1.1, result.1.2.1, sameReturnByte.trans result.1.2.2⟩,
    fun failed => result.2 (sameReturnByte.symm.trans failed)⟩

-- The destination of each slot is none or a target offset: `swapDestinations` writes
-- `m_positionOf` at these offsets.
def DestOk (fs : Flat.St) : Prop :=
  ∀ i < fs.size.toNat, Flat.get fs.dest (BitVec.ofNat 64 i) = Flat.NONE
    ∨ (Flat.get fs.dest (BitVec.ofNat 64 i)).toNat < fs.targetSize.toNat

-- The destinations are a permutation of the offsets below the size. Then the loop of `permute`
-- ends (see `Flat.permuteLoop`).
structure PermOk (fs : Flat.St) : Prop where
  lt : ∀ i < fs.size.toNat, (Flat.get fs.dest (BitVec.ofNat 64 i)).toNat < fs.size.toNat
  inj : ∀ i < fs.size.toNat, ∀ j < fs.size.toNat,
    Flat.get fs.dest (BitVec.ofNat 64 i) = Flat.get fs.dest (BitVec.ofNat 64 j) → i = j

-- A unit theorem: the body of `prog` with the precondition `A`, `d` free stack words and the
-- result `Q`, for each struct address, ghost and frame. `Sep.spec_of_body` makes it a `Sep.Spec`.
abbrev UnitThm [Host] [FunDecls] (prog : Program) (A : G → MachineData → Prop) (d : Nat)
    (Q : G → G → MachineData → MachineData → Prop) : Prop :=
  ∀ S g F, Sep.Body prog (Sep.Pre S g F A d) (fun s t => Sep.Post S F d (fun g' t => Q g g' s t) s t)

-- A unit theorem of a function that also owns `W s` (see `Sep.SpecW`).
abbrev UnitThmW [Host] [FunDecls] (prog : Program) (W : MachineData → MProp 64)
    (A : G → MachineData → Prop) (d : Nat) (Q : G → G → MachineData → MachineData → Prop) : Prop :=
  ∀ S g F, Sep.Body prog (fun s => Sep.Pre S g (W s ∗ F) A d s)
    (fun s t => Sep.Post S (W s ∗ F) d (fun g' t => Q g g' s t) s t)

/-! ## The preconditions and the results

`rsi` and `rdx` are the arguments after `this`. A slot argument is the word of the slot. -/

-- `isSpilled(slot)`: the byte that it reads is in the view.
def isSpilledA (g : G) (s : MachineData) : Prop :=
  ∀ i, spillId (StackSlot.ofWord (rsi s)) = some i → i ∈ Sep.splIds g.tgt.toList
def isSpilledQ (g g' : G) (s t : MachineData) : Prop :=
  g' = g ∧ al t = if Flat.isSpilled (flat g) (StackSlot.ofWord (rsi s)) then 1#8 else 0#8

-- `shallowestCopyPosition(slot)`
def shallowestCopyA (_g : G) (_s : MachineData) : Prop := True
def shallowestCopyQ (g g' : G) (s t : MachineData) : Prop :=
  g' = g ∧ rax t = Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord (rsi s))

-- `push(slot, destination)`: a free slot, a free record, and a destination in `m_positionOf`.
def pushA (g : G) (s : MachineData) : Prop :=
  g.h.len.toNat < g.h.n.toNat ∧ g.h.nops.toNat < 6 * g.h.n.toNat + g.xo ∧ (rdx s).toNat < g.h.n.toNat
def pushQ (g g' : G) (s t : MachineData) : Prop :=
  NormalResult (Flat.push · (StackSlot.ofWord (rsi s)) (rdx s)) g g' t

-- `dup(copy, destination)`: also a copy in the working stack.
def dupA (g : G) (s : MachineData) : Prop :=
  (rsi s).toNat < g.h.n.toNat ∧ g.h.len.toNat < g.h.n.toNat ∧ g.h.nops.toNat < 6 * g.h.n.toNat + g.xo
    ∧ (rdx s).toNat < g.h.n.toNat
def dupQ (g g' : G) (s t : MachineData) : Prop := NormalResult (Flat.dup · (rsi s) (rdx s)) g g' t

-- `swapWith(pos)`
def swapWithA (g : G) (_s : MachineData) : Prop :=
  g.h.nops.toNat < 6 * g.h.n.toNat + g.xo ∧ DestOk (flat g)
def swapWithQ (g g' : G) (s t : MachineData) : Prop := NormalResult (Flat.swapWith · (rsi s)) g g' t

-- `produce(targetOffset)`
def produceA (g : G) (s : MachineData) : Prop :=
  (rsi s).toNat < g.h.n.toNat ∧ g.h.len.toNat < g.h.n.toNat ∧ g.h.nops.toNat < 6 * g.h.n.toNat + g.xo
def produceQ (g g' : G) (s t : MachineData) : Prop := NormalResult (Flat.produce · (rsi s)) g g' t

-- `generate(targetOffset)`: room for the operation of `produce` and a swap.
def generateA (g : G) (_s : MachineData) : Prop :=
  g.h.len.toNat < g.h.n.toNat ∧ g.h.nops.toNat + 2 ≤ 6 * g.h.n.toNat + g.xo ∧ DestOk (flat g)
def generateQ (g g' : G) (s t : MachineData) : Prop := NormalResult (Flat.generate · (rsi s)) g g' t

-- `p` is a bijection of the offsets below `n`.
def Bij (n : Word) (p : Vector Word maxStackSize) : Prop :=
  (∀ i < n, Flat.get p i < n) ∧ ∀ i < n, ∀ k < n, Flat.get p i = Flat.get p k → i = k

-- `permute(permutation)` for the ghost `p`: room for `2 * size` swaps, the destinations are none
-- or target offsets, `p` is a bijection of the offsets below the size, and `permutation` (the
-- array at `rsi`, in the frame `permW`) holds `p` below the size.
def permuteA (p : Vector Word maxStackSize) (g : G) (s : MachineData) : Prop :=
  g.h.nops.toNat + 2 * g.h.len.toNat ≤ 6 * g.h.n.toNat + g.xo ∧ DestOk (flat g) ∧ Bij g.h.len p
    ∧ ∀ i < g.h.len.toNat,
      rd s.dmem (rsi s + BitVec.ofNat 64 (8 * i)) = Flat.get p (BitVec.ofNat 64 i)
def permW (s : MachineData) : MProp 64 := Sep.ExArr (rsi s) maxStackSize
def permuteQ (p : Vector Word maxStackSize) (g g' : G) (_s t : MachineData) : Prop :=
  NormalResult (Flat.permute · p) g g' t

-- `buildBottomUp()`: the invariant of the loop head at `T = 0`. `xo` is the room of the trace
-- buffer for the operations before the loop.
def loopA (g : G) (_s : MachineData) : Prop := Flat.HInv (flat g) 0#64 g.xo
def loopQ (g g' : G) (_s t : MachineData) : Prop := NormalResult Flat.buildBottomUp g g' t

end FlatShuffler.Unit
