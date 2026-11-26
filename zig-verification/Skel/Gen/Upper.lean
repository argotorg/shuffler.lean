import Skel.Gen.Types
import Skel.Gen.Shape

/-! The types of the upper generator (`docs/one-way-lift-g3-plan-20261118.md`, sections 4.2 to 4.7; task G3-05). A value of
`UpperPlan` holds the result of the rules 4.1 to 4.7 for one function. The text functions read only this value. The file
has no computation of a plan: that is task G3-06. -/

namespace Skel.Gen

/-- Equality and printing of a name by its string. The proof of validity has no part in either. -/
instance : DecidableEq Ident := fun a b =>
  if h : a.s = b.s then isTrue (by cases a; cases b; cases h; rfl) else isFalse (fun e => h (by cases e; rfl))

instance : Repr Ident where
  reprPrec i _ := repr i.s

/-- The result of the function (4.4): a value (`Encode.encode y = [r]`), a heap, or both. -/
inductive ResultKind where
  | value | heap | both
  deriving DecidableEq, Repr

/-- The L3 value of a value result (4.4), and how the register `rax` holds it. `bits w` is a `BitVec w`: with `w = 64` the
register is the value (`rax.toBitVec = y`); a narrower `w` compares the field of the low `w` bits of `rax`
(`Encode.encode y = [⟨.Ww, rax.toBitVec.setWidth w⟩]`, the form of `Fn.Return.result`); an error code of an error union with a void
payload is a `bits .W16` (0 is `ok`). `bool` is a `Bool` in one byte (the 8-bit field, 0 or 1), compared as a narrow value.
The bits above the width of `rax` are not part of the result. -/
inductive ValueTy where
  | bits (w : Width)
  | bool
  deriving DecidableEq, Repr

/-- The width of the result in `rax`. -/
def ValueTy.width : ValueTy → Width
  | .bits w => w
  | .bool => .W8

/-- The result is the whole register (64 bits). -/
def ValueTy.isWord (v : ValueTy) : Bool := v.width == Width.W64

/-- The policy is an input of `In2p` iff the result has a heap (4.2). It is a function of the kind, so a plan has no
policy flag that can disagree with its result. -/
def ResultKind.hasPolicy : ResultKind → Bool
  | .value => false
  | .heap | .both => true

/-- The class of a state register (5.2): `pointer`, the base of an access address; `counter`, a scaled index or a branch
operand; `accumulator`, any other register. The memory is not a register: it is `UpperPlan.mem`. -/
inductive FieldClass where
  | pointer | counter | accumulator
  deriving DecidableEq, Repr

/-- The type of a parameter of `l3` (4.5). Address forms have samplers; other fixed parameters keep their elaborated type. -/
inductive BinderTy where
  | addr    -- `BitVec 64`
  | addrs   -- `List (BitVec 64)`
  | source (type : Src)
  deriving DecidableEq, Repr

/-- A parameter of `l3`, `SimArr` and the rows: a statement binder after the L3 input `x` (4.5). -/
structure Binder where
  (name : Ident) (ty : BinderTy)
  deriving DecidableEq, Repr

/-- The value of a state register at a loop head, in terms of the input `a` (4.6): the input register `a.r`, a literal, a
value that the entry block loads from the heap (PIL-HEAP), a term of the inputs, or `carried`: the value that a loop before
the head leaves (a head after a loop, or the head of an inner loop; L2-LOOPS). The memory at a head is `a.heap`, so it has
no field. -/
inductive HeadVal where
  | input (r : Reg64)
  | lit (n : UInt64)
  /-- The value of the load of width `w` at the address `addr` in the entry block. `addr` is the text of the address as a
  `BitVec 64` over the input registers, with `x.input.` for the input (`bvText` of `Model.lean`). The loop row takes the value
  as a binder, with the load in `a.heap` as a hypothesis, as it takes the input registers. -/
  | load (addr : String) (w : Width)
  /-- A value of the input registers and constants that the blocks before the head compute (PIL-HEAP: `closestCopy` sets
  `r8 := -rsi` before its head; L2-LOOPS: `l2zNest` sets `rax := rdx * 8`), as the text of a `UInt64` with `x.input.` for
  the input (`u64Text` of `Model.lean`). -/
  | term (t : String)
  /-- The value that a loop before the head leaves in the register (L2-LOOPS). A head with a carried value has no loop row. -/
  | carried
  deriving DecidableEq, Repr

/-- A loop head (4.6): its block, one value per state register, and the number of blocks on its cycle (5.3).
A generalized head has arbitrary state: each register is carried, and region VCs establish its entry relation. -/
structure Head where
  (name : Ident) (state : List (Reg64 × HeadVal)) (cycle : Nat)
  (generalized : Bool := false)
  deriving DecidableEq, Repr

/-- The fuel of the sampler of a head (5.3): `6` for each block of the cycle, and `8`. -/
def Head.fuel (h : Head) : Nat := 6 * h.cycle + 8

/-- A chain ghost of the slots (4.7): `rest_<reg>`, the addresses that `Heap.chain a.heap off` follows from `reg`. -/
structure Ghost where
  (reg : Reg64) (off : Nat)
  deriving DecidableEq, Repr

/-- The plan of the upper generator for one function. The fields of the statement (the L3 input and its fields, the
frame, the policy `pol` of a heap result) follow by the rules of 4.2 and 4.5 and are not stored. -/
structure UpperPlan where
  (fn : String)                              -- the function; the row ids are `<fn>.<row>`
  (inputs : List Reg64)                      -- the registers of `In2p` after `policy` and `heap`, in `Reg64` order (4.2)
  (mem : Bool)                               -- `St` has the parameter `M` (`Vars.mem`, 4.2)
  (state : List (Reg64 × FieldClass))        -- the registers of `St` in order, each with its class (5.2)
  (kind : ResultKind)                        -- the result kind (4.4)
  (val : ValueTy := .bits .W64)              -- the L3 value of a value result; a heap result does not read `rax`
  (params : List Binder)                     -- the statement binders after `x`, in order (4.5)
  (heads : List Head)                        -- the loop heads (4.6)
  (ghosts : List Ghost)                      -- the chain ghosts of the slots (4.7)
  (room : Nat := 0)                          -- the stack room in bytes: `fn.room` of the statement, the room of the code (L3-U5)
  (call : CallForm := .call)                 -- the call form of the statement: `callB` uses `loadB`, `storeB` (D40)
  (hide : Bool := false)                     -- a room and a load through a register, no memory in the state: the L2 input
                                             -- memory is `SysV.hide` (PIL-HEAP), and `rep` says no object meets the room
  (privateStack : Bool := false)             -- initialized private bytes are carried between blocks
  (flags : List Flag := [])                  -- flags carried between blocks
  (stackArgs : Nat := 0)                     -- ABI arguments above the return word
  deriving DecidableEq, Repr

/-- The generated upper state type. Private stack bytes have their own state field. -/
def UpperPlan.stateType (p : UpperPlan) : String :=
  if p.privateStack then "StP" else if p.mem then "St In2p Heap" else "St In2p"

/-- The plan has a stack room and memory in its state (U5b, PIL-CALL2): the L2 model writes the pushes into the memory, so the
frame clauses exclude the room and no object meets the room. -/
def UpperPlan.memRoom (p : UpperPlan) : Bool := p.mem && 0 < p.room

/-- The frame clause of a heap result from the state `s` to the memory `m`: each byte that `heap` does not own, and, for
`memRoom`, that is not one of the room bytes below `sp`, is the byte of `s`. -/
def UpperPlan.frameClause (p : UpperPlan) (b heap sp m s : String) : String :=
  let room := if p.memRoom then s!"¬ SysV.Below {sp} {p.room} {b} → " else ""
  s!"∀ {b}, ¬ {heap}.Owned {b} → {room}{m}.get? {b} = {s}.get? {b}"

/-- A value result keeps every byte outside its stack room. -/
def UpperPlan.valueFrameClause (p : UpperPlan) (b sp m s : String) : String :=
  if p.room == 0 then s!"{m} = {s}"
  else s!"∀ {b}, ¬ SysV.Below {sp} {p.room} {b} → {m}.get? {b} = {s}.get? {b}"

/-- The conjunct that no object of `heap` meets the room below `sp` (PIL-HEAP `hide`, U5b `memRoom`), or none. -/
def UpperPlan.belowConj (p : UpperPlan) (b sp heap : String) : List String :=
  if p.hide || p.memRoom then [s!"(∀ {b}, SysV.Below {sp} {p.room} {b} → ¬ Covered {heap} {b})"] else []

end Skel.Gen
