module

/-
The runtime of lifted functions (lifter version 2).

A lifted function is a block machine. Each block is a Lean function `St → Option (Next L)`:
it ends in a jump to a label (`Next.go`, with the flags `Next.goF` when the target reads them) or in
a return (`Next.ret`). `run` is the one driver of all functions; its fuel is the number of block
transitions of one activation, and a call gives its fuel to the callee. `none` is a fault (an
access to an unmapped address, `ud2`, a division error, a return that does not pop the return
address) or fuel that runs out. Loops of any shape need no mutual recursion.

The state `St` has the 16 registers, the memory and two lists that only a call changes:
* `frames`: the return slots (8 bytes at an address) of the active calls. The bytes of a frame are
  not in `m`: the function cannot touch its own return address, and `ret` pops it.
* `dead`: the return slots of calls that returned. The return address that a call pushed is not
  known to the lifted function (`call` is correct for each return address), so the lifted memory
  does not have these bytes either. A later call may use the slot again.
-/
public import Kraken.StateCfg

@[expose] public section

namespace Lift.V2

structure St where
  rax : BitVec 64
  rbx : BitVec 64
  rcx : BitVec 64
  rdx : BitVec 64
  rsi : BitVec 64
  rdi : BitVec 64
  rsp : BitVec 64
  rbp : BitVec 64
  r8 : BitVec 64
  r9 : BitVec 64
  r10 : BitVec 64
  r11 : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  m : Mem 64
  dead : List (BitVec 64)
  frames : List (BitVec 64)

/-- The lifted state of the machine state `s` with the lifted memory `m`. -/
def toSt (s : MachineData) (m : Mem 64) (dead frames : List (BitVec 64)) : St where
  rax := s.regs.rax.toBitVec
  rbx := s.regs.rbx.toBitVec
  rcx := s.regs.rcx.toBitVec
  rdx := s.regs.rdx.toBitVec
  rsi := s.regs.rsi.toBitVec
  rdi := s.regs.rdi.toBitVec
  rsp := s.regs.rsp.toBitVec
  rbp := s.regs.rbp.toBitVec
  r8 := s.regs.r8.toBitVec
  r9 := s.regs.r9.toBitVec
  r10 := s.regs.r10.toBitVec
  r11 := s.regs.r11.toBitVec
  r12 := s.regs.r12.toBitVec
  r13 := s.regs.r13.toBitVec
  r14 := s.regs.r14.toBitVec
  r15 := s.regs.r15.toBitVec
  m := m
  dead := dead
  frames := frames

/-- The address of a symbol: a function that uses one needs the layout (`Labels`) of the program. -/
def lbl [Labels] (l : String) : BitVec 64 := (Labels.label l).toBitVec

/-! ### Memory -/

/-- The memory without the `n` bytes at `a`. -/
def eraseBlock (m : Mem 64) (a : BitVec 64) (n : Nat) : Mem 64 :=
  (List.range n).foldl (fun m i => m.erase (a + BitVec.ofNat 64 i)) m

/-- `movq (a), %r`: the 8 bytes at `a`, or `none` if `a` is not mapped. -/
def ld64 (m : Mem 64) (a : BitVec 64) : Option (BitVec 64) := (m.loadInt a 8).map (BitVec.ofInt 64)
def ld32 (m : Mem 64) (a : BitVec 64) : Option (BitVec 32) := (m.loadInt a 4).map (BitVec.ofInt 32)
def ld16 (m : Mem 64) (a : BitVec 64) : Option (BitVec 16) := (m.loadInt a 2).map (BitVec.ofInt 16)
def ld8 (m : Mem 64) (a : BitVec 64) : Option (BitVec 8) := (m.loadInt a 1).map (BitVec.ofInt 8)

/-- A store of `n` bytes: the memory with these bytes changed, or `none` if `a` is not mapped. -/
def stN (n : Nat) (m : Mem 64) (a : BitVec 64) (v : Int) : Option (Mem 64) :=
  if (m.loadInt a n).isSome then some (m.storeInt a n v) else none

def st64 (m : Mem 64) (a v : BitVec 64) : Option (Mem 64) := stN 8 m a v.toInt
def st32 (m : Mem 64) (a : BitVec 64) (v : BitVec 32) : Option (Mem 64) := stN 4 m a v.toInt
def st16 (m : Mem 64) (a : BitVec 64) (v : BitVec 16) : Option (Mem 64) := stN 2 m a v.toInt
def st8 (m : Mem 64) (a : BitVec 64) (v : BitVec 8) : Option (Mem 64) := stN 1 m a v.toInt

/-! ### Calls -/

/-- The slots of 8 bytes at `a` and `b` do not overlap. -/
def Apart8 (a b : BitVec 64) : Bool := 8 ≤ (a - b).toNat && 8 ≤ (b - a).toNat

/-- `call`, before the callee runs: the return address goes to the slot at `rsp - 8`. The slot
is mapped, or a slot of a call that returned; no active frame overlaps it. -/
def St.enter (st : St) : Option St :=
  let a := st.rsp - 8#64
  if (st.dead.contains a || (st.m.loadInt a 8).isSome) && st.frames.all (Apart8 a) then
    some { st with rsp := a, m := eraseBlock st.m a 8, dead := st.dead.filter (· != a),
                   frames := a :: st.frames }
  else none

/-- `ret`: pops the return slot of this activation, which must be at `rsp`. -/
def St.leave (st : St) : Option St :=
  match st.frames with
  | f :: fs =>
    if st.rsp == f then some { st with rsp := st.rsp + 8#64, dead := f :: st.dead, frames := fs }
    else none
  | [] => none

/-- A direct `call` of the lifted function `g`. -/
def call (g : Nat → St → Option St) (n : Nat) (st : St) : Option St := do g n (← st.enter)

/-! ### The driver -/

inductive Next (L : Type) where
  | go (l : L) (st : St)
  | goF (l : L) (st : St) (fl : StatusFlags)
  | ret (st : St)

/-- `step n l st fl` runs the block `l`; `n` is the fuel for the calls of the block. -/
def run {L : Type} (step : Nat → L → St → StatusFlags → Option (Next L)) :
    Nat → L → St → StatusFlags → Option St
  | 0, _, _, _ => none
  | n + 1, l, st, fl => do
    match ← step n l st fl with
    | .go l' st' => run step n l' st' fl
    | .goF l' st' fl' => run step n l' st' fl'
    | .ret st' => some st'

/-! ### Flags and bytes

The flags that Kraken's `Operation.interp` gives, as functions (the formulas are those of the
semantics). `af` is undefined after some instructions; the lifted code gives no value for it. -/

namespace Fl

/-- `adc`: the source `a`, the destination `b`. -/
def adc {w : Nat} (a b : BitVec w) (c : Bool) : StatusFlags :=
  let cv : BitVec w := if c then 1#w else 0#w
  StatusFlags.from_result (a + b + cv)
    { cf := (a + b + cv).unsigned != a.unsigned + b.unsigned + (if c then 1 else 0),
      af := ((a + b + cv).take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + (if c then 1 else 0),
      of := (a + b + cv).signed != a.signed + b.signed + (if c then 1 else 0) }

def sbb {w : Nat} (b a : BitVec w) (c : Bool) : StatusFlags :=
  let cv : BitVec w := if c then 1#w else 0#w
  StatusFlags.from_result (b - a - cv)
    { cf := (b - a - cv).unsigned != b.unsigned - a.unsigned - (if c then 1 else 0),
      af := ((b - a - cv).take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (if c then 1 else 0),
      of := (b - a - cv).signed != b.signed - a.signed - (if c then 1 else 0) }

def inc {w : Nat} (a : BitVec w) (cf : Bool) : StatusFlags :=
  StatusFlags.from_result (a + 1)
    { cf, af := ((a + 1).take 4).unsigned != (a.take 4).unsigned + 1,
      of := (a + 1).signed != a.signed + 1 }

def dec {w : Nat} (a : BitVec w) (cf : Bool) : StatusFlags :=
  StatusFlags.from_result (a - 1)
    { cf, af := ((a - 1).take 4).unsigned != (a.take 4).unsigned - 1,
      of := (a - 1).signed != a.signed - 1 }

def neg {w : Nat} (b : BitVec w) : StatusFlags :=
  StatusFlags.from_result (-b)
    { cf := b != 0, af := (b.take 4) != 0, of := (-b).signed != - b.signed }

end Fl

/-- `bswap` of 32 and 64 bits: the bytes in the other order. -/
def bswap32 (a : BitVec 32) : BitVec 32 :=
  (a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24).setWidth 32

def bswap64 (a : BitVec 64) : BitVec 64 :=
  (a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
    ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56).setWidth 64

/-- The flags at the entry of a function. No lifted function reads them. -/
def flags0 : StatusFlags := ⟨false, false, false, false, false, false⟩

/-- The function `f` ends in `r` when it runs from `st` with some fuel. -/
def RunsTo (f : Nat → St → Option St) (st r : St) : Prop := ∃ n, f n st = some r

end Lift.V2
