import Lift.Shuffler.Test.Run
import Lift.Shuffler.Internal.Proposed.Layout
import Coordinator.Dst.Rng

/-! The refuter of the proposed internal statements (task INT-Q). It runs the exact L1 of the shuffler
(`Lift.Shuffler.Test.Run.step`) on random entry states of a statement of the template of `Skel/IntQ.lean` and compares the
return state with `post`. A refute file defines `refuteCase` from the definitions of the statement and calls `verdict`.

The entry state of a sample: the PC is the entry of `fn`; the argument registers hold the arguments (the bits above the width
of a field are junk); `rsp` and the return word are those of `Lift/Shuffler/Test/Run.lean`; the `fn.room` bytes below `rsp`, the
return word and the bytes of each object are mapped, and no other byte (an access outside them is a fault). The callee-saved
registers have marks. The run passes when it returns with `rsp + 8` and the marks, the result field is `result` of L3, each
written object of `post` is in the memory, and each object that is not writable is unchanged. A sample whose input is outside
the contract `C` is skipped. Only the input types with a `Draw` instance are supported: a refute file of another input type
does not elaborate, and the verdict is `unknown`. The planner types have derived samplers in `Skel/IntQ/RefuteDraw.lean`. -/

namespace Skel.IntQ.Refute

open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Shuffler.Zig Coordinator.Dst
open Lift.Shuffler.Internal.Proposed
open Lift.Shuffler.Test.Run (rsp0 ra0 marks calleeSaved drive step hex)
open FlatShuffler (StackSlot Word maxStackSize)

/-- A sampler of the inputs of the type `α`. -/
class Draw (α : Type) where
  draw : Rng → α × Rng

export Draw (draw)

def word (g : Rng) : BitVec 64 × Rng := let (x, g) := g.next; (x.toBitVec, g)

/-- A small offset (below 24) or, one time in eight, a random word. -/
def smallWord (g : Rng) : BitVec 64 × Rng :=
  let (k, g) := g.nat 8
  if k == 0 then word g else let (n, g) := g.nat 24; (BitVec.ofNat 64 n, g)

instance : Draw (BitVec 64) := ⟨smallWord⟩
instance : Draw (BitVec 32) := ⟨fun g => let (n, g) := g.nat 16; (BitVec.ofNat 32 n, g)⟩
instance : Draw (BitVec 16) := ⟨fun g => let (x, g) := g.next; (BitVec.ofNat 16 x.toNat, g)⟩
instance : Draw (BitVec 8) := ⟨fun g => let (n, g) := g.nat 4; (BitVec.ofNat 8 n, g)⟩
instance : Draw Bool := ⟨fun g => g.bool⟩

/-- Products use the component samplers in order. -/
instance {α β : Type} [Draw α] [Draw β] : Draw (α × β) := ⟨fun g =>
  let (a, g) := draw g
  let (b, g) := draw g
  ((a, b), g)⟩

/-- Extra pointers have separate 1 MiB regions above the fixed environment and below the stack. -/
def pointer (index : Nat) (g : Rng) : BitVec 64 × Rng :=
  (BitVec.ofNat 64 (0x1000000 + index * 0x100000), g)

/-- A slot: a payload below 16, a kind of the four kinds (or another byte), an opcode 0, 5 or 7. -/
instance : Draw StackSlot := ⟨fun g =>
  let (p, g) := g.nat 16
  let (k, g) := g.pick (0 : Nat) [1, 2, 3, 9]
  let (o, g) := g.pick (0 : Nat) [5, 7]
  (⟨BitVec.ofNat 32 p, BitVec.ofNat 8 k, BitVec.ofNat 8 o⟩, g)⟩

/-- `n` draws. -/
def drawList {α : Type} [Draw α] (g : Rng) : Nat → List α × Rng
  | 0 => ([], g)
  | n + 1 => let (x, g) := draw g; let (xs, g) := drawList g n; (x :: xs, g)

/-- A vector of `n` elements: the first 24 are drawn, the others are `d` (the rule of the vectors of SAMPLE-DERIVE,
`Skel/Discover/Rand.lean`: a draw costs the same for 24 and for 1024 elements). -/
def drawVec {α : Type} {n : Nat} [Draw α] (d : α) (g : Rng) : Vector α n × Rng :=
  let (xs, g) := drawList g (min n 24)
  (Vector.ofFn fun i => xs.getD i.val d, g)

/-- A vector (`permutation : Vector Word maxStackSize` of `permute`, INT-Q2): `drawVec` with the default element. -/
instance {α : Type} {n : Nat} [Draw α] [Inhabited α] : Draw (Vector α n) := ⟨drawVec default⟩

/-- An offset of the mapping below `bound`, or `NONE` one time in four (and when `bound` is 0). The destinations are below the
target size and the positions below the stack size, as in a state of the model, so that the contracts that say so hold. -/
def mapWord (bound : Nat) (g : Rng) : BitVec 64 × Rng :=
  let (k, g) := g.nat 4
  if k == 0 || bound == 0 then (FlatShuffler.Flat.NONE, g) else let (n, g) := g.nat bound; (BitVec.ofNat 64 n, g)

/-- A state of the emission: the arrays with 24 drawn elements, sizes below 24, a reach of 0 to 16, spill bytes of a table of
16, a trace of at most 8 operations. -/
instance : Draw St := ⟨fun g =>
  let (target, g) := drawVec default g
  let (targetPad, g) := drawVec 0 g
  let (ts, g) := g.nat 24
  let (sp, g) := drawList (α := BitVec 8) g 16
  let (reach, g) := g.nat 17
  let (data, g) := drawVec default g
  let (pad, g) := drawVec 0 g
  let (size, g) := g.nat 24
  let (dl, g) := (List.range 24).foldl (fun (acc, g) _ => let (w, g) := mapWord ts g; (acc ++ [w], g)) ([], g)
  let (pl, g) := (List.range 24).foldl (fun (acc, g) _ => let (w, g) := mapWord size g; (acc ++ [w], g)) ([], g)
  let (pend, g) := smallWord g
  let (nt, g) := g.nat 9
  let trace := (List.range nt).map fun i => (⟨FlatShuffler.Op.pop, BitVec.ofNat 16 i⟩ : OpP)
  ({ target, targetPad, targetSize := BitVec.ofNat 64 ts, spills := fun id => sp.getD id.toNat 0,
     maxSwapDepth := BitVec.ofNat 64 reach, maxDupDepth := BitVec.ofNat 64 reach - 1, data, pad,
     size := BitVec.ofNat 64 size, trace, dest := Vector.ofFn fun i => dl.getD i.val FlatShuffler.Flat.NONE,
     pos := Vector.ofFn fun i => pl.getD i.val FlatShuffler.Flat.NONE, pend, blockedOffset := 0, blockedExcess := 0 }, g)⟩

/-- The addresses of a sample: apart from each other, from the code and from the stack. -/
def env (g : Rng) : Layout.Env × Rng :=
  let (p, g) := (draw g : BitVec 16 × Rng)
  ({ self := 0x10000, target := 0x20000, spills := 0x30000, data := 0x40000, trace := 0x50000, mapping := 0x80000,
     pad := p }, g)

/-- What a sample gives: whether the input is in the contract, the arguments and the objects of the call, and the result
field and the written objects of L3 (none when `run` gives none). -/
structure Case where
  pre : Bool
  args : List Field
  objs : List Object
  expect : Option (Field × List Object)
  junk : BitVec 64
  /-- Arguments seven and eight, above the entry return word. -/
  stack : Option (BitVec 64 × BitVec 64) := none

/-- The stack argument object of a sampled Call8 entry. -/
def stackObject (c : Case) : Option Object :=
  c.stack.map fun (g, h) => ⟨rsp0 + 8, [⟨.W64, g⟩, ⟨.W64, h⟩], false⟩

/-- The bytes of a field, least significant first. -/
def fieldBytes (f : Field) : List UInt8 :=
  (List.range f.w.bytes).map fun i => UInt8.ofNat (f.v.toNat >>> (8 * i))

/-- The bytes of an object, in order. -/
def objBytes (o : Object) : List UInt8 := o.fields.flatMap fieldBytes

/-- The register value of an argument: the value in the low bits, `junk` above them. -/
def argReg (junk : BitVec 64) (f : Field) : UInt64 :=
  let lo := f.v.toNat
  let hi := (junk.toNat >>> f.w.bits) <<< f.w.bits
  UInt64.ofNat (if f.w.bits == 64 then lo else hi + lo)

/-- The entry state of a call of `fn` with the case `c`. -/
def startOf (fn : Fn) (c : Case) : MachineState :=
  let m : DataMem := (∅ : DataMem).storeBytes (rsp0 - BitVec.ofNat 64 fn.room) (List.replicate fn.room 0xCD)
  let m := m.storeBytes rsp0 (Lift.Shuffler.Test.Run.le64 ra0.toNat)
  let m := (stackObject c).map (fun o => m.storeBytes o.addr (objBytes o)) |>.getD m
  let m := c.objs.foldl (fun m o => m.storeBytes o.addr (objBytes o)) m
  let a (i : Nat) (d : UInt64) : UInt64 := (c.args[i]?.map (argReg c.junk)).getD d
  ⟨{ regs := { rax := 0xAAAAAAAAAAAAAAAA, rdi := a 0 0x5050505050505050, rsi := a 1 0x5151515151515151,
               rdx := a 2 0x5252525252525252, rcx := a 3 0x5353535353535353, r8 := a 4 0x5454545454545454,
               r9 := a 5 0x5555555555555555, rsp := UInt64.ofBitVec rsp0, rbx := 0x1111111111111111,
               rbp := 0x2222222222222222, r12 := 0x3333333333333333, r13 := 0x4444444444444444,
               r14 := 0x5555555555555555, r15 := 0x6666666666666666 },
     dmem := m }, fn.entry⟩

/-- The object `o` is in the memory `m`: its bytes are there. -/
def hasObj (m : DataMem) (o : Object) : Bool := m.loadBytes o.addr o.size == some (objBytes o)

private structure Span where
  object : Object
  index : Nat
  size : Nat

private def disjoint (a n b k : Nat) : Bool := a + n ≤ b || b + k ≤ a

/-- The finite entry conditions of `Fn.Entry` for the sampled stack and memory. An invalid entry cannot refute a call.
Read-only overlaps are allowed when their bytes agree; writable overlaps are not. -/
def admissionIssue (fn : Fn) (c : Case) : Option String := do
  if c.args.length > 6 then return "more than six arguments"
  if fn.room > rsp0.toNat then return "stack room wraps below zero"
  if fn.room % 8 != 0 then return "stack room is not a whole number of words"
  let spans := c.objs.zipIdx.map fun (o, i) => (⟨o, i, o.size⟩ : Span)
  if let some s := spans.find? (fun s => s.object.addr.toNat + s.size > 2 ^ 64) then
    return s!"entry object {s.index} wraps past 2^64"
  let stack := rsp0.toNat - fn.room
  if let some s := spans.find? (fun s => !disjoint s.object.addr.toNat s.size stack (fn.room + 8)) then
    return s!"entry object {s.index} overlaps the stack room or return word"
  if let some why := spans.findSome? (fun a => spans.findSome? fun b =>
      if a.index < b.index && (a.object.writable || b.object.writable) &&
          !disjoint a.object.addr.toNat a.size b.object.addr.toNat b.size then
        some s!"entry objects {a.index} and {b.index} overlap and one is writable"
      else none) then return why
  let readonlyOverlap := spans.any fun a => spans.any fun b =>
    a.index < b.index && !disjoint a.object.addr.toNat a.size b.object.addr.toNat b.size
  if readonlyOverlap then
    let m := (startOf fn c).data.dmem
    if let some i := c.objs.findIdx? (!hasObj m ·) then
      return s!"overlapping read-only entry object {i} has conflicting bytes"
  if let some stack := stackObject c then
    unless hasObj (startOf fn c).data.dmem stack do
      return "entry object conflicts with stack arguments"
  none

/-- The stack argument words obey the return frame outside writable objects. -/
def stackFrameIssue (c : Case) (m : DataMem) : Option String := do
  let some stack := stackObject c | none
  let bytes := objBytes stack
  if (bytes.zipIdx).any (fun (v, i) =>
      let b := stack.addr + BitVec.ofNat 64 i
      let writable := c.objs.any fun o => o.writable &&
        o.addr.toNat ≤ b.toNat && b.toNat < o.addr.toNat + o.size
      !writable && m.get? b != some v) then
    some "a stack argument outside writable objects is changed"
  else none

/-- Compute the model result only for an input in the contract with an admitted entry. -/
def withExpected (fn : Fn) (c : Case) (expected : Unit → Option (Field × List Object)) : Case :=
  if !c.pre || (admissionIssue fn c).isSome then c
  else { c with expect := expected () }

/-- `none` when the run of the case `c` returns as `post` says; else what differs. -/
def checkCase (fn : Fn) (fuel : Nat) (c : Case) : Option String :=
  match c.expect with
  | none => some "run of L3 gives none"
  | some (res, written) =>
    match (drive step (Int64.ofBitVec ra0) fuel 0 (startOf fn c) {}).1 with
    | .fault pc => some s!"fault at {hex pc.toBitVec.toNat}"
    | .fuel => some s!"no return in {fuel} steps"
    | .ret s =>
      let m := s.data.dmem
      let r : Field := ⟨fn.ret, s.data.regs.rax.toBitVec.setWidth fn.ret.bits⟩
      if s.data.regs.rsp != UInt64.ofBitVec (rsp0 + 8) then some "rsp at the return is not rsp + 8"
      else if calleeSaved s.data.regs != marks then some "a callee-saved register is changed"
      else if r != res then some s!"the result field is {r.v.toNat}, L3 gives {res.v.toNat}"
      else match (written.zipIdx.find? fun (o, _) => !hasObj m o) with
        | some (o, i) => some s!"written object {i} at {hex o.addr.toNat} does not have the contents of L3"
        | none => match stackFrameIssue c m with
          | some why => some why
          | none => match (c.objs.filter (!·.writable)).findIdx? (!hasObj m ·) with
            | some i => some s!"read-only object {i} is changed"
            | none => none

/-- The verdict of `n` samples from `seed`: `REFUTE pass <checked> <skipped>`, or `REFUTE real <index> <why>` for the first
admitted sample whose run differs. With no admitted sample it gives `REFUTE unknown 0 <skipped> <reason>`. -/
def verdict (fn : Fn) (n seed : Nat) (mk : Rng → Case) (fuel : Nat := 100000) : String := Id.run do
  let mut checked := 0
  let mut lastSkipped := "no samples requested"
  for i in List.range n do
    let c := mk (Rng.stream (Rng.ofSeed seed) i)
    if !c.pre then
      lastSkipped := "outside the contract"
      continue
    if let some why := admissionIssue fn c then
      lastSkipped := why
      continue
    checked := checked + 1
    if let some why := checkCase fn fuel c then return s!"REFUTE real {i} {why}"
  if checked == 0 then return s!"REFUTE unknown 0 {n} no admissible entry: {lastSkipped}"
  return s!"REFUTE pass {checked} {n - checked}"

end Skel.IntQ.Refute
