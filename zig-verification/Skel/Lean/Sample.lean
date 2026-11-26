import Lift.Sem.HeapWF
import Lift.Sem.HeapChain
import Lift.Sem.HeapDec
import Coordinator.Dst.Rng

/-! The sample library of the sampler (`docs/one-way-lift-g3-plan-20261118.md`, section 5, task G3-12a). It holds the parts
that the samplers of the toys share: the sample of a type (5.1 step 1), the binders of the grammar (5.1 step 2), the frame
words (5.1 step 3), the redraws and the check of a heap (5.1 step 4), the free-state parts (5.2) and the text of a sample.
All functions are pure. A draw of a generator `g` uses the streams `g.stream i`; a caller that uses one generator for two
draws passes two different streams. A heap that a sample gives is a `WFHeap`, so it is well formed. -/

namespace Skel.Sample
open Lift.Sem Coordinator.Dst

/-- The longest list of words of a sample. -/
def maxLen : Nat := 6

/-- The number of redraws of a sample whose draw fails its check. -/
def redraws : Nat := 8

/-- The sample of a type from one generator. -/
class Sample (α : Type) where
  draw : Rng → α

/-- A word: `0`, a small word, or one of the two values near `2^64`. -/
def word (g : Rng) : BitVec 64 :=
  (g.pick (0 : BitVec 64) [1, 2, 3, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF]).1

instance : Sample (BitVec 64) := ⟨word⟩

/-- A list of `0` to `maxLen` words: the length from stream `0`, the word `k` from stream `k + 1`. -/
instance : Sample (List (BitVec 64)) where
  draw g :=
    let n := ((g.stream 0).natIn 0 maxLen).1
    (List.range n).map fun k => word (g.stream (k + 1))

/-- A structure by fields: the first field from stream `0`, the second from stream `1`. -/
instance {α β : Type} [Sample α] [Sample β] : Sample (α × β) where
  draw g := (Sample.draw (g.stream 0), Sample.draw (g.stream 1))

/-- An address: 8-aligned, from `8` to `2^43 - 8`. -/
def addrOf (g : Rng) : BitVec 64 :=
  BitVec.ofNat 64 (8 * ((g.natIn 1 (2 ^ 40 - 1)).1))

/-- A random order of the slots `0 .. n - 1`: the slot `k` has the key of stream `k`, and the slots are sorted by key. -/
def slots (g : Rng) (n : Nat) : List Nat :=
  (((List.range n).map fun k => (k, ((g.stream k).nat (2 ^ 64)).1)).mergeSort fun a b => a.2 ≤ b.2).map (·.1)

/-- The addresses of `n` slots of `size` bytes from `base`, in the order of `slots g n`: the slot `s` is at
`base + size * s`. `none` when `base` is `0`, `size` is `0`, or the slots pass the top of the address space. -/
def slotAddrs (g : Rng) (base : BitVec 64) (size n : Nat) : Option (List (BitVec 64)) :=
  if base = 0 ∨ size = 0 ∨ base.toNat + size * n > 2 ^ 64 then none
  else some ((slots g n).map fun s => base + BitVec.ofNat 64 (size * s))

/-- The frame of the object range that starts at `lo`: the writable word `before` right before `lo`. No word follows the range:
the bytes after it are unmapped, so a read or a write past the last object is a fault (R-F). -/
def frame (lo before : BitVec 64) : Heap :=
  [Obj.words (lo - 8) true .W64 [before]]

/-- A heap that is well formed (`Heap.WF`). The samples give only these heaps. -/
abbrev WFHeap := {h : Heap // h.WF = true}

/-- The heap as a well formed heap, or `none` when it is not well formed. -/
def WFHeap.of? (h : Heap) : Option WFHeap :=
  if hw : h.WF = true then some ⟨h, hw⟩ else none

/-- The first draw that `attempt` accepts, for the generators `g.stream i` with `i = 0 .. redraws`. `none` when all of them
fail: the sample is skipped. -/
def admit {α : Type} (attempt : Rng → Option α) (g : Rng) : Option α :=
  (List.range (redraws + 1)).findSome? fun i => attempt (g.stream i)

/-- The decision of the array part of `SimArr`: the object of `xs` at `p` is in `h`, and its cells are the words of `xs`.
The count and the policy are not in this decision. The count is `xs.length` by construction, and `WFHeap` gives the policy. -/
def holdsArray (h : Heap) (p : BitVec 64) (xs : List (BitVec 64)) : Bool :=
  h.any fun o => decide (o.addr = p) && decide (o.cells = (Obj.words p false .W64 xs).cells)

/-- The heap of an array: the object of `xs` at `base` (writable as `writable` says), and the frame of the array. -/
def arrayHeap (writable : Bool) (base : BitVec 64) (xs : List (BitVec 64)) (before : BitVec 64) : Heap :=
  Obj.words base writable .W64 xs :: frame base before

/-- One draw of an array: `xs` (`0` to `maxLen` words) at an address `base` from `addrOf`, and the frame word from stream
`2`. `none` when the heap is not well formed. -/
def arrayAttempt (writable : Bool) (g : Rng) : Option (BitVec 64 × List (BitVec 64) × WFHeap) :=
  let xs : List (BitVec 64) := Sample.draw (g.stream 0)
  let base := addrOf (g.stream 1)
  (WFHeap.of? (arrayHeap writable base xs (word (g.stream 2)))).map fun h => (base, xs, h)

/-- The admitted array of stream `g` (`Sum`, `Find`, `Fill`): the address, the words and the heap. `none` when all redraws
fail. -/
def arraySample (g : Rng) (writable : Bool) : Option (BitVec 64 × List (BitVec 64) × WFHeap) :=
  admit (arrayAttempt writable) g

/-- The node objects of a list: node `k` is at `ps[k]`, with the value `vs[k]` at offset `0` and the address `ps[k + 1]` at
offset `8` (`0` for the last node). -/
private def nodesOf : List (BitVec 64) → List (BitVec 64) → Heap
  | v :: vs, p :: ps => Obj.words p false .W64 [v, ps.headD 0] :: nodesOf vs ps
  | _, _ => []

/-- The node objects of the values `vs` at the addresses `ps`. `none` when the lengths differ. -/
def nodes? (vs ps : List (BitVec 64)) : Option Heap :=
  if vs.length = ps.length then some (nodesOf vs ps) else none

/-- One draw of a chain (`Walk`): the values `vs` in 16-byte nodes at `slotAddrs` from `base`, and the frame of the nodes. The
result is the values, the node addresses in list order, and the heap. `none` when the heap is not well formed. -/
def chainAttempt (g : Rng) : Option (List (BitVec 64) × List (BitVec 64) × WFHeap) := do
  let vs : List (BitVec 64) := Sample.draw (g.stream 0)
  let base := addrOf (g.stream 1)
  let ps ← slotAddrs (g.stream 2) base 16 vs.length
  let objs ← nodes? vs ps
  let h ← WFHeap.of? (objs ++ frame base (word (g.stream 3)))
  pure (vs, ps, h)

/-- The admitted chain of stream `g` (`Walk`). `none` when all redraws fail. -/
def chainSample (g : Rng) : Option (List (BitVec 64) × List (BitVec 64) × WFHeap) :=
  admit chainAttempt g

/-- The kind of a free state (5.2), one of four equally likely: a counter out of range, one field or the memory from another
visit, an accumulator (a word), or the frame changed. -/
inductive FreeKind where
  | counter | fromVisit | word | frame
  deriving DecidableEq, Repr

/-- The kind of a free state of stream `g`. -/
def freeKind (g : Rng) : FreeKind :=
  match (g.natIn 0 3).1 with
  | 0 => .counter
  | 1 => .fromVisit
  | 2 => .word
  | _ => .frame

/-- A counter from `0` to `len + 3`: the counter out of range of 5.2 for a list of `len` words. -/
def counter (g : Rng) (len : Nat) : Nat := (g.natIn 0 (len + 3)).1

/-- A visit `k ≠ j` of `n` visits (`k` from `0` to `n - 1`), or `none` when there is no other visit. -/
def otherVisit (g : Rng) (n j : Nat) : Option Nat :=
  if n ≤ 1 then none else
    let k := (g.natIn 0 (n - 2)).1
    some (if k < j then k else k + 1)

/-- A free state with one field (or the memory) from another visit: `cur` with the field `get` of the visit `k ≠ j` put in by
`set`. The visits are the states of a run from the head; the first is the input and the last is the state after the run.
`none` when there is no other visit. -/
def fromVisit {σ τ : Type} (g : Rng) (visits : List σ) (j : Nat) (cur : σ) (get : σ → τ) (set : σ → τ → σ) : Option σ :=
  (otherVisit g visits.length j).bind fun k => (visits[k]?).map fun v => set cur (get v)

/-- A pointer field: the pointer of one visit (for a walk, the node addresses and `0`). It is never a random word. `none` when
there is no visit. -/
def pointer (g : Rng) (ptrs : List (BitVec 64)) : Option (BitVec 64) :=
  ptrs[(g.nat ptrs.length).1]?

/-- A member of `xs`, or `other`: one draw in two is a member of `xs` at a random position, else `other`. An empty `xs` gives
`other`. -/
def memberOr {α : Type} (g : Rng) (xs : List α) (other : α) : α :=
  if ((g.stream 0).natIn 0 1).1 = 1 then xs.getD ((g.stream 1).natIn 0 (xs.length - 1)).1 other else other

/-- The first word of an object, raised by one. `none` when the object has no cell. -/
def bumpObj (o : Obj) : Option Obj :=
  match o.cells with
  | c :: cs => (c.get .W64).map fun (v : BitVec 64) => { o with cells := ⟨.W64, v + 1⟩ :: cs }
  | [] => none

/-- A frame with one object (chosen by `g`) bumped by `bumpObj`. `none` when the frame is empty. -/
def bumpFrame (g : Rng) (fr : Heap) : Option Heap :=
  let k := (g.natIn 0 (fr.length - 1)).1
  (fr[k]?.bind bumpObj).map fun o => fr.set k o

/-- The text of sample `index` of `seed`: the admitted sample at an even index (`skipped` when it is skipped), the free state
at an odd index. The generator is `Rng.stream (Rng.ofSeed seed) index`. -/
def shownAt {α : Type} (render : α → String) (admitted : Rng → Option α) (free : Rng → α) (seed index : Nat) : String :=
  let g := Rng.stream (Rng.ofSeed seed) index
  if index % 2 = 0 then
    match admitted g with
    | some x => render x
    | none => "skipped"
  else render (free g)

end Skel.Sample
