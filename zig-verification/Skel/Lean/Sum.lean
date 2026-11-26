import Skel.Lean.Refute
import Lift.Sem.Heap

/-! The samplers of the toySum refuter (`docs/one-way-lift-skeleton-plan-20261118.md`, section 5.3).
An input is an array of words in a heap, with the pointer and the count; a state adds the index and
the sum. This file does not name the constructors of the hand model: the generated refute files
pass them to `Skel.Refute`. All functions are pure. -/

namespace Skel.Sum
open Lift.Sem Coordinator.Dst Skel.Refute

/-- The length of the array of stream `g`: from 0 to 6. -/
def lengthOf (g : Rng) : Nat := ((Rng.stream g 0).natIn 0 6).1

/-- The address of the array of stream `g`: 8-aligned, below `2^43`. -/
def baseOf (g : Rng) : BitVec 64 := BitVec.ofNat 64 (8 * ((Rng.stream g 1).natIn 0 (2 ^ 40)).1)

/-- The word `k` of stream `g`: a small word, or one of the two values near `2^64`. -/
def wordAt (g : Rng) (k : Nat) : BitVec 64 :=
  ((Rng.stream g (2 + k)).pick (0 : BitVec 64)
    [1, 2, 3, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF]).1

/-- The heap of an array `xs` at `base` (read-only), and a writable object 64 bytes above it. The
array takes at most 48 bytes, so the two objects are apart. -/
def heapOf (base : BitVec 64) (xs : List (BitVec 64)) : Heap :=
  [Obj.words base false .W64 xs, Obj.words (base + 64) true .W64 [0]]

/-- The admitted inputs of stream `g`: an array `xs` of 0 to 6 words at an 8-aligned address `p`,
with `n = xs.length`, and the heap of the array. -/
def inputs (g : Rng) : List (BitVec 64) × Heap × UInt64 × UInt64 :=
  let len := lengthOf g
  let base := baseOf g
  let xs := (List.range len).map (wordAt g)
  (xs, heapOf base xs, UInt64.ofBitVec base, UInt64.ofNat len)

/-- The free states of stream `g`: the inputs of `inputs g`, an index `i` from `0` to `length + 3`,
and any sum `acc`. -/
def states (g : Rng) : List (BitVec 64) × Heap × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (xs, h, p, n) := inputs g
  let i := ((Rng.stream g 8).natIn 0 (xs.length + 3)).1
  let acc := ((Rng.stream g 9).nat (2 ^ 64)).1
  (xs, h, p, n, UInt64.ofNat i, UInt64.ofNat acc)

/-- The text of sample `index` of `seed`: `render` of the admitted or the free sample that
`sampleAt` gives. -/
def shown {σ R : Type} (render : σ → String) (admitted : Rng → σ × R) (free : Rng → σ)
    (seed index : Nat) : String :=
  match sampleAt admitted free seed index with
  | .admitted x _ => render x
  | .free x => render x

end Skel.Sum
