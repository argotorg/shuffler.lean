import Skel.Lean.Sum
import Lift.Spike.Sum

/-! Tests of `Skel.Sum` (`Skel/Lean/Sum.lean`) against the hand model `Lift.Spike.Sum`, for the
seeds 0 to 49. The tests are `#guard` commands, so they run when the module is built. -/

namespace Skel.Test.LeanSum

open Lift.Sem Coordinator.Dst Skel.Sum

/-- The seeds of the tests. -/
def seeds : List Nat := List.range 50

/-- The value of an `.ok`; else `none`. -/
def okVal {α : Type} : Res α → Option α
  | .ok v => some v
  | _ => none

def noRun (f : Empty) : Empty.elim f → Res (Empty.elim f) := f.elim

/-- Some object of `h` is the array `xs` at `p`: its address is `p`, it has one cell per word, and
each cell holds the word. -/
def arrayIn (h : Heap) (p : BitVec 64) (xs : List (BitVec 64)) : Bool :=
  h.any fun o => o.addr == p && o.cells.length == xs.length &&
    (List.range xs.length).all fun i => o.get (p + BitVec.ofNat 64 (8 * i)) .W64 == xs[i]?

/-- Each object other than the array at `p` (`len` words) is apart from it. -/
def otherApart (h : Heap) (p : BitVec 64) (len : Nat) : Bool :=
  h.all fun o => o.addr == p || decide (o.addr.toNat + o.size ≤ p.toNat) ||
    decide (p.toNat + 8 * len ≤ o.addr.toNat)

/-- The input as data that can be compared. -/
def describe (x : List (BitVec 64) × Heap × UInt64 × UInt64) :
    List (BitVec 64) × List (Nat × Bool × List (BitVec 64)) × UInt64 × UInt64 :=
  (x.1, x.2.1.map (fun o => (o.addr.toNat, o.writable, o.cells.filterMap (fun c => c.get .W64))),
    x.2.2.1, x.2.2.2)

/-- The state as data that can be compared. -/
def describeState (x : List (BitVec 64) × Heap × UInt64 × UInt64 × UInt64 × UInt64) :
    (List (BitVec 64) × List (Nat × Bool × List (BitVec 64)) × UInt64 × UInt64) × UInt64 × UInt64 :=
  (describe (x.1, x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)

/-- The input of seed `s`: the array is in the heap, `n` is its length, the address is 8-aligned,
one other object is apart from the array, and the hand loop from `entry` returns the sum. -/
def inputOk (s : Nat) : Bool :=
  let (xs, h, p, n) := inputs (Rng.ofSeed s)
  arrayIn h p.toBitVec xs && n.toNat == xs.length && p.toNat % 8 == 0 &&
    h.length == 2 && otherApart h p.toBitVec xs.length &&
    okVal (Lift.Spike.Sum.blocksP.run noRun (2 * xs.length + 8) .entry
      (Lift.Spike.Sum.init (⟨h, p, n⟩ : Lift.Spike.Sum.In2p))) == some (UInt64.ofBitVec xs.sum)

/-- The state of seed `s` at the loop head: the input holds as in `inputOk` (without the loop), and
`i` is in `0 .. length + 3`. -/
def stateOk (s : Nat) : Bool :=
  let (xs, h, p, n, i, _) := states (Rng.ofSeed s)
  arrayIn h p.toBitVec xs && n.toNat == xs.length && p.toNat % 8 == 0 &&
    h.length == 2 && otherApart h p.toBitVec xs.length && decide (i.toNat ≤ xs.length + 3)

/-! ### The inputs -/

#guard seeds.all inputOk

-- The samples are not all the same: at least 5 different lengths in the 50 seeds.
#guard ((seeds.map fun s => (inputs (Rng.ofSeed s)).1.length).eraseDups).length ≥ 5
-- The empty list occurs for some seed, and the length 6 (the upper bound) occurs too.
#guard seeds.any fun s => (inputs (Rng.ofSeed s)).1.isEmpty
#guard seeds.any fun s => (inputs (Rng.ofSeed s)).1.length == 6
-- The words near 2^64 occur, so that the sums wrap.
#guard (seeds.flatMap fun s => (inputs (Rng.ofSeed s)).1).contains 0xFFFFFFFFFFFFFFFF
#guard (seeds.flatMap fun s => (inputs (Rng.ofSeed s)).1).contains 0xFFFFFFFFFFFFFFFE

-- The same seed gives the same sample.
#guard seeds.all fun s => describe (inputs (Rng.ofSeed s)) == describe (inputs (Rng.ofSeed s))

/-! ### The states -/

#guard seeds.all stateOk

-- The input part of a state is the input of the same seed.
#guard seeds.all fun s =>
  let x := states (Rng.ofSeed s)
  describe (x.1, x.2.1, x.2.2.1, x.2.2.2.1) == describe (inputs (Rng.ofSeed s))
-- The same seed gives the same state.
#guard seeds.all fun s =>
  describeState (states (Rng.ofSeed s)) == describeState (states (Rng.ofSeed s))

/-! ### `shown` -/

-- Even index: the admitted sample; odd index: the free sample.
#guard shown (fun (x : Nat) => toString x) (fun _ => (7, ())) (fun _ => 8) 1 0 == "7"
#guard shown (fun (x : Nat) => toString x) (fun _ => (7, ())) (fun _ => 8) 1 1 == "8"

end Skel.Test.LeanSum
