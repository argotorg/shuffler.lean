import Lift.Shuffler.Zig.Emission
import Coordinator.Dst.Rng

/-! Support of the held-out evaluation D15a (`docs/research/invariant-discovery-eval-20261119.md`). The discovery ladder needs,
for a fueled L3 site, a sampler of states (`Rng → σ`) and a `Repr` of the state (the search of D9 prints a state). The model
state `Lift.Shuffler.Zig.St` has neither, and `Skel/Discover` makes neither. This module gives both, from the types of the
fields only: it reads no loop and states no property of a loop.

- A scalar word is a value `0 .. 7`; an element of a vector of words is a value `0 .. 7` or `2^64 - 1` (1 draw in 8).
  Versions 1 and 2 of the sampler are kept below with the results that they gave.
- A `BitVec n` of another width is a value `0 .. 3`.
- A vector of 1024 elements has element `k` from stream `k`.
- The function `spills` is a constant function of one drawn byte.
- The list `trace` is empty.
Each field has its own stream. -/

namespace Skel.Eval.D15

open Coordinator.Dst (Rng)
open FlatShuffler (Word StackSlot maxStackSize)

/-- Version 1 of the word sampler. With it, a state of size `2^64 - 1` gave trace runs that did not end in the time limit
of the trace (120 s) in all 6 rounds of `surplusLoop` (mode a). -/
def wordV1 (g : Rng) : Word :=
  if ((g.stream 0).natIn 0 7).1 = 7 then BitVec.allOnes 64 else BitVec.ofNat 64 ((g.stream 1).natIn 0 7).1

/-- Version 2: a word is a value `0 .. 7`. With it, no element of `dest` is `2^64 - 1`, and each of the 200 trace runs of
`surplusLoop` (mode a) ended at its first visit. -/
def word (g : Rng) : Word := BitVec.ofNat 64 (g.natIn 0 7).1

/-- Version 3, used for the results of the report: a scalar word field is `word` (`0 .. 7`); an element of a vector of
words is `wordV1` (`0 .. 7`, or `2^64 - 1` in 1 draw of 8). -/
def elem (g : Rng) : Word := wordV1 g

def small (n : Nat) (g : Rng) : BitVec n := BitVec.ofNat n (g.natIn 0 3).1

def slot (g : Rng) : StackSlot := ⟨small 32 (g.stream 0), small 8 (g.stream 1), small 8 (g.stream 2)⟩

def vec {α : Type} (d : Rng → α) (g : Rng) : Vector α maxStackSize := Vector.ofFn fun k => d (g.stream k.val)

def st (g : Rng) : Lift.Shuffler.Zig.St :=
  { target := vec slot (g.stream 0), targetPad := vec (small 16) (g.stream 1), targetSize := word (g.stream 2),
    spills := let b := small 8 (g.stream 3); fun _ => b, maxSwapDepth := word (g.stream 4),
    maxDupDepth := word (g.stream 5), data := vec slot (g.stream 6), pad := vec (small 16) (g.stream 7),
    size := word (g.stream 8), trace := [], dest := vec elem (g.stream 9), pos := vec elem (g.stream 10),
    pend := word (g.stream 11), blockedOffset := word (g.stream 12), blockedExcess := word (g.stream 13) }

/-- The state of the site of `permuteLoop`: the emission state and a vector of words. -/
def stPerm (g : Rng) : Lift.Shuffler.Zig.St × Vector Word maxStackSize := (st (g.stream 0), vec elem (g.stream 1))

/-- The text of the state: the scalar fields, the size of the trace, and the first 8 elements of each vector (the spills
function has no text). -/
def text (s : Lift.Shuffler.Zig.St) : String :=
  let first {α : Type} [Repr α] (v : Vector α maxStackSize) : String := reprStr (v.toList.take 8)
  s!"⟨size {s.size.toNat}, targetSize {s.targetSize.toNat}, maxSwapDepth {s.maxSwapDepth.toNat}, " ++
  s!"maxDupDepth {s.maxDupDepth.toNat}, pend {s.pend.toNat}, blocked {s.blockedOffset.toNat}/{s.blockedExcess.toNat}, " ++
  s!"trace {s.trace.length}, data {first s.data}, dest {first s.dest}, pos {first s.pos}, target {first s.target}⟩"

instance : Repr Lift.Shuffler.Zig.St := ⟨fun s _ => .text (text s)⟩

end Skel.Eval.D15
