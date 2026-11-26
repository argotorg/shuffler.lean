module

public import Lift.Shuffler.Zig.Planner
public meta import Lift.Shuffler.Zig.Planner
public import Lift.Shuffler.Ext.FlatPlan
public meta import Lift.Shuffler.Ext.FlatPlan
public import Lean.Data.Json
public meta import Lean.Data.Json

@[expose] public section

/-! Tests of the planner of the Zig flat model (`Lift.Shuffler.Zig.Planner`, K3h): `Planner`, `PSt`,
`copyFrom` with the pads, `ctorP`, `runLoop` and `plannerRun` (the Zig `Planner.run`,
`Lift/LLVM/data/shuffler/src/shuffler.zig` 1131-1200).

1. Hand-computed cases. Each expected value is computed from the Zig source (`Planner.run` 1131-1199,
   `Emission` 478-978, `MappingBuilder` 354-448). The pads: a source slot keeps its padding when it
   moves (`Stack.swap` Z:253-255) and when it is copied (`Stack.dup` Z:270); a slot that `produce`
   pushes has the padding of the target word (Z:630, 634).
2. The model against the external `plannerRun` on seeded inputs at the reach 16, padding dropped, and
   properties of the padding of the output.
3. The model against the native vectors of the compiled Zig `shuffle`
   (`Lift/Shuffler/Test/data/native-*.jsonl`) where one plan runs. Each `#guard` and `#eval` runs the
   compiled code at elaboration. -/

namespace Lift.Shuffler.Test.Planner

open Lift.Shuffler.Zig
open FlatShuffler (Word StackSlot maxStackSize Push Load Dup Swap)
open FlatShuffler.Flat (NONE Status RunU Mapping Uninit Locals ResolveU get)

/-! ### Builders -/

/-- A vector of `maxStackSize` elements: the list, then `d`. -/
def vecD {α : Type} (d : α) (l : List α) : Vector α maxStackSize :=
  Vector.ofFn fun i => l.getD i.val d

/-- A variable (kind value, opcode 1). -/
def v (k : Nat) : StackSlot := ⟨BitVec.ofNat 32 k, 0, 1⟩

/-- A literal (kind value, opcode `Const`). -/
def lit (k : Nat) : StackSlot := ⟨BitVec.ofNat 32 k, 0, 0⟩

/-- A function return label (kind 3). -/
def lbl : StackSlot := ⟨7, 3, 1⟩

/-- The junk slot (the wildcard of a target). -/
def jk : StackSlot := StackSlot.junk

/-- A planner over the slots (with their padding). -/
def mkPl (src tgt : List (StackSlot × BitVec 16)) (allowed : Bool := true) (reach : Word := 16) :
    Planner where
  source := vecD jk (src.map (·.1))
  sourcePad := vecD 0 (src.map (·.2))
  sourceSize := BitVec.ofNat 64 src.length
  target := vecD jk (tgt.map (·.1))
  targetPad := vecD 0 (tgt.map (·.2))
  targetSize := BitVec.ofNat 64 tgt.length
  allowed := allowed
  reach := reach

def zW : Vector Word maxStackSize := Vector.replicate maxStackSize 0

/-- The content of the scratch arrays: all zero. -/
def us0 : Nat → RunU := fun _ =>
  { mapping := ⟨zW, zW⟩, u := ⟨zW, zW, 0, 0⟩, l := ⟨zW, zW, zW⟩,
    r := ⟨Vector.replicate maxStackSize 0, zW⟩ }

/-- Another content of the scratch arrays: other values, and another one for each attempt. -/
def usJ : Nat → RunU := fun k =>
  let w : Vector Word maxStackSize := Vector.replicate maxStackSize (BitVec.ofNat 64 (7 + k))
  { mapping := ⟨w, w⟩, u := ⟨w, w, 9, 11⟩, l := ⟨w, w, w⟩,
    r := ⟨Vector.replicate maxStackSize (BitVec.ofNat 8 (3 + k)), w⟩ }

/-- The sentinel of the caller's buffers: `data`, its padding and `sources` that a run does not write
keep it; `saw` starts true, and the run sets it (Z:1141). -/
def s0 : PSt where
  spills := fun _ => 0
  dropped := Vector.replicate maxStackSize 0
  saw := true
  data := Vector.replicate maxStackSize (v 99)
  pad := Vector.replicate maxStackSize 0x5A5A
  trace := []
  sources := Vector.replicate maxStackSize 0xDEAD

def run (pl : Planner) (take : Bool := false) (spills : BitVec 32 → BitVec 8 := fun _ => 0)
    (us : Nat → RunU := us0) : Exit Status × PSt :=
  plannerRun pl take { s0 with spills } us

/-- The first `k` words of the data with their padding. -/
def outData (s : PSt) (k : Nat) : List (StackSlot × BitVec 16) :=
  (List.range k).map fun j => (get s.data (BitVec.ofNat 64 j), get s.pad (BitVec.ofNat 64 j))

def outSources (s : PSt) (k : Nat) : List Word :=
  (List.range k).map fun j => get s.sources (BitVec.ofNat 64 j)

/-- What a hand case compares: the control, the first `k` words with padding, the trace, the first
`k` sources and `saw`. -/
def view (r : Exit Status × PSt) (k : Nat) :=
  (r.1, outData r.2 k, r.2.trace, outSources r.2 k, r.2.saw)

def sw (d : BitVec 8) : OpP := ⟨⟨Swap, d, jk⟩, 0⟩
def dp (d : BitVec 8) : OpP := ⟨⟨Dup, d, jk⟩, 0⟩
def popP : OpP := ⟨FlatShuffler.Op.pop, 0⟩
def pushP (s : StackSlot) (p : BitVec 16) : OpP := ⟨FlatShuffler.Op.push s, p⟩

/-! ### `copyFrom` (Z:1171) -/

-- The loop writes the data and its padding below the source size; the rest keeps its content.
#guard
  let pl := mkPl [(v 1, 0xA1), (v 2, 0xA2), (v 3, 0xA3)] []
  let r := copyFrom pl 0 s0.data s0.pad
  (List.range 5).map (fun j => (get r.1 (BitVec.ofNat 64 j), get r.2 (BitVec.ofNat 64 j))) ==
    [(v 1, 0xA1), (v 2, 0xA2), (v 3, 0xA3), (v 99, 0x5A5A), (v 99, 0x5A5A)]

-- From `i = 2` on: the offsets 0 and 1 keep their content.
#guard
  let pl := mkPl [(v 1, 0xA1), (v 2, 0xA2), (v 3, 0xA3)] []
  let r := copyFrom pl 2 s0.data s0.pad
  (List.range 4).map (fun j => (get r.1 (BitVec.ofNat 64 j), get r.2 (BitVec.ofNat 64 j))) ==
    [(v 99, 0x5A5A), (v 99, 0x5A5A), (v 3, 0xA3), (v 99, 0x5A5A)]

-- An empty source writes nothing.
#guard
  let r := copyFrom (mkPl [] []) 0 s0.data s0.pad
  r.1 == s0.data && r.2 == s0.pad

/-! ### `ctorP` (`Emission.init`, Z:500-524) -/

-- The planned mapping: source 0 to target 1, source 1 to target 0. The sizes: 2 source, 3 target.
-- The arrays of the scratch have 7 (`dest`, `pos`) and the blocked members 9 and 11.
def planned2 : Mapping := ⟨vecD NONE [1, 0], vecD NONE [1, 0]⟩
def u7 : Uninit := ⟨Vector.replicate maxStackSize 7, Vector.replicate maxStackSize 7, 9, 11⟩

def ct (reach : Word) : St :=
  ctorP (mkPl [(v 1, 0xA1), (v 2, 0xA2)] [(v 2, 0xB2), (v 1, 0xB1), (v 3, 0xB3)] true reach)
    (vecD (v 5) [v 1, v 2]) (vecD 0x77 [0xA1, 0xA2]) planned2 (fun _ => 1) u7

-- The reach is `max_swap_depth`, one less is `max_dup_depth` (Z:513-514).
#guard (ct 16).maxSwapDepth == 16 && (ct 16).maxDupDepth == 15
#guard (ct 2).maxSwapDepth == 2 && (ct 2).maxDupDepth == 1
-- The reach 0 wraps (`max_swap_depth - 1`).
#guard (ct 0).maxSwapDepth == 0 && (ct 0).maxDupDepth == 0xFFFFFFFFFFFFFFFF
-- The stack is the source: the size, the data and the padding; the trace is empty.
#guard (ct 16).size == 2 && (ct 16).trace == [] && (ct 16).data == vecD (v 5) [v 1, v 2] &&
  (ct 16).pad == vecD 0x77 [0xA1, 0xA2]
-- The target with its padding, and the spills.
#guard (ct 16).targetSize == 3 && (ct 16).target == vecD jk [v 2, v 1, v 3] &&
  (ct 16).targetPad == vecD 0 [0xB2, 0xB1, 0xB3] && (ct 16).spills 5 == 1
-- The mapping: the entries of `planned` below the sizes (dest below 2, pos below 3: `pos[2]` is
-- none in `planned`), the scratch content above (7).
#guard (ct 16).dest == (vecD 7 [1, 0]) && (ct 16).pos == (vecD 7 [1, 0, NONE])
-- `pending_generations`: the target offsets without a position (Z:521-523): offset 2 only.
#guard (ct 16).pend == 1
-- The blocked members are not initialised (Z:455): the scratch content.
#guard (ct 16).blockedOffset == 9 && (ct 16).blockedExcess == 11

/-! ### `plannerRun`: hand-computed cases -/

-- Empty stacks: Done, nothing written, `saw` false (Z:1141).
#guard view (run (mkPl [] [])) 0 == (.done, [], [], [], false)
#guard (run (mkPl [] [])).2.data == s0.data && (run (mkPl [] [])).2.pad == s0.pad &&
  (run (mkPl [] [])).2.sources == s0.sources

-- The target is the source: no operation. The output has the source padding, not the target one.
#guard view (run (mkPl [(v 1, 0xA1), (v 2, 0xA2), (v 3, 0xA3)] [(v 1, 0xB1), (v 2, 0xB2), (v 3, 0xB3)])) 4 ==
  (.done, [(v 1, 0xA1), (v 2, 0xA2), (v 3, 0xA3), (v 99, 0x5A5A)], [], [0, 1, 2, 0xDEAD], false)

-- One swap: reversal of three. In place: offset 1. Closest copies: 0 to 2, 2 to 0. One swap of
-- depth 2; the padding moves with the slots (Z:253-255); the op has the padding 0.
#guard view (run (mkPl [(v 1, 0xA1), (v 2, 0xA2), (v 3, 0xA3)] [(v 3, 0xB3), (v 2, 0xB2), (v 1, 0xB1)])) 3 ==
  (.done, [(v 3, 0xA3), (v 2, 0xA2), (v 1, 0xA1)], [sw 2], [2, 1, 0], false)

-- A dup: the source slot is in place; the second target slot has no source (the slot is mapped
-- once). The generation is a dup of depth 1; the copy has the padding of the source slot (Z:270),
-- not the padding 0xB2 of the target word.
#guard view (run (mkPl [(v 1, 0xA1)] [(v 1, 0xB1), (v 1, 0xB2)])) 2 ==
  (.done, [(v 1, 0xA1), (v 1, 0xA1)], [dp 1], [0, NONE], false)

-- A pop: the surplus top is popped (`removeSurplus`, Z:741-); the data above the size keeps the popped slot.
#guard view (run (mkPl [(v 1, 0xA1), (v 2, 0xA2)] [(v 1, 0xB1)])) 2 ==
  (.done, [(v 1, 0xA1), (v 2, 0xA2)], [popP], [0, 0xDEAD], false)

-- A wildcard target slot: the source slot 0 is kept in place by `keepWildcardSlots` (Z:425).
#guard view (run (mkPl [(v 1, 0xA1), (v 2, 0xA2)] [(jk, 0xB0), (v 2, 0xB2)])) 2 ==
  (.done, [(v 1, 0xA1), (v 2, 0xA2)], [], [0, 1], false)
#guard view (run (mkPl [(v 1, 0xA1), (v 2, 0xA2)] [(jk, 0xB0), (v 2, 0xB2)]) true) 2 ==
  (.done, [(v 1, 0xA1), (v 2, 0xA2)], [], [0, 1], false)

-- A wildcard slot copy (Z:406-423): target `[junk, v1]` and source `[v1]`. The only copy of `v1` is
-- in a wildcard slot, so `saw_wildcard_copy` is set. Leave (`take` false): the copy is not taken;
-- the junk slot keeps source 0; the second target slot is a dup (depth 1, padding of the source).
#guard view (run (mkPl [(v 1, 0xA1)] [(jk, 0xB0), (v 1, 0xB1)]) false) 2 ==
  (.done, [(v 1, 0xA1), (v 1, 0xA1)], [dp 1], [0, NONE], true)
-- Take: source 0 goes to target 1, and target 0 has no source. `produce` pushes the junk slot with
-- the padding of the target word (Z:630); the swap of depth 1 (Z:657-659) moves the paddings.
#guard view (run (mkPl [(v 1, 0xA1)] [(jk, 0xB0), (v 1, 0xB1)]) true) 2 ==
  (.done, [(jk, 0xB0), (v 1, 0xA1)], [pushP jk 0xB0, sw 1], [NONE, 0], true)

-- A spilled target slot: the source slot is surplus (popped), the target slot is reloaded from
-- its spill with the padding of the target word (Z:634). The spill is a Load (kind 4).
#guard view (run (mkPl [(v 1, 0xA1)] [(v 2, 0xB2)]) false (fun i => if i == 2 then 1 else 0)) 1 ==
  (.done, [(v 2, 0xB2)], [popP, pushP (v 2) 0xB2], [NONE], false)

-- A literal that is not in the source is pushed with the padding of the target word (Z:634).
#guard view (run (mkPl [] [(lit 5, 0xB5)])) 1 ==
  (.done, [(lit 5, 0xB5)], [pushP (lit 5) 0xB5], [NONE], false)

-- The scratch content does not change a result.
#guard view (run (mkPl [(v 1, 0xA1), (v 2, 0xA2), (v 3, 0xA3)] [(v 3, 0xB3), (v 2, 0xB2), (v 1, 0xB1)]) false
    (fun _ => 0) usJ) 3 ==
  (.done, [(v 3, 0xA3), (v 2, 0xA2), (v 1, 0xA1)], [sw 2], [2, 1, 0], false)
#guard view (run (mkPl [(v 1, 0xA1)] [(jk, 0xB0), (v 1, 0xB1)]) true (fun _ => 0) usJ) 2 ==
  (.done, [(jk, 0xB0), (v 1, 0xA1)], [pushP jk 0xB0, sw 1], [NONE, 0], true)

-- An assertion exit: the target slot `v2` is not on the stack, not generatable and not spilled
-- (Z:1142-1150). `saw` is false, nothing else is written.
#guard view (run (mkPl [(v 1, 0xA1)] [(v 2, 0xB2)])) 1 ==
  (.assertionExit, [(v 99, 0x5A5A)], [], [0xDEAD], false)
-- A return label in the target that the source does not have: the same check.
#guard (run (mkPl [(v 1, 0xA1)] [(lbl, 0xB2)])).1 == .assertionExit
#guard (run (mkPl [(v 1, 0xA1)] [(lbl, 0xB2)])).2.dropped == s0.dropped

/-- Four variables and the reversal with the two middle ones in place: the first and last swap places
(depth 3). With the reach 2 a swap has the depth 2 at most and a dup 1: the first attempt is Blocked.
Each slot is a variable that is not spilled, and the target slots are not junk, so with no spilling
each class is `none` (Z:1040-1062) and `resolve` finds no victim (Z:1117): Blocked. -/
def deep4 (allowed : Bool) : Planner :=
  mkPl [(v 1, 0xA1), (v 2, 0xA2), (v 3, 0xA3), (v 4, 0xA4)]
    [(v 4, 0xB4), (v 2, 0xB2), (v 3, 0xB3), (v 1, 0xB1)] allowed 2

-- Blocked: no spill, no drop (Z:1117), `saw` false.
#guard (run (deep4 false)).1 == .blocked
#guard (run (deep4 false)).2.dropped == s0.dropped
#guard (run (deep4 false)).2.saw == false
#guard (List.range 8).all fun i => (run (deep4 false)).2.spills (BitVec.ofNat 32 i) == 0
-- The same input at the reach 3 (swap depth 3): Done, one swap of depth 3, no drop.
#guard view (run { deep4 false with reach := 3 }) 4 ==
  (.done, [(v 4, 0xA4), (v 2, 0xA2), (v 3, 0xA3), (v 1, 0xA1)], [sw 3], [3, 1, 2, 0], false)
-- With spilling the attempt after a block drops one slot and spills its variable: Done, exactly
-- one dropped slot, and its variable is the one spilled.
#guard
  let r := run (deep4 true)
  let dropped := (List.range 4).filter fun i => get r.2.dropped (BitVec.ofNat 64 i) != 0
  let spilled := (List.range 8).filter fun i => r.2.spills (BitVec.ofNat 32 i) != 0
  r.1 == .done && dropped.length == 1 && spilled.length == 1 &&
    dropped.map (· + 1) == spilled
-- The final stack of that run is the target, and each output slot has the padding of its source
-- slot, except the reloaded one, which has the padding of its target word (Z:634).
#guard
  let r := run (deep4 true)
  (outData r.2 4).map (·.1) == [v 4, v 2, v 3, v 1]

/-! ### Equality with the external model at the reach 16, padding dropped -/

/-- A hash of the seed and an index (the finaliser of splitmix64). -/
def mix (x : UInt64) : UInt64 :=
  let z := x + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- A number below `n`, a function of the seed and the index `i`. -/
def rnd (seed i n : Nat) : Nat := (mix (UInt64.ofNat (seed * 4096 + i))).toNat % n

/-- The slots of the random inputs: variables 1 to 4, two literals, a return label, a junk slot. -/
def palette : Nat → StackSlot
  | 0 => v 1 | 1 => v 2 | 2 => v 3 | 3 => v 4 | 4 => lit 3 | 5 => lit 4 | 6 => lbl | _ => jk

/-- A random input. The source padding of offset `i` is `0x100 + i` and the target padding of offset
`k` is `0x200 + k`, so that a padding names the word that it came from. The class is `seed % 4`:
0 small stacks, with target slots from the source, literals and junk; 1 the same with a variable
that the source does not have (assertion exits); 2 deep stacks of 19 to 22 distinct variables with a
near reversal as target (Blocked without spilling, and with no spilled variable); 3 stacks of up to 14 slots of the variables 1
to 3 (copies, wildcard slots). `take`, `allowed` and the spill bytes are random. -/
structure Case where
  src : List (StackSlot × BitVec 16)
  tgt : List (StackSlot × BitVec 16)
  allowed : Bool
  take : Bool
  spills : BitVec 32 → BitVec 8

def genCase (seed : Nat) : Case :=
  let cls := seed % 4
  let ns :=
    if cls == 2 then 19 + rnd seed 0 4 else if cls == 3 then rnd seed 0 15 else rnd seed 0 9
  let nt :=
    if cls == 2 then ns else if cls == 3 then rnd seed 1 15 else rnd seed 1 9
  let srcSlot (i : Nat) : StackSlot :=
    if cls == 2 then v (i + 1)
    else if cls == 3 then palette (rnd seed (100 + i) 3)
    else palette (rnd seed (100 + i) 8)
  let src := (List.range ns).map fun i => (srcSlot i, BitVec.ofNat 16 (0x100 + i))
  -- the near reversal: the reverse of the source with three random swaps
  let rev := (src.map (·.1)).reverse
  let swapped := (List.range 3).foldl (fun (l : List StackSlot) k =>
    let a := rnd seed (200 + 2 * k) (max l.length 1)
    let b := rnd seed (201 + 2 * k) (max l.length 1)
    l.mapIdx fun i x => if i == a then l.getD b x else if i == b then l.getD a x else x) rev
  let tgtSlot (k : Nat) : StackSlot :=
    if cls == 2 then swapped.getD k jk
    else
      let r := rnd seed (300 + k) 10
      if r == 0 then jk
      else if r == 1 then lit (rnd seed (350 + k) 3)
      else if (r == 2 || r == 3) && cls == 1 then v 9
      else if src.isEmpty then jk
      else (src.getD (rnd seed (400 + k) src.length) (jk, 0)).1
  let tgt := (List.range nt).map fun k => (tgtSlot k, BitVec.ofNat 16 (0x200 + k))
  { src, tgt, allowed := rnd seed 2 2 == 1, take := rnd seed 3 2 == 1,
    spills := fun i =>
      if cls == 2 && rnd seed 4 2 == 0 then 0 else if rnd seed (500 + i.toNat) 6 == 0 then 1 else 0 }

def Case.planner (c : Case) : Planner := mkPl c.src c.tgt c.allowed 16

def Case.run (c : Case) (us : Nat → RunU := us0) : Exit Status × PSt :=
  Test.Planner.run c.planner c.take c.spills us

/-- The external planner of a case: written out here, not through `Planner.toExt`. -/
def Case.extPlanner (c : Case) : FlatShuffler.Flat.Planner where
  source := vecD jk (c.src.map (·.1))
  sourceSize := BitVec.ofNat 64 c.src.length
  target := vecD jk (c.tgt.map (·.1))
  targetSize := BitVec.ofNat 64 c.tgt.length
  allowed := c.allowed

def Case.extRun (c : Case) : FlatShuffler.Flat.ExecutionOutcome Status FlatShuffler.Flat.PSt :=
  FlatShuffler.Flat.plannerRun c.extPlanner c.take
    { spills := c.spills, dropped := s0.dropped, saw := true, data := s0.data, trace := [],
      sources := s0.sources } us0

/-- The control of the Zig model as an external control; `outOfFuel` has none. -/
def ctlE {α : Type} : Exit α → Option (FlatShuffler.Flat.ExecutionControl α)
  | .returned a => some (.returned a)
  | .assertionExit => some .assertionExit
  | .outOfFuel => none

def spillBytes (sp : BitVec 32 → BitVec 8) : List (BitVec 8) :=
  (List.range 16).map fun i => sp (BitVec.ofNat 32 i)

/-- The Zig result and the external result have the same control, spills, dropped bytes, `saw`,
data, trace (the operations without padding) and sources. -/
def agree (c : Case) : Bool :=
  let z := c.run
  let e := c.extRun
  ctlE z.1 == some e.1 && spillBytes z.2.spills == spillBytes e.2.spills &&
    z.2.dropped == e.2.dropped && z.2.saw == e.2.saw && z.2.data == e.2.data &&
    z.2.trace.map (·.op) == e.2.trace && z.2.sources == e.2.sources

def seeds : List Nat := List.range 300

#guard seeds.all fun s => agree (genCase s)

/-- Count of the seeds with the control `k`. -/
def count (k : Exit Status) : Nat := (seeds.filter fun s => (genCase s).run.1 == k).length

#eval s!"done {count .done}, blocked {count .blocked}, assertion {count .assertionExit}"
#guard count .done ≥ 60
#guard count .blocked ≥ 10
#guard count .assertionExit ≥ 20
#guard count .outOfFuel == 0
-- The runs with a wildcard copy (`saw`), and with a spill.
#eval s!"saw {(seeds.filter fun s => (genCase s).run.2.saw).length}, \
  new spills {(seeds.filter fun s => let c := genCase s; c.run.1 == .done && (spillBytes c.run.2.spills != spillBytes c.spills)).length}"
#guard (seeds.filter fun s => (genCase s).run.2.saw).length ≥ 10
#guard (seeds.filter fun s =>
  let c := genCase s
  c.run.1 == .done && (spillBytes c.run.2.spills != spillBytes c.spills)).length ≥ 5

-- The scratch content does not change the result (the external model gets arbitrary content too).
#guard seeds.all fun s =>
  let c := genCase s
  let a := c.run
  let b := c.run usJ
  a.1 == b.1 && a.2.data == b.2.data && a.2.pad == b.2.pad && a.2.trace == b.2.trace &&
    a.2.sources == b.2.sources && a.2.dropped == b.2.dropped && a.2.saw == b.2.saw &&
    spillBytes a.2.spills == spillBytes b.2.spills

/-! ### The padding of the output -/

/-- The slots `a` and `b` are equal without padding. -/
def eqS (a b : StackSlot) : Bool := a == b

/-- P0: in a Done run each output slot below the target size is the target slot, where the target
slot is not a wildcard. -/
def p0 (c : Case) : Bool :=
  let r := c.run
  r.1 != .done || (List.range c.tgt.length).all fun j =>
    let t := (c.tgt.getD j (jk, 0)).1
    t == jk || get r.2.data (BitVec.ofNat 64 j) == t

#guard seeds.all fun s => p0 (genCase s)

/-- P1: in a Done run the padding of each output slot is the padding of a source slot with the same
word, or of a target slot with the same word (a pushed word, Z:630, 634). A padding comes only from
a word on the stack or a pushed target word, and a swap and a dup move the padding with the word. -/
def p1 (c : Case) : Bool :=
  let r := c.run
  r.1 != .done || (List.range c.tgt.length).all fun j =>
    let w := get r.2.data (BitVec.ofNat 64 j)
    let p := get r.2.pad (BitVec.ofNat 64 j)
    c.src.any (fun (s, sp) => s == w && sp == p) || c.tgt.any (fun (t, tp) => t == w && tp == p)

#guard seeds.all fun s => p1 (genCase s)

/-- P2: in a Done run, a variable that is not spilled at the end and has one copy in the source is
never pushed or copied: if it is bound for the target offset `j` in the plan, the output slot `j` has
its source padding. -/
def p2Offsets (c : Case) : List Nat :=
  let r := c.run
  if r.1 != .done then [] else
  (List.range c.tgt.length).filter fun j =>
    let src := get r.2.sources (BitVec.ofNat 64 j)
    src != NONE &&
      let s := (c.src.getD src.toNat (jk, 0)).1
      FlatShuffler.Flat.isVariable s && !FlatShuffler.Flat.spillIsSpilled r.2.spills s &&
        (c.src.filter fun (x, _) => x == s).length == 1

def p2 (c : Case) : Bool :=
  let r := c.run
  (p2Offsets c).all fun j =>
    get r.2.pad (BitVec.ofNat 64 j) == (c.src.getD (get r.2.sources (BitVec.ofNat 64 j)).toNat (jk, 0)).2

#guard seeds.all fun s => p2 (genCase s)
#eval s!"P2 offsets {(seeds.map fun s => (p2Offsets (genCase s)).length).foldl (· + ·) 0}"
#guard ((seeds.map fun s => (p2Offsets (genCase s)).length).foldl (· + ·) 0) ≥ 100

/-- P3: in a Done run, a literal that the target has once and the source not at all is pushed (it
can come from nowhere else), with the padding of its target word (Z:634). -/
def p3Offsets (c : Case) : List Nat :=
  let r := c.run
  if r.1 != .done then [] else
  (List.range c.tgt.length).filter fun j =>
    let t := (c.tgt.getD j (jk, 0)).1
    FlatShuffler.isLiteralValue t && t.kind == 0 &&
      (c.tgt.filter fun (x, _) => x == t).length == 1 && !(c.src.any fun (x, _) => x == t)

def p3 (c : Case) : Bool :=
  let r := c.run
  (p3Offsets c).all fun j => get r.2.pad (BitVec.ofNat 64 j) == (c.tgt.getD j (jk, 0)).2

#guard seeds.all fun s => p3 (genCase s)
#eval s!"P3 offsets {(seeds.map fun s => (p3Offsets (genCase s)).length).foldl (· + ·) 0}"
#guard ((seeds.map fun s => (p3Offsets (genCase s)).length).foldl (· + ·) 0) ≥ 20

/-! ### The native vectors of the compiled Zig `shuffle`

A vector runs one plan when no target word is a wildcard (kind 1): then `saw_wildcard_copy` is
never set (a copy in a wildcard slot needs a junk target slot), `shuffle` runs the planner once
with `take` false and the spill bytes of the input (Z:1322-1359), and status 0, 1, 2 are Done,
Blocked and an assertion exit of `plannerRun` (for a reach of at least 2 and sizes of at most 1,024).
For status 0 the vector has the stack (padding included), the trace and the sources; for 1 and 2 only
the status. After Done the spill byte of each source variable is 1 if `plannerRun` spilled it
(or it was spilled), else 0 (the restore and `commit`, Z:1290-1313), and the other bytes are those of
the input. -/

open Lean in
structure Vec where
  id : String
  source : List Nat
  target : List Nat
  spills : List Nat
  reach : Nat
  allowed : Bool
  status : Nat
  stack : List Nat
  trace : List (Nat × Nat × Nat)
  sources : List (Option Nat)
  spillsAfter : List Nat

open Lean in
def Vec.ofJson (j : Json) : Except String Vec := do
  let arr (k : String) : Except String (List Nat) := do
    return (← j.getObjValAs? (Array Nat) k).toList
  let opt (k : String) : Except String (Array Json) :=
    match j.getObjVal? k with
    | .ok (.arr a) => pure a
    | _ => pure #[]
  let trace ← (← opt "trace").toList.mapM fun e => do
    let a ← e.getArr?
    match a.toList with
    | [k, d, w] => return (← k.getNat?, ← d.getNat?, ← w.getNat?)
    | _ => throw "trace entry"
  let sources ← (← opt "sources").toList.mapM fun e =>
    if e.isNull then pure none else (some <$> e.getNat?)
  let id ← j.getObjValAs? String "id"
  let source ← arr "source"
  let target ← arr "target"
  let spills ← arr "spills"
  let reach ← j.getObjValAs? Nat "reach"
  let allowed ← j.getObjValAs? Bool "allowed"
  let status ← j.getObjValAs? Nat "status"
  let stack := (← opt "stack").toList.filterMap (·.getNat?.toOption)
  let spillsAfter ← arr "spills_after"
  return { id, source, target, spills, reach, allowed, status, stack, trace, sources, spillsAfter }

def slotOfWord (w : Nat) : StackSlot × BitVec 16 :=
  Slot.split (Lift.Pilot.Slot.ofWord (BitVec.ofNat 64 w))

def wordOf (p : StackSlot × BitVec 16) : Nat := (Slot.join p).word.toNat

/-- One plan runs and the sizes and the reach are those that `plannerRun` models. -/
def Vec.eligible (x : Vec) : Bool :=
  2 ≤ x.reach && x.source.length ≤ 64 && x.target.length ≤ 64 &&
    x.target.all fun w => (slotOfWord w).1.kind != 1

/-- The check of one vector: none, or the message. -/
def Vec.check (x : Vec) : Option String :=
  let pl := mkPl (x.source.map slotOfWord) (x.target.map slotOfWord) x.allowed (BitVec.ofNat 64 x.reach)
  let spills : BitVec 32 → BitVec 8 := fun i => BitVec.ofNat 8 (x.spills.getD i.toNat 0)
  let r := run pl false spills
  let n := x.target.length
  match x.status with
  | 1 => if r.1 == .blocked then none else some s!"{x.id}: status 1, model {repr r.1}"
  | 2 => if r.1 == .assertionExit then none else some s!"{x.id}: status 2, model {repr r.1}"
  | 0 =>
    if r.1 != .done then some s!"{x.id}: status 0, model {repr r.1}"
    else if (outData r.2 n).map wordOf != x.stack then some s!"{x.id}: stack"
    else if r.2.trace.map (fun o => (o.op.kind.toNat, o.op.depth.toNat, wordOf (o.op.slot, o.pad))) != x.trace then
      some s!"{x.id}: trace"
    else if (outSources r.2 n).map (fun w => if w == NONE then none else some w.toNat) != x.sources then
      some s!"{x.id}: sources"
    else
      let srcVars := (x.source.map slotOfWord).map (·.1) |>.filter FlatShuffler.Flat.isVariable
      let want : List Nat := (List.range x.spillsAfter.length).map fun i =>
        match srcVars.find? (·.payload.toNat == i) with
        | some s => if FlatShuffler.Flat.spillIsSpilled r.2.spills s then 1 else 0
        | none => x.spills.getD i 0
      if want != x.spillsAfter then some s!"{x.id}: spills after" else none
  | k => some s!"{x.id}: status {k}"

open Lean in
/-- The number of eligible vectors of a file, by status, or the first failure. -/
def checkFile (path : String) : IO (Nat × Nat × Nat) := do
  let txt ← IO.FS.readFile path
  let mut c0 := 0
  let mut c1 := 0
  let mut c2 := 0
  for l in txt.splitOn "\n" do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    if (j.getObjVal? "id").toOption.isNone then continue
    let x ← IO.ofExcept (Vec.ofJson j)
    unless x.eligible do continue
    if let some msg := x.check then throw (IO.userError msg)
    match x.status with
    | 0 => c0 := c0 + 1
    | 1 => c1 := c1 + 1
    | _ => c2 := c2 + 1
  return (c0, c1, c2)

#eval show IO Unit from do
  let (a0, a1, a2) ← checkFile "Lift/Shuffler/Test/data/native-random.jsonl"
  let (b0, b1, b2) ← checkFile "Lift/Shuffler/Test/data/native-boundary.jsonl"
  IO.println s!"native vectors compared (done, blocked, assertion): random {a0}/{a1}/{a2}, boundary {b0}/{b1}/{b2}"
  unless a0 + b0 ≥ 100 && a1 + b1 ≥ 1 && a2 + b2 ≥ 1 do
    throw (IO.userError "too few eligible native vectors")

end Lift.Shuffler.Test.Planner
