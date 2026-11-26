import Skel.IntQ.Refute
import Skel.Discover.Rand
import Lift.Shuffler.Ext.FlatPlan
import Lift.Shuffler.Zig.Planner

/-! The samplers of the planner types for the refuter (task INT-Q3). The refuter (`Skel/IntQ/Refute.lean`) draws each input of
a model function with `Skel.IntQ.Refute.Draw`. The planner functions have inputs of the types `Planner`, `PSt`, `Mapping`,
`Builder`, `Locals`, `RunU` and functions of them, which have no `Refute.Draw` instance: the verdict of 6 accepted statements
of INT-Q2 was `unknown`. A sampler of each of these types is derived here with the handler of SAMPLE-DERIVE
(`deriving instance Skel.Discover.Rand.Draw`, `Skel/Discover/Rand.lean`), and `Refute.Draw` takes it (an instance of low
priority: the instances of `Refute.lean` come first).

The leaf samplers have the ranges of `Refute.lean`: a `Word` is below 24, or `NONE` (0, 12 or 50 percent, by input); a `BitVec 8` is below 4; a
`StackSlot` is the slot of `Refute.lean`. A `Vector` of 1024 elements has 24 drawn elements, the others are the quiet value
(`Rand.Draw (Vector α n)`). A function is a table: `BitVec 32 → BitVec 8` has 16 entries (as the spill table of `Draw St`),
`Nat → α` has 8 entries and the quiet value after them. A structure and an enumeration have no `Draw` of their own: `deriving`
makes it, fields in order. A type that has fields of a function type has no `ToJson`, so `derive_state` (which derives the
printer and the parser too) does not apply, and the instances are derived with `deriving instance`, innermost first. -/

namespace Skel.IntQ.Refute

open Coordinator.Dst
open FlatShuffler (StackSlot)

/-- The bounds of the derived samplers: sizes and words below 24, 24 drawn elements of a vector, at most 8 elements of a list. -/
def bounds : Skel.Discover.Rand.Bounds :=
  { natMax := 23, wordMax := 23, edgePercent := 0, maxLen := 8, active := 24, nonePercent := 12, tries := 1 }

/-- A word: `NONE` with the share `nonePercent` of the bounds (a calm draw is 0), else a number up to `wordMax`. -/
instance (priority := high) : Skel.Discover.Rand.Draw (BitVec 64) :=
  ⟨fun b g =>
    if b.calm then 0
    else if Skel.Discover.Rand.natUpTo (g.stream 1) 99 < b.nonePercent then FlatShuffler.Flat.NONE
    else BitVec.ofNat 64 (Skel.Discover.Rand.natUpTo g b.wordMax)⟩

/-- A byte: below 4 (a kind of an operation, a flag). -/
instance (priority := high) : Skel.Discover.Rand.Draw (BitVec 8) :=
  ⟨fun b g => if b.calm then 0 else BitVec.ofNat 8 (Skel.Discover.Rand.natUpTo g 3)⟩

/-- A slot: the slot of `Refute.lean` (a calm draw is the default slot). -/
instance : Skel.Discover.Rand.Draw StackSlot := ⟨fun b g => if b.calm then default else (draw g : StackSlot × Rng).1⟩

/-- A table of 16 entries (a spill set of the model). -/
instance : Skel.Discover.Rand.Draw (BitVec 32 → BitVec 8) :=
  ⟨fun b g =>
    let t := (List.range 16).map fun i => Skel.Discover.Rand.Draw.draw b (g.stream i) (α := BitVec 8)
    fun id => t.getD id.toNat 0⟩

/-- A table of 8 entries, and the quiet value after them (the locals of the attempts of `Planner.run`). -/
instance {α : Type} [Skel.Discover.Rand.Draw α] : Skel.Discover.Rand.Draw (Nat → α) :=
  ⟨fun b g =>
    let t := (List.range 8).map fun i => Skel.Discover.Rand.Draw.draw b (g.stream i) (α := α)
    let q := Skel.Discover.Rand.Draw.draw b.quiet (Rng.ofSeed 0) (α := α)
    fun i => t.getD i q⟩

deriving instance Skel.Discover.Rand.Draw for FlatShuffler.Op
deriving instance Skel.Discover.Rand.Draw for Lift.Shuffler.Zig.OpP
deriving instance Skel.Discover.Rand.Draw for FlatShuffler.Flat.Mapping
deriving instance Skel.Discover.Rand.Draw for FlatShuffler.Flat.Uninit
deriving instance Skel.Discover.Rand.Draw for FlatShuffler.Flat.Locals
deriving instance Skel.Discover.Rand.Draw for FlatShuffler.Flat.ResolveU
deriving instance Skel.Discover.Rand.Draw for FlatShuffler.Flat.RunU
deriving instance Skel.Discover.Rand.Draw for FlatShuffler.Flat.Builder
deriving instance Skel.Discover.Rand.Draw for FlatShuffler.Flat.Planner
deriving instance Skel.Discover.Rand.Draw for Lift.Shuffler.Zig.Planner
deriving instance Skel.Discover.Rand.Draw for Lift.Shuffler.Zig.PSt

/-! ## The decision of a contract

A contract `C` is decided with `decide`. For `∀ v ∈ l, p v` with a list `l` of words, instance search takes
`BitVec.instDecidableForallBitVec` (`∀ v : BitVec 64, v ∈ l → p v`, all 2^64 words), and the run does not end (the contract of
`Planner.classify`: `∀ v ∈ M.dest.toList, v.toNat < maxStackSize`). These instances decide by the list. -/

instance (priority := high) {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] : Decidable (∀ a ∈ l, p a) :=
  List.decidableBAll p l

instance (priority := high) {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] : Decidable (∃ a, a ∈ l ∧ p a) :=
  List.decidableBEx p l

/-- The refuter draws a type that has a derived sampler. The share of `NONE` in the words of an input is 0, 12 or 50 percent
(one of them for each input): a contract that bounds each word needs the first, a path of `NONE` the others. -/
instance (priority := low) {α : Type} [Skel.Discover.Rand.Draw α] : Draw α :=
  ⟨fun g =>
    let (k, g) := g.nat 3
    (Skel.Discover.Rand.Draw.draw { bounds with nonePercent := [0, 12, 50].getD k 0 } (g.stream 0), g.stream 1)⟩

end Skel.IntQ.Refute
