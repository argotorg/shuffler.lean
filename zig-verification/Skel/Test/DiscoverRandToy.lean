import Skel.Discover.Rand
import Skel.Discover.Site

/-! The toy loop states of the suite `discoverrand` (`Skel/Test/DiscoverRand.lean`). The types have no sampler, no printer and no
parser: `derive_state` makes them. The machine is the shape of a model state of the held-out evaluation, with no name of it:
a vector of small structures (a word, a Nat and an `Option` field), an index, a count and an enum. -/

namespace DiscoverRandToy

open Lean Skel.Discover Skel.Discover.Rand

/-- The kind of a slot. -/
inductive Mode where
  | idle | scan | done
  deriving BEq, DecidableEq

/-- One slot of the machine: a word, a Nat and an `Option` field. -/
structure Cell where
  word : BitVec 64
  count : Nat
  tag : Option (BitVec 8)
  deriving BEq

/-- The state of the toy loop: 1024 slots, an index, a count and a mode. -/
structure Machine where
  cells : Vector Cell 1024
  idx : Nat
  total : Nat
  mode : Mode
  deriving BEq

/-- A state with a small vector, a `Bool`, a `Fin`, a list, an array, a pair and small words. -/
structure Small where
  flag : Bool
  small : Fin 5
  xs : List Nat
  ys : Array (BitVec 16)
  pair : Nat × Bool
  byte : UInt8
  wide : UInt64
  signed : Int
  trio : Vector Nat 3
  deriving BEq

/-- A type with a parameter. -/
structure Pair (α : Type) where
  first : α
  second : Option α
  deriving BEq

/-- A state whose fields are two instances of a type with a parameter. -/
structure Holder where
  p : Pair Nat
  q : Pair (BitVec 8)
  deriving BEq

derive_state Machine Small Holder

/-- The scan of the slots: it adds the count of each slot from the index to the end. -/
def scan : Nat → Machine → Option Nat
  | 0, _ => none
  | n + 1, s =>
    if h : s.idx < 1024 then scan n { s with total := s.total + s.cells[s.idx].count, idx := s.idx + 1 }
    else some s.total

/-- A short loop: it steps from the index to 8. -/
def walk : Nat → Machine → Option Nat
  | 0, _ => none
  | n + 1, s =>
    if h : s.idx < 8 then walk n { s with total := s.total + (s.cells[s.idx]'(Nat.lt_trans h (by decide))).count, idx := s.idx + 1 }
    else some s.total

/-- The same loop with an exit that is true at the start: it never takes a step. -/
def stop : Nat → Machine → Option Nat
  | 0, _ => none
  | n + 1, s => if s.idx < 1025 then some s.total else stop n { s with idx := s.idx + 1 }

/-- A loop that never exits before its fuel is spent. -/
def spin : Nat → Machine → Option Nat
  | 0, _ => none
  | n + 1, s => spin n { s with total := s.total + 1 }

open Elab Term in
/-- `rand_site% f`: the JSON text of `siteOf? f`, run when the term is elaborated. -/
elab "rand_site% " f:ident : term => do
  match ← siteOf? f.getId with
  | .ok s => pure (mkStrLit (toJson s).compress)
  | .error e => throwError "siteOf? failed: {repr e}"

/-- The JSON of the sites of the loops above. -/
def scanJson : String := rand_site% DiscoverRandToy.scan
def walkJson : String := rand_site% DiscoverRandToy.walk
def stopJson : String := rand_site% DiscoverRandToy.stop
def spinJson : String := rand_site% DiscoverRandToy.spin

end DiscoverRandToy
