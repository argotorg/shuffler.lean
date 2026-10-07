import Shuffler.Optimality.ValueGraph.Defs
import Shuffler.Feasibility.Spec

/-!
The graph construction for growth inside a final window of seventeen slots.
Old mismatches are directed value edges. An extra root supplies one edge to
each birth target and receives one edge for each requested added occurrence.
An Euler tour split at the root assigns one old-edge trail to each birth.
The born value closes that trail, and its new top resolves the resulting cycle.

A directed cycle through the old top is extracted first. Any unserved value
component that touches this cycle is inserted into it. This retains the top's
one-swap discount. A correct old top can also join an unserved value component.
The definitions return data only; checked replay is in `ShortGrowth.Build`.
-/

namespace Shuffler.Optimality.ShortGrowth

inductive Edge where
  | old (position : Nat)
  | enter (position : Nat)
  | leave (value : Value) (serial : Nat)
  deriving DecidableEq

def Edge.start (source : Stack) : Edge → Option Value
  | .old position => source[position]?
  | .enter _ => none
  | .leave value _ => some value

def Edge.finish (target : Stack) : Edge → Option Value
  | .old position => target[position]?
  | .enter position => target[position]?
  | .leave _ _ => none

structure Birth where
  position : Nat
  value : Value
  path : List Nat

structure GraphPlan where
  cycles : List (List Nat)
  births : List Birth

def oldEdges (source target : Stack) : List Nat :=
  (List.range source.length).filter fun i => source[i]? != target[i]?

-- Breadth-first search stores a reversed path. A vertex is expanded once.
-- At most one entry is queued per old edge, plus the initial vertex.
def findPath (source target : Stack) (edges : List Nat) (goal : Option Value) :
    Nat → List (Option Value × List Nat) → List (Option Value) → Option (List Nat)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, (vertex, reversed) :: queue, seen =>
      if vertex = goal then some reversed.reverse
      else if vertex ∈ seen then findPath source target edges goal fuel queue seen
      else
        let next := (edges.filter fun i => source[i]? = vertex).map fun i =>
          (target[i]?, i :: reversed)
        findPath source target edges goal fuel (queue ++ next) (vertex :: seen)

def topCircuit (source target : Stack) (edges : List Nat) : List Nat :=
  let top := source.length - 1
  if top ∈ edges then
    match findPath source target (edges.erase top) source[top]?
      (edges.length + 1) [(target[top]?, [])] [] with
    | none => []
    | some path => top :: path
  else if 0 < source.length then [top] else []

def addedValues (target : Stack) (missing : Multiset Value) : List Value :=
  target.dedup.flatMap fun value => List.replicate (missing.count value) value

def augmentedEdges (source target : Stack) (missing : Multiset Value) (old : List Nat) : List Edge :=
  ((List.range (target.length - source.length)).map fun i => .enter (source.length + i)) ++
    old.map Edge.old ++
    ((addedValues target missing).zipIdx.map fun pair => .leave pair.1 pair.2)

-- Root tours start with an enter edge because those edges are listed first.
-- Every leave edge closes one birth trail. The parse rejects malformed tours.
def decodeBirths : List Edge → Option (Nat × List Nat) → Option (List Birth)
  | [], none => some []
  | [], some _ => none
  | .enter position :: rest, none => decodeBirths rest (some (position, []))
  | .old position :: rest, some (birth, reversed) =>
      decodeBirths rest (some (birth, position :: reversed))
  | .leave value _ :: rest, some (birth, reversed) => do
      let births ← decodeBirths rest none
      some ({ position := birth, value := value, path := reversed.reverse } :: births)
  | _, _ => none

def oldPosition : Edge → Option Nat
  | .old position => some position
  | _ => none

def separate : List (List Edge) → Option GraphPlan
  | [] => some ⟨[], []⟩
  | circuit :: rest => do
      let later ← separate rest
      if circuit.all (fun edge => (oldPosition edge).isSome) then
        some ⟨circuit.filterMap oldPosition :: later.cycles, later.births⟩
      else
        let births ← decodeBirths circuit none
        some ⟨later.cycles, births ++ later.births⟩

-- Insert a closed tour immediately before an edge with the same source
-- value. The two tours have disjoint positions but can share a value vertex.
def splice (source : Stack) (base extra : List Nat) : Option (List Nat) := do
  let i ← (List.range base.length).find? fun i =>
    extra.any fun position => source[position]? = (base[i]?.bind fun p => source[p]?)
  let position ← base[i]?
  let j ← (List.range extra.length).find? fun j =>
    (extra[j]?.bind fun p => source[p]?) = source[position]?
  some (base.take i ++ extra.rotate j ++ base.drop i)

def absorb (source : Stack) : List (List Nat) → List Nat → List (List Nat) × List Nat
  | [], top => ([], top)
  | circuit :: rest, top =>
      match splice source top circuit with
      | some joined => absorb source rest joined
      | none =>
          let later := absorb source rest top
          (circuit :: later.1, later.2)

def graph (source target : Stack) (missing : Multiset Value) : Option GraphPlan := do
  let old := oldEdges source target
  let top := topCircuit source target old
  let remaining := old.filter fun position => position ∉ top
  let edges := augmentedEdges source target missing remaining
  let tours := ValueGraph.decompose (Edge.start source) (Edge.finish target) edges.length edges
  let result ← separate tours
  let joined := absorb source result.cycles top
  let before := if 1 < joined.2.length then joined.2 :: joined.1 else joined.1
  some ⟨before, result.births.mergeSort (fun a b => a.position ≤ b.position)⟩

-- Return absolute positions to exchange with the current top. The directed
-- value circuit is reversed to obtain occurrence destinations.
def cyclePositions (top : Nat) (cycle : List Nat) : List Nat :=
  if cycle.length ≤ 1 then []
  else if top ∈ cycle then
    (cycle.rotate (cycle.idxOf top + 1)).dropLast.reverse
  else cycle.reverse ++ cycle.getLast?.toList

end Shuffler.Optimality.ShortGrowth
