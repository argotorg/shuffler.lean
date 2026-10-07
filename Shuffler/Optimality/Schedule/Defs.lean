import Shuffler.Optimality.Schedule.Estimate
import Shuffler.Optimality.GenerationChoice
import Shuffler.Optimality.ValueGraph
import Shuffler.Optimality.Schedule.Cycles
import Shuffler.Optimality.Schedule.Chains
import Shuffler.Optimality.Reintroduction

/-!
A bounded placement heuristic. It returns ordinary instruction lists.
Checked replay and the complete fallback are kept in `Schedule.Build`.

Each round adds one requested value. A position is fixed only when the next
birth would put it outside SWAP reach. Earlier swaps and out-of-order births
are allowed. `Reserve` is checked at the end of every accepted round.
-/

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

inductive Policy where
  | balanced
  | eager
  | preserve
  | chain
  deriving DecidableEq

-- Keep the original choices while the lineage ranking and joined cycles
-- are evaluated. Both modes use the same checked scheduling loop.
inductive Mode where
  | relaxed
  | lineage
  | chains
  deriving DecidableEq

structure Strategy where
  policy : Policy
  mode : Mode
  deriving DecidableEq

def Strategy.balanced : Strategy := ⟨.balanced, .lineage⟩
def Strategy.eager : Strategy := ⟨.eager, .lineage⟩
def Strategy.preserve : Strategy := ⟨.preserve, .lineage⟩
def Strategy.chain : Strategy := ⟨.chain, .chains⟩
def Strategy.withMode (strategy : Strategy) (mode : Mode) : Strategy := { strategy with mode }

def simulate (spills : SpillSet) (source : Stack) (ops : List Op) : Option Stack :=
  (replay spills source ops).map (fun result => result.target)

def swapPosition (stack : Stack) (position : Nat) : List Op :=
  if position + 1 < stack.length then [.swap (stack.length - 1 - position)] else []

-- Every occurrence is considered. A matching position emits no swaps.
def placements (stack : Stack) (position : Nat) (value : Value) : List (List Op) :=
  ((List.range stack.length).filter fun index =>
    decide (max position (frozen stack) ≤ index ∧ stack[index]? = some value)).map fun index =>
      if index = position then []
      else swapPosition stack index ++ swapPosition stack position

def swapPrefixes (stack : Stack) : List (List Op) :=
  [] :: ((List.range (min MAX_SWAP_DEPTH (stack.length - 1))).map fun index =>
    [.swap (index + 1)])

-- With a full window the next frozen output is mandatory. If it is already
-- correct, swaps among the other sixteen positions remain candidates.
def prefixes (stack target : Stack) : List (List Op) :=
  if stack.length < MAX_SWAP_DEPTH + 1 then swapPrefixes stack
  else
    let position := frozen stack
    match target[position]? with
    | none => []
    | some value =>
        let place := placements stack position value
        if stack[position]? = some value then
          place ++ ((List.range MAX_DUP_DEPTH).map fun index => [.swap (index + 1)])
        else place

def preparePrefixes (spills : SpillSet) (stack target : Stack)
    (cycles : List (List Op)) : List (List Op) :=
  cycles.flatMap fun ops =>
    match simulate spills stack ops with
    | none => []
    | some after => (prefixes after target).map (ops ++ ·)

def cyclePrefixes (spills : SpillSet) (stack target : Stack) : List (List Op) :=
  preparePrefixes spills stack target (readyCycles spills stack target)

def demandedValues (target : Stack) (missing : Multiset Value) : List Value :=
  (target.filter fun value => decide (value ∈ missing)).dedup

-- The first demanded kind ensures a candidate even when all new values are
-- far ahead. The two short target ranges and the window supply other choices.
def birthValues (stack target : Stack) (missing : Multiset Value) : List Value :=
  let first := (target.find? fun value => decide (value ∈ missing)).toList
  let near := (target.drop (frozen stack)).take (MAX_SWAP_DEPTH + 1)
  let born := (target.drop stack.length).take (MAX_SWAP_DEPTH + 1)
  ((first ++ near ++ born ++ window stack).filter fun value =>
    decide (value ∈ missing)).dedup

def generationBase (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (target : Stack) (missing : Multiset Value) : Nat :=
  (demandedValues target missing).foldl (fun total value =>
    let dup := costs.dup.score weights
    let unit := min dup ((introductionCost costs weights spills value).getD dup)
    total + missing.count value * unit) 0

-- Charge regeneration only when a source cannot remain available. Rescue
-- swaps can also do placement work, so their cost is not added here.
def sourcePressure (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (stack target : Stack) (missing : Multiset Value) : Nat :=
  let reachable := window stack
  (demandedValues target missing).foldl (fun total value =>
    match introductionCost costs weights spills value with
    | none => total
    | some intro =>
        let extra := intro - costs.dup.score weights
        let reserved := MAX_SWAP_DEPTH + 1 ≤ stack.length &&
          target[frozen stack]? == some value && reachable.count value == 1
        if reserved then total + extra
        else if value ∈ reachable then total else total + extra) 0

def mismatchCount (stack target : Stack) : Nat :=
  ((List.zip stack target).filter fun pair => decide (pair.1 ≠ pair.2)).length

-- A birth can keep the old top value as the next chain pivot. Prefer that
-- on a score tie when an unfinished old position still wants this value.
def continuesOldChain (stack target : Stack) : Bool :=
  stack.getLast? == stack[stack.length - 2]? &&
    (List.zip (window stack) (target.drop (frozen stack))).any fun pair =>
      pair.1 != pair.2 && stack.getLast? == some pair.2

structure Candidate where
  ops : List Op
  stack : Stack
  missing : Multiset Value
  estimate : Nat
  relaxedEstimate : Nat
  pressure : Nat
  immediate : Nat
  mismatches : Nat
  birthMatch : Bool
  continuesChain : Bool

def makeCandidate (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (stack target : Stack) (missing : Multiset Value) (before : List Op)
    (value : Value) : Option Candidate := do
  let prepared ← simulate spills stack before
  let generation ← cheapestGeneration costs weights spills prepared value
  let ops := before ++ [generation]
  let after ← simulate spills stack ops
  let rest := missing.erase value
  if Reserve spills after target rest then
    let pressure := sourcePressure costs weights spills after target rest
    let immediate := (opsCost costs ops).score weights
    let generation := generationBase costs weights spills target rest
    let estimate := immediate + generation +
      max (pressure + costs.swap.score weights * placementEstimate after target)
        (lineageBound costs weights spills after target rest)
    let relaxedEstimate := immediate + generation + pressure +
      costs.swap.score weights * relaxedPlacementEstimate after target
    some {
      ops := ops
      stack := after
      missing := rest
      estimate := estimate
      relaxedEstimate := relaxedEstimate
      pressure := pressure
      immediate := immediate
      mismatches := mismatchCount after target
      birthMatch := target[stack.length]? == some value
      continuesChain := continuesOldChain after target
    }
  else none

def prefers (strategy : Strategy) (a b : Candidate) : Bool :=
  let pa := (if strategy.mode = .relaxed then a.relaxedEstimate else a.estimate) +
    if strategy.policy = .preserve then a.pressure else 0
  let pb := (if strategy.mode = .relaxed then b.relaxedEstimate else b.estimate) +
    if strategy.policy = .preserve then b.pressure else 0
  if pa != pb then pa < pb
  else if strategy.policy = .chain && a.continuesChain != b.continuesChain then a.continuesChain
  else if strategy.policy = .eager && a.mismatches != b.mismatches then a.mismatches < b.mismatches
  else if a.immediate != b.immediate then a.immediate < b.immediate
  else if a.birthMatch != b.birthMatch then a.birthMatch
  else a.mismatches ≤ b.mismatches

def choose (strategy : Strategy) : List Candidate → Option Candidate
  | [] => none
  | first :: rest => some (rest.foldl (fun best candidate =>
      if prefers strategy candidate best then candidate else best) first)

def next (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack target : Stack) (missing : Multiset Value) : Option Candidate :=
  let joined := if strategy.mode = .relaxed then [] else
    preparePrefixes spills stack target
      (joinedCycles stack target missing ++ topValueCycles stack target ++
        if strategy.mode = .chains then openChains stack target else [])
  choose strategy ((prefixes stack target ++ cyclePrefixes spills stack target ++ joined).dedup.flatMap fun before =>
    (birthValues stack target missing).filterMap fun value =>
      makeCandidate costs weights spills stack target missing before value)

-- Equal occurrences may exchange roles in the final cycle decomposition.
def finish (spills : SpillSet) (stack target : Stack) : Option (List Op) :=
  (ValueGraph.build spills stack target).map (fun result => flatten result.trace)

def rounds (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (target : Stack) :
    Nat → Stack → Multiset Value → List Op → Option (List Op)
  | 0, stack, missing, reversed => do
      if missing = 0 then
        let last ← finish spills stack target
        some (reversed.reverse ++ last)
      else none
  | fuel + 1, stack, missing, reversed => do
      let candidate ← next strategy costs weights spills stack target missing
      rounds strategy costs weights spills target fuel candidate.stack candidate.missing
        (candidate.ops.reverse ++ reversed)

def plan (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) : Option (List Op) :=
  rounds strategy costs weights spills target missing.card source missing []

end Shuffler.Optimality.Schedule
