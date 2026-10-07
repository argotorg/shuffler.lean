import Shuffler.Optimality.BirthPlacement.FixedWord.Theorems
import Shuffler.Optimality.BirthPlacement.Improve
import Shuffler.Optimality.Replay

namespace Shuffler.Optimality.BirthPlacement.Sharpness

def value (index : Nat) : Value := .Var ⟨index⟩

def spills (count : Nat) : SpillSet := (Finset.range (count + 1)).image VarId.mk

-- v0, v1, v1, v2, v2, ..., v(count-1), v(count-1), vcount.
def word (count : Nat) : Stack :=
  List.ofFn fun index : Fin (2 * count) => value ((index.val + 1) / 2)

def target (count : Nat) : Stack :=
  List.ofFn fun index : Fin (2 * count) => value
    (if index.val = 0 then 1
     else if index.val % 2 = 0 then index.val / 2 - 1
     else if index.val + 1 = 2 * count then count - 1
     else index.val / 2 + 2)

def comparisonOps (count : Nat) : List Op :=
  [.load ⟨0⟩] ++ ((List.range (count - 1)).flatMap fun index =>
    [.load ⟨index + 1⟩, .dup 1, .swap (if index = 0 then 2 else 3)]) ++
    [.load ⟨count⟩, .swap 2]

def canonicalOps (count : Nat) : List Op :=
  [.load ⟨0⟩, .load ⟨1⟩, .swap 1, .dup 2] ++
    ((List.range (count - 2)).flatMap fun index =>
      [.load ⟨index + 2⟩, .swap 2, .swap 1, .dup 3]) ++
    [.load ⟨count⟩, .swap 2, .swap 1]

def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push ⟨0, by decide⟩) (fun _ => .push ⟨0, by decide⟩)

-- Each component is obtained from an actual production Trace.
def facts (count : Nat) (weights : Weights) : Option (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let reference ← replay (spills count) [] (comparisonOps count)
  let actual := reference.built.trace
  let candidate := (optimizeTraceWord costs weights actual reference.built.noPop).built.trace
  let base := baseline costs weights (spills count) [] (reference.target : Multiset Value)
  return (candidate.swapCount, actual.swapCount, (SwapRuns.normalize candidate).swapCount,
    (traceCost costs candidate).score weights - base,
    (traceCost costs actual).score weights - base, base)

def check (count : Nat) (weights : Weights) : Bool :=
  match replay (spills count) [] (comparisonOps count) with
  | none => false
  | some reference =>
      let actual := reference.built.trace
      let candidate := (optimizeTraceWord costs weights actual reference.built.noPop).built.trace
      let candidateNoPop := (optimizeTraceWord costs weights actual reference.built.noPop).built.noPop
      decide (reference.target = target count) &&
        decide (SwapRuns.births actual = word count) &&
        decide (flatten candidate = canonicalOps count) &&
        decide ((replay (spills count) [] (flatten candidate)).map (·.target) = some (target count)) &&
        decide ((SwapRuns.normalize candidate).swapCount = candidate.swapCount) &&
        decide ((improveTraceWord costs weights candidate candidateNoPop).swapCount = candidate.swapCount)

end Shuffler.Optimality.BirthPlacement.Sharpness
