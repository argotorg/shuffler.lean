import Shuffler.Optimality.ShortGrowth.Graph
import Shuffler.Optimality.GenerationChoice

namespace Shuffler.Optimality.ShortGrowth

def simulate (spills : SpillSet) (source : Stack) (ops : List Op) : Option Stack :=
  (replay spills source ops).map fun result => result.target

def emitBirths (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) :
    Stack → List Birth → Option (List Op)
  | _, [] => some []
  | stack, birth :: rest => do
      if birth.position ≠ stack.length then none
      else
        let generation ← cheapestGeneration costs weights spills stack birth.value
        let swaps := birth.path.reverse.map fun position => Op.swap (birth.position - position)
        let ops := generation :: swaps
        let after ← simulate spills stack ops
        let later ← emitBirths costs weights spills after rest
        some (ops ++ later)

-- A matching prefix can be left outside the final window. This also covers
-- padded short-stack examples. Exact replay checks source availability when
-- a copy exists only in that prefix.
def plan (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) : Option (List Op) := do
  let fixed := target.length - (MAX_SWAP_DEPTH + 1)
  if Shuffler.Placement.Reserve spills source target missing ∧ fixed ≤ source.length ∧
      target.take fixed = source.take fixed then
    let result ← graph source target missing
    let before := result.cycles.flatMap fun cycle =>
      (cyclePositions (source.length - 1) cycle).map fun position =>
        Op.swap (source.length - 1 - position)
    let prepared ← simulate spills source before
    let births ← emitBirths costs weights spills prepared result.births
    some (before ++ births)
  else none

end Shuffler.Optimality.ShortGrowth
