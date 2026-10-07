import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightCertificate
import Init.Data.Vector.OfFn

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

structure Arc where
  tail : Nat
  head : Nat
  capacity : Nat
  cost : Int
  reverse : Nat
  deriving Inhabited, Repr

structure Network where
  source : Nat
  sink : Nat
  edges : Array Arc
  outgoing : Array (List Nat)
  deriving Inhabited, Repr

def Network.add (graph : Network) (tail head capacity : Nat) (cost : Int) : Network :=
  let index := graph.edges.size
  let outgoing := graph.outgoing.set! tail (index :: graph.outgoing[tail]!)
  { graph with
    edges := graph.edges.push ⟨tail, head, capacity, cost, index + 1⟩ |>.push
      ⟨head, tail, 0, -cost, index⟩
    outgoing := outgoing.set! head ((index + 1) :: outgoing[head]!) }

-- Each target has one chain node for source-interior rows and one for other rows.
-- A generic row-to-column path has cost 1 + [both endpoints are interior].
-- A legal identity edge has cost zero.
def network [DecidableEq α] (reach height : Nat) (word target : Fin size → α) : Network :=
  let births := Vector.ofFn word
  let outputs := Vector.ofFn target
  let indices := List.finRange size
  let base : Network := ⟨4 * size, 4 * size + 1, #[], Array.replicate (4 * size + 2) []⟩
  let columns := indices.foldl (fun graph index =>
    let graph := graph.add (size + index.val) graph.sink 1 0
    let graph := graph.add (2 * size + index.val) (size + index.val) (size + 1)
      (if index.val + 1 < height then 1 else 0)
    let graph := graph.add (3 * size + index.val) (size + index.val) (size + 1) 0
    match indices.find? (fun next => index.val < next.val && outputs[index.val] == outputs[next.val]) with
    | none => graph
    | some next =>
        (graph.add (2 * size + index.val) (2 * size + next.val) (size + 1) 0).add
          (3 * size + index.val) (3 * size + next.val) (size + 1) 0) base
  indices.foldl (fun graph index =>
    let graph := graph.add graph.source index.val 1 0
    let graph := if births[index.val] = outputs[index.val] then
        graph.add index.val (size + index.val) (size + 1) 0 else graph
    if index.val + reach + 1 < height then graph
    else match indices.find? (fun output =>
        index.val ≤ output.val + reach && births[index.val] == outputs[output.val]) with
      | none => graph
      | some output => graph.add index.val
          ((if index.val + 1 < height then 2 else 3) * size + output.val) (size + 1) 1) columns

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
