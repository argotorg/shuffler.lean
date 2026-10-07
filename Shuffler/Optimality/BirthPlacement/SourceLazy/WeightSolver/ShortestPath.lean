import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Network

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

structure Flow where
  capacity : Array Nat
  potential : Array Int
  deriving Inhabited, Repr

def initial (graph : Network) : Flow :=
  ⟨graph.edges.map Arc.capacity, Array.replicate graph.outgoing.size 0⟩

structure Labels where
  distance : Array (Option Int)
  predecessor : Array (Option Nat)
  settled : Array Bool
  deriving Inhabited, Repr

-- This scan is the simple Lean implementation. A bucket queue can replace it
-- for the separate quadratic runtime argument.
def leastUnsettled (labels : Labels) : Option (Nat × Int) :=
  (List.range labels.distance.size).foldl (fun best index =>
    if labels.settled[index]! then best
    else match labels.distance[index]!, best with
      | none, _ => best
      | some distance, none => some (index, distance)
      | some distance, some (_, prior) => if distance < prior then some (index, distance) else best) none

def relax (graph : Network) (flow : Flow) (vertex : Nat) (distance : Int)
    (labels : Labels) : Labels :=
  graph.outgoing[vertex]!.foldl (fun labels edgeIndex =>
    let edge := graph.edges[edgeIndex]!
    if flow.capacity[edgeIndex]! = 0 || labels.settled[edge.head]! then labels
    else
      let candidate := distance + edge.cost + flow.potential[vertex]! - flow.potential[edge.head]!
      let improve := match labels.distance[edge.head]! with
        | none => true
        | some old => candidate < old
      if improve then { labels with
        distance := labels.distance.set! edge.head (some candidate)
        predecessor := labels.predecessor.set! edge.head (some edgeIndex) }
      else labels) labels

def search (graph : Network) (flow : Flow) : Nat → Labels → Option (Labels × Int)
  | 0, _ => none
  | fuel + 1, labels => do
      let (vertex, distance) ← leastUnsettled labels
      if vertex = graph.sink then return (labels, distance)
      let labels := { labels with settled := labels.settled.set! vertex true }
      search graph flow fuel (relax graph flow vertex distance labels)

def shortest (graph : Network) (flow : Flow) : Option (Labels × Int) :=
  search graph flow graph.outgoing.size
    ⟨(Array.replicate graph.outgoing.size none).set! graph.source (some 0),
      Array.replicate graph.outgoing.size none, Array.replicate graph.outgoing.size false⟩

def path (graph : Network) (labels : Labels) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, vertex =>
      if vertex = graph.source then some []
      else do
        let edgeIndex ← labels.predecessor[vertex]!
        let previous ← path graph labels fuel graph.edges[edgeIndex]!.tail
        return edgeIndex :: previous

def augment (graph : Network) (flow : Flow) : Option Flow := do
  let (labels, distance) ← shortest graph flow
  let steps ← path graph labels graph.outgoing.size graph.sink
  let capacity := steps.foldl (fun capacity edgeIndex =>
    let reverse := graph.edges[edgeIndex]!.reverse
    (capacity.set! edgeIndex (capacity[edgeIndex]! - 1)).set! reverse (capacity[reverse]! + 1)) flow.capacity
  -- Truncation also updates unreachable vertices. This keeps all residual
  -- reduced costs nonnegative when the current potentials are feasible.
  let potential := (List.range graph.outgoing.size).foldl (fun potential vertex =>
    let change := match labels.distance[vertex]! with
      | none => distance
      | some found => min found distance
    potential.set! vertex (flow.potential[vertex]! + change)) flow.potential
  return ⟨capacity, potential⟩

def run (graph : Network) (count : Nat) : Option Flow :=
  (List.range count).foldlM (fun flow _ => augment graph flow) (initial graph)

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
