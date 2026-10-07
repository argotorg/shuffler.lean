import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.ShortestPath

namespace Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver

-- Consume one unit of the final integral flow, from one row to a target column.
def decodePath (graph : Network) (size : Nat) : Nat → Nat → Array Nat → Option (Nat × Array Nat)
  | 0, _, _ => none
  | fuel + 1, vertex, remaining =>
      if size ≤ vertex ∧ vertex < 2 * size then some (vertex - size, remaining)
      else do
        let edgeIndex ← graph.outgoing[vertex]!.find? fun index =>
          0 < graph.edges[index]!.capacity && 0 < remaining[index]!
        decodePath graph size fuel graph.edges[edgeIndex]!.head
          (remaining.set! edgeIndex (remaining[edgeIndex]! - 1))

def decode (graph : Network) (flow : Flow) (size : Nat) : Option (Array Nat × Array Nat) := do
  let remaining := graph.edges.mapIdx fun index edge => edge.capacity - flow.capacity[index]!
  let (_, forward, backward) ← (List.range size).foldlM (fun (remaining, forward, backward) row => do
    let (column, remaining) ← decodePath graph size graph.outgoing.size row remaining
    return (remaining, forward.push column, backward.set! column row))
      (remaining, #[], Array.replicate size 0)
  return (forward, backward)

-- Both directions are checked. No unchecked inverse enters the result type.
def checkedPermutation (size : Nat) (forward backward : Array Nat) : Option (Equiv.Perm (Fin size)) :=
  if hf : forward.size = size then
    if hb : backward.size = size then
      if hfb : ∀ i : Fin size, forward[i.val]'(by omega) < size then
        if hbb : ∀ i : Fin size, backward[i.val]'(by omega) < size then
          let f : Fin size → Fin size := fun i => ⟨forward[i.val]'(by omega), hfb i⟩
          let g : Fin size → Fin size := fun i => ⟨backward[i.val]'(by omega), hbb i⟩
          if hi : (∀ i, g (f i) = i) ∧ (∀ i, f (g i) = i) then
            some ⟨f, g, hi.1, hi.2⟩
          else none
        else none
      else none
    else none
  else none

structure Solution (reach height : Nat) (word target : Fin size → α) where
  assignment : Equiv.Perm (Fin size)
  allowed : ∀ index, EndpointAllowed reach height word target index (assignment index)
  dual : WeightDual size
  valid : dual.Valid reach height word target
  attains : dual.bound = weightScore height assignment

def check [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (assignment : Equiv.Perm (Fin size)) (dual : WeightDual size) :
    Option (Solution reach height word target) :=
  if ha : ∀ index, EndpointAllowed reach height word target index (assignment index) then
    if hv : dual.Valid reach height word target then
      if he : dual.bound = weightScore height assignment then
        some ⟨assignment, ha, dual, hv, he⟩
      else none
    else none
  else none

-- Some contains a proof of the minimum. None does not prove infeasibility.
-- Total success for feasible words still needs an SSP invariant proof.
def solve [DecidableEq α] (reach height : Nat) (word target : Fin size → α) :
    Option (Solution reach height word target) := do
  let graph := network reach height word target
  let flow ← run graph size
  let (forward, backward) ← decode graph flow size
  let assignment ← checkedPermutation size forward backward
  let dual : WeightDual size := ⟨fun i => -flow.potential[i.val]!,
    fun i => flow.potential[size + i.val]!⟩
  check reach height word target assignment dual

theorem Solution.minimum (result : Solution (size := size) reach height word target)
    (other : Equiv.Perm (Fin size))
    (hallowed : ∀ index, EndpointAllowed reach height word target index (other index)) :
    weightScore height result.assignment ≤ weightScore height other :=
  result.dual.minimum result.valid result.attains other hallowed

end Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver
