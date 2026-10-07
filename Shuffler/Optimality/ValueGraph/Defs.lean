import Shuffler.Permute.Defs
import Mathlib.GroupTheory.Perm.List

/-!
An executable occurrence assignment for the no-growth placement problem.
Each mismatched movable position is an edge from its source value to its target
value. Hierholzer's traversal gives a circuit in each balanced value component.
Reversing the circuit gives the corresponding cycle of occurrence destinations.

The correct top position joins its value component when that component has an
edge. Equal occurrences can thus change roles and remove an entry/exit swap.
The checked wrapper returns only production traces with the exact endpoint.

The complete construction is proved in `ValueGraph.lean`: it succeeds exactly
when `Reserve` holds with no additions. The certified entry point also proves minimum
SWAP count over all value-correct traces with no POP and no additions. This
gives minimum weighted cost for every primitive cost model.
-/

namespace Shuffler.Optimality.ValueGraph

section Euler

variable {ι ν : Type} [DecidableEq ι] [DecidableEq ν]

-- The pending list is a path of vertices with their incoming edges. Each
-- step either removes an unused edge or removes a pending path entry.
def walk (start finish : ι → ν) : Nat → List (ν × Option ι) →
    List ι → List ι → List ι × List ι
  | 0, _, remaining, circuit => (circuit, remaining)
  | _ + 1, [], remaining, circuit => (circuit, remaining)
  | fuel + 1, (vertex, incoming) :: pending, remaining, circuit =>
      match remaining.find? (fun edge => start edge = vertex) with
      | some edge =>
          walk start finish fuel ((finish edge, some edge) :: (vertex, incoming) :: pending)
            (remaining.erase edge) circuit
      | none =>
          walk start finish fuel pending remaining (incoming.toList ++ circuit)

def tour (start finish : ι → ν) (first : ι) (edges : List ι) : List ι × List ι :=
  walk start finish (2 * edges.length + 1) [(start first, none)] edges []

def decompose (start finish : ι → ν) : Nat → List ι → List (List ι)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, first :: rest =>
      let result := tour start finish first (first :: rest)
      result.1 :: decompose start finish fuel result.2

end Euler

def mismatches (source target : Stack) (hlen : source.length = target.length) :
    List (Fin source.length) :=
  (List.finRange source.length).filter fun i =>
    i.rev.val ≤ MAX_SWAP_DEPTH ∧ source[i] ≠ target[i.val]'(by omega)

-- A correct top can be a useful temporary occurrence of a value already in
-- the graph. Include its self-loop exactly in that case.
def edges (source target : Stack) (hlen : source.length = target.length) :
    List (Fin source.length) :=
  let remaining := mismatches source target hlen
  if hn : 0 < source.length then
    let top : Fin source.length := ⟨source.length - 1, by omega⟩
    if source[top] = target[top.val]'(by omega) ∧
        remaining.any (fun i => source[i] = source[top] ∨
          target[i.val]'(by omega) = source[top]) then
      remaining ++ [top]
    else remaining
  else remaining

def circuits (source target : Stack) (hlen : source.length = target.length) :
    List (List (Fin source.length)) :=
  let positions := edges source target hlen
  decompose (fun i => source[i]) (fun i => target[i.val]'(by omega))
    positions.length positions

def assignment (source target : Stack) (hlen : source.length = target.length) :
    Shuffler.Permute.Permutation source :=
  (((circuits source target hlen).map List.formPerm).prod).symm

end Shuffler.Optimality.ValueGraph
