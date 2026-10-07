import Shuffler.Optimality.GroupEntry.TopCutDefs
import Shuffler.Optimality.GroupEntry.CorrectBoundaryDefs
import Shuffler.Optimality.OldPositions.Defs
import Shuffler.Feasibility.Spec

namespace Shuffler.Optimality.GroupEntry

private def neighbors (edges : List (Value × Value)) (value : Value) : List Value :=
  (edges.flatMap fun edge =>
    (if edge.1 = value then [edge.2] else []) ++
      (if edge.2 = value then [edge.1] else [])).dedup

private def visit (edges : List (Value × Value)) : Nat → List Value → List Value → List Value
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, value :: pending, seen =>
      let visited := value :: seen
      let fresh := (neighbors edges value).filter fun next =>
        !decide (next ∈ visited ∨ next ∈ pending)
      visit edges fuel (pending ++ fresh) visited

private def components (edges : List (Value × Value)) : Nat → List Value → List (List Value)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, first :: rest =>
      let component := visit edges (2 * edges.length + 1) [first] []
      component :: components edges fuel (rest.filter fun value => !decide (value ∈ component))

-- Only the movable window is needed to propose labels. The certificate
-- checks every old position, including the frozen prefix. A missed group
-- can reduce this bound but cannot make an invalid label certificate pass.
def candidateGroups (source target : Stack) (missing : Multiset Value) : List (List Value) :=
  let edges := (List.zip (Shuffler.Placement.window source)
    (target.drop (Shuffler.Placement.frozen source))).filter fun edge => edge.1 ≠ edge.2
  let values := (edges.flatMap fun edge => [edge.1, edge.2]).dedup
  (components edges values.length values).filter fun group =>
    !group.any (fun value => source.getLast? = some value ∨ value ∈ missing)

def labels (groups : List (List Value)) (value : Value) : Option (Fin groups.length) :=
  (List.finRange groups.length).find? fun group => value ∈ groups[group]

def checked (source target : Stack) (missing : Multiset Value) : Option (Certificate source target missing) :=
  let groups := candidateGroups source target missing
  certificate source target missing groups.length (labels groups)

private def forwardVisit (edges : List (Value × Value)) : Nat → List Value → List Value → List Value
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, value :: pending, seen =>
      let visited := value :: seen
      let fresh := ((edges.filterMap fun edge => if edge.1 = value then some edge.2 else none).dedup).filter
        fun next => !decide (next ∈ visited ∨ next ∈ pending)
      forwardVisit edges fuel (pending ++ fresh) visited

-- Reach forward from the wanted old-top value along old-position edges.
-- A cut is useful only when it excludes the old source top. The finite
-- certificate checks this and every closure condition before use.
def checkedTopCut (cert : Certificate source target missing) : Option (TopCutCertificate cert) :=
  let edges := List.zip (source.take (source.length - 1)) target
  let cut := forwardVisit edges (2 * edges.length + 1) (target[source.length - 1]?).toList []
  topCutCertificate cert (fun value => decide (value ∈ cut))

def requiredSwaps (source target : Stack) (missing : Multiset Value) : Nat :=
  max (correctBoundaryBound source target missing)
    (max (OldPositions.requiredSwaps source target)
      (match checked source target missing with
        | none => 0
        | some cert => (OldPositions.mismatches source target).card + cert.groups +
            if (checkedTopCut cert).isSome then 1 else 0))

def bound (costs : PrimitiveCosts) (weights : Weights)
    (source target : Stack) (missing : Multiset Value) : Nat :=
  costs.swap.score weights * requiredSwaps source target missing

end Shuffler.Optimality.GroupEntry
