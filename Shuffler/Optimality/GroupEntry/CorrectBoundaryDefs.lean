import Shuffler.Optimality.OldPositions.Defs
import Shuffler.Feasibility.Spec

namespace Shuffler.Optimality.GroupEntry

open Shuffler.Placement

def CorrectBoundary (source target : Stack) (missing : Multiset Value) (value : Value) : Prop :=
  missing ≠ 0 ∧ 17 ≤ source.length ∧
    target[frozen source]? = some value ∧ source[frozen source]? ≠ some value ∧
    source[source.length - 1]? ≠ some value ∧
    ∀ i : Fin source.length, source[i] = value → target[i.val]? = some value

instance : Decidable (CorrectBoundary source target missing value) := by
  unfold CorrectBoundary
  infer_instance

def checkedCorrectBoundary (source target : Stack) (missing : Multiset Value) :
    Option {value : Value // CorrectBoundary source target missing value} := do
  let value ← target[frozen source]?
  if h : CorrectBoundary source target missing value then some ⟨value, h⟩ else none

def correctBoundaryBound (source target : Stack) (missing : Multiset Value) : Nat :=
  if (checkedCorrectBoundary source target missing).isSome then
    (OldPositions.mismatches source target).card + 2
  else 0

end Shuffler.Optimality.GroupEntry
