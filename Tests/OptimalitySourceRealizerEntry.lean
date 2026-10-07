import Shuffler.Optimality.BirthPlacement.SourceEntry

namespace Tests.OptimalitySourceRealizerEntry

open Shuffler.Optimality.BirthPlacement

private def closedPlan : SourcePlan ∅ [.Lit 1, .Lit 0, .Lit 2] [.Lit 0, .Lit 1, .Lit 2] where
  source_length := by decide
  assignment := Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method _ := .direct
  available index := by have := index.isLt; simp at this

-- A source-only two-cycle below the top needs three top SWAPs.
#guard (SourceEntry.build closedPlan).built.trace.swapCount = 3
#guard (SourceEntry.build closedPlan).built.trace.additions = 0

private def emptyPlan : SourcePlan ∅ [] [] where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method _ := .direct
  available index := by have := index.isLt; simp at this

#guard (SourceEntry.build emptyPlan).built.trace.swapCount = 0

private def openPlan : SourcePlan ∅ [.Lit 3, .Lit 0, .Lit 2]
    [.Lit 0, .Lit 1, .Lit 2, .Lit 3] where
  source_length := by decide
  assignment := Equiv.swap (⟨0, by decide⟩ : Fin 4) ⟨3, by decide⟩ *
    Equiv.swap (⟨3, by decide⟩ : Fin 4) ⟨1, by decide⟩
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method _ := .direct
  available := by decide

-- Future token3 stays outside the source domain. Only the source prefix is permuted.
#guard (SourceEntry.build openPlan).built.trace.swapCount = 3
#guard prefixValues [.Lit 0, .Lit 1, .Lit 2, .Lit 3]
  (SourcePrefix.run openPlan.assignment 3).permutation 3 = [.Lit 0, .Lit 3, .Lit 2]

private def boundaryTarget : Stack := List.replicate 18 (.Lit 0)
private def boundaryAssignment : Equiv.Perm (Fin boundaryTarget.length) :=
  Equiv.swap ⟨1, by decide⟩ ⟨17, by decide⟩
private def boundaryPlan : SourcePlan ∅ boundaryTarget boundaryTarget where
  source_length := by decide
  assignment := boundaryAssignment
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method _ := .direct
  available index := by have := index.isLt; simp [boundaryTarget] at this

-- At source height18, position1 is exactly SWAP16 away and remains reachable.
#guard (SourceEntry.build boundaryPlan).built.trace.swapCount = 1
#guard SourceEntry.permutation boundaryPlan ⟨1, by decide⟩ = ⟨17, by decide⟩

-- Position0 at that height would require SWAP17. The source-frozen field rejects it.
#guard ¬ (∀ index : Fin boundaryTarget.length, index.val + 17 < boundaryTarget.length →
  Equiv.swap (⟨0, by decide⟩ : Fin boundaryTarget.length) ⟨17, by decide⟩ index = index)

example (plan : SourcePlan spills source target) :
    (SourceEntry.build plan).built.trace.swapCount =
      sourceEntryCost plan.assignment source.length plan.source_length :=
  (SourceEntry.build plan).count

end Tests.OptimalitySourceRealizerEntry
