import Shuffler.Optimality.Collective.RetainedWithoutDirect.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityRetainedWithoutDirect

open Shuffler.Optimality Shuffler.Optimality.Collective

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def c : Value := .Var ⟨44⟩
private def spills : SpillSet := {⟨42⟩, ⟨43⟩, ⟨44⟩}
private def source : Stack := List.replicate 15 (.Lit 0)
private def target : Stack := [a,b,a,c,a] ++ source
private def missing : Multiset Value := {a,a,a,b,c}
private def ops : List Op :=
  [.load ⟨42⟩, .dup 1, .swap 16, .load ⟨43⟩, .swap 16,
    .load ⟨42⟩, .swap 16, .load ⟨44⟩, .swap 16, .swap 4, .swap 15]
private def built := (replayExact spills source target missing ops).get (by decide)

-- The first a interval has a resident seed, but another LOAD of a occurs
-- before its end cut. Only the second a interval has no direct introduction.
#guard (retained built.trace).card = 2
#guard (retainedWithoutDirect built.trace).card = 1
#guard directBefore a 1 built.trace = 1
#guard directBefore a 3 built.trace = 2
#guard directBefore a 5 built.trace = 2
#guard (paidIntervals source target \ retainedWithoutDirect built.trace).card = 1

example : FeasiblePaidIntervals source target (retainedWithoutDirect built.trace) :=
  retainedWithoutDirect_feasible built.trace built.noPop (by decide)

example : intervalCount (paidIntervals source target \ retainedWithoutDirect built.trace) a ≤
    Lineage.directCount a built.trace - 1 := by
  simpa only [show a ∉ source by decide, ite_false] using
    omitted_without_direct_count_le built.trace built.noPop a

example (costs : PrimitiveCosts) (weights : Weights) :
    intervalWeight (fun value => directPrice costs weights spills value - unitPrice costs weights spills value)
      (paidIntervals source target \ retainedWithoutDirect built.trace) ≤
        generationSurcharge costs weights target.toFinset built.trace :=
  omitted_without_direct_weight_le_generationSurcharge costs weights built.trace built.noPop

end Tests.OptimalityRetainedWithoutDirect
