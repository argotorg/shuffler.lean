import Shuffler.Optimality.FrozenPrefix.Approximation

open Shuffler.Optimality
open Shuffler.Placement

namespace OptimalityFrozenPrefixTests

private def zero : Value := .Lit 0
private def one : Value := .Lit 1
private def spills : SpillSet := {⟨7⟩}
private def working : Stack := List.replicate 17 zero
private def result : Stack := working ++ [zero,one,.Var ⟨7⟩]
private def fixed : Stack := [.Var ⟨900⟩,.Var ⟨901⟩]
private def missing : Multiset Value := {zero,one,.Var ⟨7⟩}
private def ops : List Op := [.swap 16,.dup 16,.push one,.load ⟨7⟩]

-- Exercise both maximum instruction depths, then PUSH and LOAD.
private def suffixTrace : Trace spills working result :=
  .Load ⟨7⟩ (by decide)
    (.Push one (by decide)
      (.Dup 16 (by decide) (by decide) (by decide)
        (.Swap 16 (by decide) (by decide) (by decide) (.Lit working))))

#guard flatten suffixTrace = ops
#guard suffixTrace.additions = missing
#guard traceCost (PrimitiveCosts.cppEstimate (fun _ => .push ⟨0,by decide⟩)
  (fun _ => .push ⟨0,by decide⟩)) suffixTrace = ⟨15,7⟩
#guard frozen (fixed ++ working) = fixed.length

private def wideLoadCosts : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨31,by decide⟩)

-- The only old copy is frozen. Removing it raises the baseline from a DUP
-- price to a direct LOAD price; the baseline need not stay equal.
#guard baseline wideLoadCosts .bytesOnly spills (.Var ⟨7⟩ :: working) {.Var ⟨7⟩} = 1
#guard baseline wideLoadCosts .bytesOnly spills working {.Var ⟨7⟩} = 34

example : ∃ full : Trace spills (fixed ++ working) (fixed ++ result),
    Eligible missing full ∧ flatten full = ops ∧
      ∀ costs, traceCost costs full = traceCost costs suffixTrace := by
  have he : Eligible missing suffixTrace := ⟨by trivial, by decide⟩
  obtain ⟨full, he, ho, hc⟩ := FrozenPrefix.exists_lift_eligible suffixTrace he fixed
  exact ⟨full, he, ho, hc⟩

example (full : Trace spills (fixed ++ working) (fixed ++ result))
    (he : Eligible missing full) :
    ∃ reduced : Trace spills working result, Eligible missing reduced ∧
      flatten reduced = flatten full ∧
      ∀ costs, traceCost costs reduced = traceCost costs full := by
  have h := FrozenPrefix.exists_drop_eligible full he fixed.length (by decide)
  rw [List.drop_left, List.drop_left] at h
  exact h

-- At height 17 the frozen prefix is empty. Removing one slot would make
-- this legal SWAP16 invalid on the reduced stack.
#guard frozen working = 0
#guard (replay spills (working.drop 1) [.swap 16]).isNone

-- The reduced identity trace exists, but a changed frozen value prevents
-- the corresponding full trace. Thus prefix matching cannot be omitted.
private def blockedSource : Stack := zero :: working
private def blockedTarget : Stack := one :: working

example : ¬∃ trace : Trace spills blockedSource blockedTarget,
    Eligible 0 trace ∧ flatten trace = [] := by
  intro h
  have hp := (FrozenPrefix.exists_operations_iff spills blockedSource blockedTarget
    0 1 (by decide) []).mp h
  exact (by decide : blockedTarget.take 1 ≠ blockedSource.take 1) hp.1

example : ∃ trace : Trace spills (blockedSource.drop 1) (blockedTarget.drop 1),
    Eligible 0 trace ∧ flatten trace = [] :=
  ⟨.Lit working, ⟨trivial, rfl⟩, rfl⟩

end OptimalityFrozenPrefixTests
