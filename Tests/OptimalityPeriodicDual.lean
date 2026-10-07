import Shuffler.Optimality.BirthPlacement.Dual.Trace
import Shuffler.Optimality.Replay.Cost

namespace Tests.OptimalityPeriodicDual

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement Dual

set_option maxRecDepth 8192

-- This is the saved witness from evidence-carrier-r16-relaxation-gap.json.
private def target : Stack := [.Var ⟨42⟩, .Var ⟨43⟩, .Var ⟨44⟩, .Var ⟨45⟩, .Var ⟨46⟩, .Var ⟨47⟩, .Var ⟨48⟩, .Var ⟨49⟩, .Var ⟨50⟩, .Var ⟨51⟩, .Var ⟨52⟩, .Var ⟨53⟩, .Var ⟨54⟩, .Var ⟨55⟩, .Var ⟨56⟩, .Var ⟨57⟩, .Var ⟨43⟩, .Var ⟨44⟩, .Var ⟨45⟩, .Var ⟨46⟩, .Var ⟨47⟩, .Var ⟨48⟩, .Var ⟨49⟩, .Var ⟨50⟩, .Var ⟨51⟩, .Var ⟨52⟩, .Var ⟨53⟩, .Var ⟨54⟩, .Var ⟨55⟩, .Var ⟨56⟩, .Var ⟨57⟩, .Var ⟨43⟩, .Var ⟨44⟩, .Var ⟨45⟩, .Var ⟨46⟩, .Var ⟨47⟩, .Var ⟨48⟩, .Var ⟨49⟩, .Var ⟨50⟩, .Var ⟨51⟩, .Var ⟨52⟩, .Var ⟨53⟩, .Var ⟨54⟩, .Var ⟨55⟩, .Var ⟨56⟩, .Var ⟨57⟩, .Var ⟨42⟩]
private def spills : SpillSet := {⟨42⟩, ⟨43⟩, ⟨44⟩, ⟨45⟩, ⟨46⟩, ⟨47⟩, ⟨48⟩, ⟨49⟩, ⟨50⟩, ⟨51⟩, ⟨52⟩, ⟨53⟩, ⟨54⟩, ⟨55⟩, ⟨56⟩, ⟨57⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push ⟨31, by decide⟩) (fun _ => .push ⟨31, by decide⟩)
private def ops : List Op := [.load ⟨42⟩, .load ⟨43⟩, .load ⟨44⟩, .load ⟨45⟩, .load ⟨46⟩, .load ⟨47⟩, .load ⟨48⟩, .load ⟨49⟩, .load ⟨50⟩, .load ⟨51⟩, .load ⟨52⟩, .load ⟨53⟩, .load ⟨54⟩, .load ⟨55⟩, .load ⟨56⟩, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .dup 15, .load ⟨57⟩, .dup 1, .swap 16, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1, .dup 16, .swap 1]
private def witness := (replayExact spills [] target (target : Multiset Value) ops).get (by decide)

-- These integer coefficients came from an external feasibility search.
-- Lean checks them; no claim about the external solver is used below.
private def certificate : Certificate target.length target.length where
  scale := 1
  row := ![16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
  column := ![1, 0, -2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0]
  quotaWeight := ![16, 1, 0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 14, 13, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  capWeight := ![50, 65, 66, 65, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 52, 53, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 65, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 1600000 in
private theorem valid : certificate.Valid (targetGap costs .bytesOnly spills target)
    (costs.swap.score .bytesOnly) := by decide

private theorem witnessScore : (traceCost costs witness.trace).score .bytesOnly = 591 := by
  rw [replayExact_cost costs spills [] target (target : Multiset Value) ops witness (Option.some_get _).symm]
  decide

example : baseline costs .bytesOnly spills [] (target : Multiset Value) = 575 := by decide
example : certificate.lowerNumerator (targetGap costs .bytesOnly spills target)
    (directTotal costs .bytesOnly spills target) (costs.swap.score .bytesOnly) = 1166 := by decide

-- The candidate's score plus baseline meets the dual bound. Attainment of
-- the joint plan objective is not a hypothesis of this theorem.
example (other : Trace spills [] target) (hpop : other.noPop) :
    (traceCost costs witness.trace).score .bytesOnly -
        baseline costs .bytesOnly spills [] (target : Multiset Value) ≤
      2 * ((traceCost costs other).score .bytesOnly -
        baseline costs .bytesOnly spills [] (target : Multiset Value)) :=
  certificate.surplus_le_twice costs .bytesOnly valid witness.trace
    (by rw [witnessScore]; decide) other hpop

-- This certificate does not meet the sufficient exact-score test.
example : ¬(certificate.scale * (2 * (traceCost costs witness.trace).score .bytesOnly : Nat) ≤
    certificate.lowerNumerator (targetGap costs .bytesOnly spills target)
      (directTotal costs .bytesOnly spills target) (costs.swap.score .bytesOnly)) := by
  rw [witnessScore]
  decide

end Tests.OptimalityPeriodicDual
