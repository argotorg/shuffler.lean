import Shuffler.Optimality.BirthPlacement.Dual.Source
import Shuffler.Optimality.Replay.Cost

namespace Tests.OptimalitySourceDual

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement Dual

set_option maxRecDepth 8192

-- The saved source case has baseline 66 and schedule score 81.
private def source : Stack := [.Lit 0, .Lit 0, .Var ⟨42⟩, .Lit 1, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0]
private def target : Stack := [.Lit 0, .Lit 0, .Lit 1, .Var ⟨42⟩, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 1, .Var ⟨42⟩]
private def missing : Multiset Value := ([.Lit 1, .Var ⟨42⟩, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0, .Lit 0] : Stack)
private def spills : SpillSet := {⟨44⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun value => if value = .Lit 0 then .push0 else .push 0) (fun _ => .push0)
private def ops : List Op := [.push (.Lit 0), .swap 15, .swap 16, .dup 1, .swap 16, .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .swap 16, .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 0), .push (.Lit 1), .push (.Lit 0), .swap 15]
private def witness := (replayExact spills source target missing ops).get (by decide)

-- Only the hard variable gap has a nonzero quota multiplier.
private def gaps : Fin 1 → Gap := fun _ => ⟨.Var ⟨42⟩, 19, 2, 0⟩
private def certificate : Certificate target.length 1 where
  scale := 1
  row := ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -6]
  column := ![0, 3, 0, 9, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 9]
  quotaWeight := ![9]
  capWeight := ![0]

set_option maxHeartbeats 800000 in
private theorem valid : certificate.ValidOn gaps (costs.swap.score .gasOnly)
    (sourceAllowed source target) := by decide

private theorem witnessScore : (traceCost costs witness.trace).score .gasOnly = 81 := by
  rw [replayExact_cost costs spills source target missing ops witness (Option.some_get _).symm]
  decide

example : sourceBaseline costs .gasOnly spills source target = 66 := by decide
example : certificate.lowerNumerator gaps (sourceBaseline costs .gasOnly spills source target)
    (costs.swap.score .gasOnly) = 147 := by decide

private theorem quotas (plan : SourcePlan spills source target) (gap : Fin 1) :
    (gaps gap).required ≤ prefixCount target (gaps gap) plan.assignment := by
  have h := sourcePlan_mandatoryGap plan (.Var ⟨42⟩) (by decide) 3 ⟨49, by decide⟩
    (by decide) (by decide) (by decide)
  exact h

example (other : Trace spills source target) (hpop : other.noPop) :
    (traceCost costs witness.trace).score .gasOnly - sourceBaseline costs .gasOnly spills source target ≤
      2 * ((traceCost costs other).score .gasOnly - sourceBaseline costs .gasOnly spills source target) :=
  certificate.source_surplus_le_twice costs .gasOnly valid quotas witness.trace
    (by rw [witnessScore]; decide) other hpop

example : ¬(certificate.scale * (2 * (traceCost costs witness.trace).score .gasOnly : Nat) ≤
    certificate.lowerNumerator gaps (sourceBaseline costs .gasOnly spills source target)
      (costs.swap.score .gasOnly)) := by
  rw [witnessScore]
  decide

end Tests.OptimalitySourceDual
