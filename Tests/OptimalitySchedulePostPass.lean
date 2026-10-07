import Shuffler.Optimality.Schedule.PostPass.Guarantees

namespace Tests.OptimalitySchedulePostPass

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def basicCosts : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push ⟨0, by decide⟩) (fun _ => .push ⟨0, by decide⟩)

private def result (spills : SpillSet) (source : Stack) (ops : List Op) : Option (Cost × Cost) := do
  let replayed ← replay spills source ops
  let final := Schedule.postPass basicCosts .gasOnly replayed.built
  return (traceCost basicCosts replayed.built.trace, traceCost basicCosts final.trace)

-- The empty-source branch removes a redundant equal-value SWAP.
#guard result ∅ [] [.push (.Lit 1), .push (.Lit 1), .swap 1] =
  some (⟨9, 5⟩, ⟨6, 4⟩)

-- The supplied-assignment candidate can cost more; the incumbent is retained.
#guard result ∅ [.Lit 0, .Lit 1, .Lit 2] [.push (.Lit 3), .swap 2, .swap 3] =
  some (⟨9, 4⟩, ⟨9, 4⟩)

-- Source-offset method choice can replace a LOAD with a reachable DUP.
#guard result {⟨42⟩} [.Var ⟨42⟩] [.load ⟨42⟩] = some (⟨6, 3⟩, ⟨3, 1⟩)
#guard result ∅ [] [] = some (⟨0, 0⟩, ⟨0, 0⟩)

private def savedSource : Stack := [.Lit 0, .Lit 1, .Lit 256, .Lit 452312848583266388373324160190187140051835877600158453279131187530910662656, .Var ⟨100⟩, .Var ⟨101⟩, .Var ⟨102⟩, .Var ⟨103⟩, .Var ⟨104⟩, .Var ⟨105⟩, .Var ⟨106⟩, .Var ⟨107⟩, .Var ⟨108⟩, .Var ⟨109⟩, .Var ⟨110⟩, .Var ⟨111⟩]
private def savedTarget : Stack := [.Lit 0, .Lit 1, .Lit 256, .Lit 452312848583266388373324160190187140051835877600158453279131187530910662656, .Var ⟨101⟩, .Var ⟨102⟩, .Var ⟨103⟩, .Var ⟨104⟩, .Var ⟨105⟩, .Var ⟨108⟩, .Var ⟨107⟩, .Var ⟨108⟩, .Var ⟨109⟩, .Var ⟨110⟩, .Var ⟨111⟩, .Var ⟨106⟩, .Lit 1, .Lit 452312848583266388373324160190187140051835877600158453279131187530910662656, .Lit 452312848583266388373324160190187140051835877600158453279131187530910662656, .Lit 1, .Var ⟨100⟩, .Lit 1, .Lit 452312848583266388373324160190187140051835877600158453279131187530910662656, .Var ⟨100⟩, .Var ⟨100⟩, .Lit 0, .Var ⟨100⟩, .Var ⟨100⟩, .Lit 1, .Var ⟨100⟩, .Var ⟨100⟩, .Var ⟨100⟩]
private def savedOps : List Op := [.swap 1, .swap 2, .swap 3, .swap 4, .swap 5, .dup 15, .dup 14, .dup 1, .dup 3, .dup 16, .swap 15, .swap 16, .dup 2, .swap 15, .swap 16, .dup 4, .swap 15, .swap 16, .dup 2, .swap 15, .swap 16, .dup 3, .swap 15, .swap 16, .dup 14, .swap 16, .push (.Lit 0), .swap 1, .dup 1, .dup 6, .dup 2, .dup 1, .dup 1, .swap 8, .swap 9, .swap 10]

private def savedSpills : SpillSet := {⟨103⟩, ⟨104⟩, ⟨105⟩, ⟨107⟩, ⟨108⟩, ⟨115⟩}
private def savedCosts : PrimitiveCosts := PrimitiveCosts.evm
  (fun value => if value = .Lit 0 then .push0 else if value = .Lit 1 then .push ⟨0, by decide⟩
    else if value = .Lit 256 then .push ⟨1, by decide⟩ else .push ⟨31, by decide⟩)
  (fun id => if id.val = 115 then .push0 else if id.val = 105 then .push ⟨1, by decide⟩
    else .push ⟨31, by decide⟩)
private def mixedWeights : Weights := ⟨1, 1, by decide⟩

-- This is a saved v15 portfolio output, not a synthetic schedule.
#guard (replay savedSpills savedSource savedOps).map (fun replayed =>
  let final := Schedule.postPass savedCosts mixedWeights replayed.built
  (replayed.target, traceCost savedCosts replayed.built.trace, traceCost savedCosts final.trace)) =
    some (savedTarget, ⟨107, 36⟩, ⟨95, 32⟩)

example (costs : PrimitiveCosts) (weights : Weights)
    (incumbent : Shuffler.Placement.BuiltTrace spills source target missing) :
    (traceCost costs (Schedule.postPass costs weights incumbent).trace).score weights ≤
      (traceCost costs incumbent.trace).score weights := Schedule.postPass_le costs weights incumbent

example (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) :
    (Schedule.build costs weights spills source target missing).isSome ↔
      Shuffler.Placement.Reserve spills source target missing :=
  Schedule.build_succeeds_iff_reserve costs weights spills source target missing

end Tests.OptimalitySchedulePostPass
