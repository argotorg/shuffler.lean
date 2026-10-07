import Shuffler.Optimality.Schedule.Chains
import Shuffler.Optimality.Schedule.Build

open Shuffler.Optimality

namespace OptimalityOpenChainTests

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def c : Value := .Var ⟨2⟩

#guard Schedule.openChains [] [] = []
#guard Schedule.openChains [a] [b] = []
#guard Schedule.openChains [a,b,c] [a,b,c] = []
#guard Schedule.openChains [a,b,c] [b,c,.Lit 99] =
  [[.swap 1], [.swap 1,.swap 2]]

-- The fixed top position must not appear as an illegal SWAP0.
#guard Schedule.openChains [a,b,c] [b,c,c] =
  [[.swap 1], [.swap 1,.swap 2]]

private def distinct17 : Stack := (List.range 17).map (fun i => .Var ⟨i⟩)
private def rotated18 : Stack := distinct17.drop 1 ++ [.Lit 99, a]

#guard (Schedule.openChains distinct17 rotated18).getLast? =
  some ((List.range 16).map fun i => .swap (i + 1))

private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push ⟨0, by decide⟩) (fun _ => .push ⟨0, by decide⟩)

private def originalStrategies : List Schedule.Strategy :=
  let policies : List Schedule.Strategy := [.balanced,.eager,.preserve]
  policies.map (·.withMode .relaxed) ++ policies

#guard (Schedule.buildWith originalStrategies costs ⟨1,1,by decide⟩ ∅
  distinct17 rotated18 {.Lit 99}).map (fun result => result.trace.swapCount) = some 17

-- Each raw policy still has nineteen SWAPs. Normalizing candidates before
-- comparison attains the seventeen-SWAP witness even with the six policies.
#guard originalStrategies.map (fun strategy =>
  (Schedule.candidate strategy costs ⟨1,1,by decide⟩ ∅ distinct17 rotated18 {.Lit 99}).map
    (fun result => result.trace.swapCount)) = List.replicate 6 (some 19)

-- The witness SWAP1,...,SWAP16; PUSH99; SWAP1 has seventeen swaps.
#guard (Schedule.build costs ⟨1,1,by decide⟩ ∅ distinct17 rotated18 {.Lit 99}).map
  (fun result => result.trace.swapCount) = some 17

end OptimalityOpenChainTests
