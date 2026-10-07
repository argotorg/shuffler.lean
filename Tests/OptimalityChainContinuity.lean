import Shuffler.Optimality.Schedule.Soundness
import Shuffler.Optimality.GroupEntry.CorrectBoundaryDefs

open Shuffler.Optimality

namespace OptimalityChainContinuityTests

private def v (n : Nat) : Value := .Var ⟨n⟩
private def zero : Value := .Lit 0
private def one : Value := .Lit 1
private def narrow : Value := .Lit 256
private def wide : Value := .Lit (2 ^ 248)
private def source : Stack :=
  [zero,zero,one,narrow,wide] ++ (List.range 13).map (fun n => v (n + 100))
private def target : Stack := [zero,v 112,zero,one,narrow,wide] ++
  (List.range 6).map (fun n => v (n + 100)) ++
  (List.range 5).map (fun n => v (n + 107)) ++ [one,v 100,v 104,v 106,v 106]
private def missing : Multiset Value := {one,v 100,v 104,v 106}
private def spills : SpillSet := {⟨101⟩,⟨104⟩,⟨105⟩,⟨108⟩,⟨110⟩,⟨111⟩,⟨114⟩,⟨115⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun value => if value = zero then .push0 else if value = wide then .push ⟨31,by decide⟩
    else if value = narrow then .push ⟨1,by decide⟩ else .push ⟨0,by decide⟩)
  (fun id => if id = ⟨104⟩ || id = ⟨114⟩ then .push ⟨31,by decide⟩
    else if id = ⟨108⟩ || id = ⟨110⟩ then .push0
    else if id = ⟨115⟩ then .push ⟨0,by decide⟩ else .push ⟨1,by decide⟩)

-- Four births cost 12. The certified eleven-SWAP witness has total cost 45.
-- The nine raw policies choose the next matched birth and use sixteen SWAPs.
#guard (Schedule.build costs .gasOnly spills source target missing).map
  (fun result => traceCost costs result.trace) = some ⟨45,15⟩

private def previousStrategies : List Schedule.Strategy :=
  let policies : List Schedule.Strategy := [.balanced,.eager,.preserve]
  policies.map (·.withMode .relaxed) ++ policies ++ policies.map (·.withMode .chains)

#guard (Schedule.buildWith previousStrategies costs .gasOnly spills source target missing).map
  (fun result => traceCost costs result.trace) = some ⟨48,49⟩

-- This control runs the actual raw policies, before portfolio normalization.
#guard previousStrategies.map (fun strategy =>
  (Schedule.candidate strategy costs .gasOnly spills source target missing).map
    (fun result => (traceCost costs result.trace).gas)) = List.replicate 9 (some 60)

#guard baseline costs .gasOnly spills source missing = 12
#guard staticExcess costs .gasOnly spills source target missing = 33

-- The first changed birth still permits the certified optimal cost.
private def delayedChain : List Op :=
  [.swap 16,.swap 15,.dup 13,.dup 2,.swap 16,.swap 15,.swap 14,.swap 13,
    .swap 12,.swap 11,.swap 10,.dup 1,.swap 10,.swap 9,.dup 1]

#guard (replayExact spills source target missing delayedChain).map
  (fun result => traceCost costs result.trace) = some ⟨45,15⟩

-- The second changed birth forces eleven more SWAPs.
private def badPrefix : List Op := [.swap 16,.swap 15,.dup 13,.dup 10]
private def residualMissing : Multiset Value := {one,v 106}
private def tightResidual : List Op :=
  [.swap 2,.swap 16,.swap 15,.swap 14,.swap 13,.swap 12,.swap 11,.swap 10,
    .push one,.swap 3,.swap 10,.swap 9,.dup 1]

#guard (Schedule.simulate spills source badPrefix).map
  (fun residual => GroupEntry.correctBoundaryBound residual target residualMissing) = some 11

#guard (Schedule.simulate spills source badPrefix).bind (fun residual =>
  (replayExact spills residual target residualMissing tightResidual).map
    (fun result => traceCost costs result.trace)) = some ⟨39,14⟩

#guard !Schedule.continuesOldChain [] []
#guard !Schedule.continuesOldChain [one,one] [one,one]
#guard Schedule.continuesOldChain [zero,one,one] [one,zero,one]

end OptimalityChainContinuityTests
