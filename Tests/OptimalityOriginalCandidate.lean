import Shuffler.Optimality.Schedule.Build

open Shuffler.Optimality

namespace OptimalityOriginalCandidateTests

private def zero : Value := .Lit 0
private def one : Value := .Lit 1
private def hard : Value := .Var ⟨42⟩
private def wide : Value := .Lit (2 ^ 248)
private def source : Stack :=
  [zero,one,zero,zero,zero,one,zero,hard,hard,zero,one,zero,zero,wide,zero,zero]
private def target : Stack :=
  [one,one,zero,hard,zero,one,zero,zero,zero,wide,one,zero,zero,hard,zero,zero,zero,zero,zero]
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun value => if value = zero then .push0 else if value = wide then .push ⟨31,by decide⟩
    else .push ⟨0,by decide⟩)
  (fun _ => .push ⟨1,by decide⟩)

-- The nine scheduler policies score166. Original BBU scores160.
#guard (Schedule.build costs ⟨5,1,by decide⟩ {⟨44⟩} source target {one,zero,zero}).map
  (fun result => (traceCost costs result.trace).score ⟨5,1,by decide⟩) = some 160

#guard (Schedule.originalCandidate {⟨44⟩} source target {one,zero,zero}).map
  (fun result => (traceCost costs result.trace).score ⟨5,1,by decide⟩) = some 160

-- Other candidates can still improve a successful original call.
#guard (Schedule.originalCandidate ∅ [zero] [zero,zero] {zero}).map
  (fun result => traceCost costs result.trace) = some ⟨3,1⟩
#guard (Schedule.build costs .gasOnly ∅ [zero] [zero,zero] {zero}).map
  (fun result => traceCost costs result.trace) = some ⟨2,1⟩

-- A wildcard pattern is not a concrete zero endpoint. The checked
-- candidate must reject this input.
#guard (Schedule.originalCandidate ∅ [zero] [.Wildcard] 0).isNone

-- Cardinality alone does not establish the requested additions.
#guard (Schedule.originalCandidate ∅ [zero] [zero,zero] {one}).isNone

#guard (Schedule.originalCandidate ∅
  ([hard] ++ List.replicate 17 zero) (List.replicate 17 zero ++ [hard]) 0).isNone

end OptimalityOriginalCandidateTests
