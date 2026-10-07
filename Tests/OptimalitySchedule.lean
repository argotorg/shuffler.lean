import Shuffler.Optimality.Schedule.Theorems

open Shuffler.Optimality

namespace OptimalityScheduleTests

private def a : Value := .Var ⟨1⟩
private def b : Value := .Var ⟨2⟩
private def c : Value := .Var ⟨3⟩
private def zero : Value := .Lit 0
private def wide : Value := .Lit (2 ^ 248)

private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun value => if value = zero then .push0
    else if value = wide then .push ⟨31, by decide⟩ else .push ⟨0, by decide⟩)
  (fun _ => .push ⟨0, by decide⟩)

private def candidateCost (weights : Weights) (spills : SpillSet)
    (source target : Stack) (missing : Multiset Value) : Option Cost :=
  (Schedule.candidate .balanced costs weights spills source target missing).map fun result =>
    traceCost costs result.trace

-- Both traces have the same target and additions. Portfolio ties use the
-- unweighted cost as well, so candidate order cannot select a dominated trace.
private def compareOps (weights : Weights) (value : Value)
    (first second : List Op) : Option Cost := do
  let a ← replayExact ∅ [value] [value,value] {value} first
  let b ← replayExact ∅ [value] [value,value] {value} second
  return traceCost costs (Schedule.cheaper costs weights a b).trace

#guard compareOps .bytesOnly zero [.dup 1] [.push zero] = some ⟨2,1⟩
#guard compareOps .bytesOnly zero [.push zero] [.dup 1] = some ⟨2,1⟩
#guard compareOps .gasOnly wide [.push wide] [.dup 1] = some ⟨3,1⟩
#guard compareOps .gasOnly wide [.dup 1] [.push wide] = some ⟨3,1⟩

-- A swap before birth and a swap after birth are both required by examples.
#guard candidateCost .bytesOnly ∅ [a,b] [b,a,a] {a} = some ⟨6,2⟩
#guard candidateCost .bytesOnly ∅ [a,b] [a,a,b] {a} = some ⟨6,2⟩

-- A complete old top cycle can be cheaper before the next birth.
#guard candidateCost .bytesOnly ∅ [a,b,c] [b,c,a,zero] {zero} = some ⟨8,3⟩

-- The first generated value is b, although the first target value is c.
#guard candidateCost .bytesOnly {⟨2⟩,⟨3⟩} [a] [c,b,a] {b,c} = some ⟨15,7⟩

private def sourceWide : Stack := [wide] ++ List.replicate 15 zero
private def targetWide : Stack := [wide] ++ List.replicate 32 zero ++ [wide]
private def missingWide : Multiset Value := (List.replicate 17 zero ++ [wide] : Stack)

private def shortTargetWide : Stack := [wide] ++ List.replicate 16 zero ++ [wide]

#guard candidateCost .bytesOnly ∅ sourceWide shortTargetWide {zero,wide} = some ⟨8,3⟩
#guard candidateCost ⟨32,3,by decide⟩ ∅ sourceWide shortTargetWide {zero,wide} = some ⟨5,34⟩
#guard candidateCost ⟨30,3,by decide⟩ ∅ sourceWide shortTargetWide {zero,wide} = some ⟨8,3⟩
#guard (Schedule.appendCandidate costs .bytesOnly ∅ sourceWide shortTargetWide {zero,wide}).map
    (fun result => traceCost costs result.trace) = some ⟨5,34⟩

-- Regeneration and copying win under different weights at the actual reach limit.
#guard candidateCost .bytesOnly ∅ sourceWide targetWide missingWide = some ⟨43,20⟩
#guard candidateCost .gasOnly ∅ sourceWide targetWide missingWide = some ⟨37,50⟩
#guard candidateCost ⟨6,1,by decide⟩ ∅ sourceWide targetWide missingWide = some ⟨37,50⟩

-- The lower swap count would require three loads instead of one.
#guard candidateCost .gasOnly {⟨1⟩,⟨3⟩}
    ([a,b] ++ List.replicate 14 zero) ([a,a] ++ List.replicate 14 zero ++ [c,b,a])
    {a,a,c} = some ⟨18,7⟩

-- Oracle regressions: retain the top as a cycle pivot, and reuse a loaded kind.
#guard candidateCost ⟨6,1,by decide⟩ {⟨1⟩,⟨2⟩} [b,a] [a,a,b,zero] {a,zero} = some ⟨8,3⟩
#guard candidateCost ⟨1,1,by decide⟩ {⟨1⟩,⟨2⟩} [zero] [a,zero,a,b] {a,a,b} = some ⟨18,8⟩

-- A future birth cannot enter a component after its first slot freezes.
-- Copying the cheap literal first also preserves the wide literal source.
#guard candidateCost ⟨1,1,by decide⟩ ∅
    ([wide,.Lit 1] ++ List.replicate 14 zero)
    ([.Lit 1,wide] ++ List.replicate 15 zero ++ [.Lit 1,wide])
    {zero,wide,.Lit 1} = some ⟨17,6⟩

-- An attached old cycle must join the top cycle before the next birth.
#guard candidateCost ⟨1,1,by decide⟩ ∅
    ([b,zero,a,c] ++ List.replicate 12 zero ++ [a])
    ([a,.Lit 3,c,a] ++ List.replicate 12 zero ++ [b,zero])
    {.Lit 3} = some ⟨15,6⟩

-- Keeping the narrow literal would use two more swaps than regenerating it.
#guard (Schedule.build costs ⟨6,1,by decide⟩ ∅
    ([wide,.Lit 1] ++ List.replicate 14 zero)
    ([.Lit 1,wide] ++ List.replicate 31 zero ++ [wide,.Lit 1])
    ((List.replicate 17 zero ++ [wide,.Lit 1] : Stack) : Multiset Value)).map
    (fun result => traceCost costs result.trace) = some ⟨52,24⟩

-- Equal gas at the lineage bound does not imply equal byte cost. Continue
-- the endpoint portfolio so one DUP plus one SWAP can replace the LOAD.
#guard (Schedule.appendCandidate costs .gasOnly {⟨1⟩}
    ([a] ++ List.replicate 15 zero) ([a] ++ List.replicate 16 zero ++ [a]) {zero,a}).map
    (fun result => traceCost costs result.trace) = some ⟨8,4⟩
#guard (Schedule.build costs .gasOnly {⟨1⟩}
    ([a] ++ List.replicate 15 zero) ([a] ++ List.replicate 16 zero ++ [a]) {zero,a}).map
    (fun result => traceCost costs result.trace) = some ⟨8,3⟩

-- The top value can close an old circuit even when its own target differs.
-- Resolve that circuit before the next birth removes the available pivot.
#guard Schedule.topValueCycles [a,b,b] [b,a,zero] = [[.swap 2,.swap 1]]
#guard Schedule.topValueCycles [a,b] [b,zero] = []
#guard (Schedule.build costs .gasOnly ∅
    ([a,b] ++ List.replicate 14 zero)
    ([b,a] ++ List.replicate 15 zero ++ [a,b]) {zero,a,b}).map
    (fun result => traceCost costs result.trace) = some ⟨17,6⟩

-- The complete wrapper retains a zero-operation identity candidate.
#guard (Schedule.build costs .bytesOnly ∅ [a,b] [a,b] 0).map
    (fun result => traceCost costs result.trace) = some Cost.zero

-- Equal counts do not make a changed frozen position reachable.
#guard (Schedule.build costs .bytesOnly ∅
    ([wide] ++ List.replicate 17 zero) (List.replicate 17 zero ++ [wide]) 0).isNone

-- One hard source cannot supply both the frozen output and a later copy.
#guard (Schedule.build costs .bytesOnly ∅
    ([a] ++ List.replicate 16 zero) ([a] ++ List.replicate 16 zero ++ [a]) {a}).isNone

end OptimalityScheduleTests
