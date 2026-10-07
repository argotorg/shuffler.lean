import Shuffler.Optimality.Schedule.Soundness

open Shuffler.Optimality

namespace OptimalityRawChainTests

private def zero : Value := .Lit 0
private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def source : Stack := List.replicate 15 zero
private def target : Stack := [a] ++ List.replicate 12 b ++ [a] ++ source
private def missing : Multiset Value := {a,a} + Multiset.replicate 12 b
private def spills : SpillSet := {⟨42⟩,⟨43⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨31,by decide⟩)

-- Keep b through its run, then introduce a again. This uses three LOADs,
-- eleven DUPs, and fifteen SWAPs. It is a witness, not an optimum claim.
private def witness : List Op :=
  [.load ⟨42⟩,.swap 15,.load ⟨43⟩,.dup 1] ++
    (List.range 10).flatMap (fun index => [.swap 16,.dup (index + 2)]) ++
    [.swap 16,.load ⟨42⟩,.swap 15,.swap 12,.swap 16]

#guard baseline costs .bytesOnly spills source missing = 80

#guard (replayExact spills source target missing witness).map
  (fun result => traceCost costs result.trace) = some ⟨96,128⟩

-- The raw policy keeps a through the long b run and repeatedly loads b.
#guard (Schedule.candidate .chain costs .bytesOnly spills source target missing).map
  (fun result => (traceCost costs result.trace).bytes) = some 457

-- The full portfolio keeps the original-BBU candidate and avoids this loss.
#guard (Schedule.build costs .bytesOnly spills source target missing).map
  (fun result => (traceCost costs result.trace).bytes) = some 146

-- The witness alone refutes factor two for a trace of the raw-policy cost.
-- The true optimum can only make the required upper bound smaller.
example (raw reference : Trace spills source target) (he : Eligible missing reference)
    (hr : (traceCost costs raw).bytes = 457)
    (href : (traceCost costs reference).bytes = 128) :
    ¬TwiceExcess costs .bytesOnly missing raw := by
  intro h
  have hb : baseline costs .bytesOnly spills source missing = 80 := by decide
  have hc := h.2 reference he
  simp only [Cost.score_bytesOnly, hr, href, hb] at hc
  omega

end OptimalityRawChainTests
