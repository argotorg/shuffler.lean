import Shuffler.Optimality.GroupEntry.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityGroupEntry

open Shuffler.Optimality

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def c : Value := .Var ⟨2⟩
private def d : Value := .Var ⟨3⟩
private def e : Value := .Var ⟨4⟩
private def zero : Value := .Lit 0
private def labelAB (value : Value) : Option (Fin 1) :=
  if value = a ∨ value = b then some ⟨0, by decide⟩ else none

#guard (GroupEntry.certificate [a, b, c] [b, a, c] 0 1 labelAB).isSome
#guard !(GroupEntry.certificate [a, b, a] [b, a, a] 0 1 labelAB).isSome
#guard !(GroupEntry.certificate [a, b, c] [a, b, c] 0 1 labelAB).isSome
#guard !(GroupEntry.certificate [a, c] [c, a] 0 1 labelAB).isSome
#guard !(GroupEntry.certificate [a, b, c] [b, a, c, a] {a} 1 labelAB).isSome
#guard !(GroupEntry.certificate [a, b, c] [b, a] 0 1 labelAB).isSome

#guard GroupEntry.requiredSwaps [] [] 0 = 0
#guard GroupEntry.requiredSwaps [a] [zero, a, a] {zero, a} = 1
#guard GroupEntry.requiredSwaps [a, b] [b, a] 0 = 1
#guard GroupEntry.requiredSwaps [a, b, a] [b, a, a] 0 = 2
#guard GroupEntry.requiredSwaps [a, b, c] [b, a, c] 0 = 3
#guard GroupEntry.requiredSwaps [a, b, c, d, e] [b, a, d, c, e] 0 = 6
#guard GroupEntry.requiredSwaps [a, b, c] [b, a, c, zero] {zero} = 3
#guard GroupEntry.requiredSwaps [a, b, c] [b, a, c, a] {a} = 2
#guard (GroupEntry.checked [a, b, c, d, e] [b, a, d, c, e] 0).map (fun cert => cert.groups) = some 2

private def exactGrowth := (replayExact ∅ [a, b, c] [b, a, c, zero] {zero}
  [.swap 2, .swap 1, .swap 2, .push zero]).get (by decide)

#guard exactGrowth.trace.swapCount = 3

private def cutBase := (GroupEntry.certificate [a, b] [zero, a, b] {zero} 0
  (fun _ => none)).get (by decide)

#guard (GroupEntry.topCutCertificate cutBase (fun value => value = a ∨ value = zero)).isSome
#guard !(GroupEntry.topCutCertificate cutBase (fun _ => true)).isSome
#guard !(GroupEntry.topCutCertificate cutBase (fun value => value = a)).isSome
#guard !(GroupEntry.topCutCertificate cutBase (fun value => value = zero)).isSome
#guard (GroupEntry.checkedTopCut cutBase).isSome

private def cyclicBase := (GroupEntry.checked [a, b] [b, a] 0).get (by decide)
#guard !(GroupEntry.checkedTopCut cyclicBase).isSome

private def emptyBase := (GroupEntry.checked [] [] 0).get (by decide)
#guard !(GroupEntry.checkedTopCut emptyBase).isSome

#guard GroupEntry.requiredSwaps [a, b] [zero, a, b] {zero} = 2
#guard GroupEntry.requiredSwaps [a, b, c, d, e] [b, a, zero, d, c, e] {zero} = 5

private def labelledBase := (GroupEntry.checked [a, b, c, d, e]
  [b, a, zero, d, c, e] {zero}).get (by decide)
#guard (GroupEntry.topCutCertificate labelledBase (fun value => value = c ∨ value = zero)).isSome
#guard !(GroupEntry.topCutCertificate labelledBase
  (fun value => value = a ∨ value = b ∨ value = c ∨ value = zero)).isSome

private def exactCut := (replayExact ∅ [a, b] [zero, a, b] {zero}
  [.swap 1, .push zero, .swap 2]).get (by decide)
private def exactCutAndGroup := (replayExact ∅ [a, b, c, d, e] [b, a, zero, d, c, e] {zero}
  [.swap 2, .push zero, .swap 3, .swap 5, .swap 4, .swap 5]).get (by decide)

#guard exactCut.trace.swapCount = 2
#guard exactCutAndGroup.trace.swapCount = 5

example : GroupEntry.requiredSwaps [a, b, c, d, e] [b, a, zero, d, c, e] {zero} ≤
    exactCutAndGroup.trace.swapCount :=
  GroupEntry.requiredSwaps_le_swapCount exactCutAndGroup.trace
    ⟨exactCutAndGroup.noPop, exactCutAndGroup.additions⟩

example : GroupEntry.requiredSwaps [a, b, c] [b, a, c, zero] {zero} ≤ exactGrowth.trace.swapCount :=
  GroupEntry.requiredSwaps_le_swapCount exactGrowth.trace ⟨exactGrowth.noPop, exactGrowth.additions⟩

example (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + GroupEntry.bound costs weights source target missing ≤
      (traceCost costs trace).score weights :=
  GroupEntry.baseline_add_bound_le_score costs weights trace he

end Tests.OptimalityGroupEntry
