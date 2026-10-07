import Shuffler.Optimality.Collective.OneGap.Theorems

namespace Tests.OptimalityOneGap

open Shuffler.Optimality.Collective.OneGap

private def a : Value := .Lit 0
private def b : Value := .Lit 1
private def c : Value := .Lit 2
private def d : Value := .Lit 3
private def sample : Stack := [a, b, b, c, a]
private def last : Fin sample.length := ⟨4, by decide⟩

#guard Family sample 2 last
#guard IsRoot (fun index => sample[index]) ⟨1, by decide⟩
#guard ¬IsRoot (fun index => sample[index]) ⟨2, by decide⟩
#guard (firstOccurrence (fun index => sample[index]) ⟨2, by decide⟩).val = 1
#guard CarrierSlots (fun index => sample[index]) 2 last ⟨1, by decide⟩ (some ⟨3, by decide⟩)
#guard ¬CarrierSlots (fun index => sample[index]) 2 last ⟨1, by decide⟩ none
#guard ¬CarrierSlots (fun index => sample[index]) 2 last ⟨2, by decide⟩ (some ⟨3, by decide⟩)
#guard birthWord sample last ⟨1, by decide⟩ (some ⟨3, by decide⟩) = [a, a, b, b, c]

example : ∃ prefetch middle, CarrierSlots (fun index => sample[index]) 2 last prefetch middle :=
  Family.exists_carrierSlots (by decide : Family sample 2 last)

private def oneHop : Stack := [a, b, c, a]
#guard Family oneHop 2 ⟨3, by decide⟩
#guard CarrierSlots (fun index => oneHop[index]) 2 ⟨3, by decide⟩ ⟨2, by decide⟩ none
#guard birthWord oneHop ⟨3, by decide⟩ ⟨2, by decide⟩ none = [a, b, a, c]

-- The two delayed target values can be equal. A separate recent copy
-- at position six keeps d readable after the first carrier hop.
private def equalDelayed : Stack := [a, b, c, d, b, c, d, d, a]
#guard Family equalDelayed 4 ⟨8, by decide⟩
#guard CarrierSlots (fun index => equalDelayed[index]) 4 ⟨8, by decide⟩
  ⟨3, by decide⟩ (some ⟨7, by decide⟩)
#guard RecentCopy (fun index => equalDelayed[index]) 4 ⟨7, by decide⟩
#guard birthWord equalDelayed ⟨8, by decide⟩ ⟨3, by decide⟩ (some ⟨7, by decide⟩) =
  [a, b, c, a, b, c, d, d, d]

-- A second gap at the reach bound is allowed.
#guard Family [a, b, c, d, b, a] 3 ⟨5, by decide⟩

-- The stated family excludes both a third a and a second long gap.
#guard ¬Family [a, a, b, c, a] 2 ⟨4, by decide⟩
#guard ¬Family [a, b, c, d, c, b, a] 3 ⟨6, by decide⟩

end Tests.OptimalityOneGap
