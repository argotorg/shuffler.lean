import Shuffler.Optimality.ValueGraph.Defs
import Shuffler.Optimality.Cost

namespace Shuffler.Optimality.ValueGraph

-- Finite data certify a lower bound. No claim about the graph traversal is
-- trusted by this boundary: all representatives and position labels are checked.
structure LabelCertificate (source target : Stack) (hlen : source.length = target.length) where
  groups : Nat
  label : Value → Option (Fin groups)
  representative : Fin groups → Fin source.length
  representative_mismatch : ∀ group,
    source[representative group] ≠ target[(representative group).val]'(by omega)
  representative_label : ∀ group, label source[representative group] = some group
  position_label : ∀ i : Fin source.length, label source[i] = label (target[i.val]'(by omega))

def labels (source : Stack) (cycles : List (List (Fin source.length)))
    (value : Value) : Option (Fin cycles.length) :=
  (List.finRange cycles.length).find? fun group =>
    (cycles[group]).any fun position => source[position] = value

def certificate (source target : Stack) (hlen : source.length = target.length) :
    Option (LabelCertificate source target hlen) :=
  let cycles := circuits source target hlen
  let pick := fun group : Fin cycles.length =>
    (cycles[group]).find? fun position => source[position] ≠ target[position.val]'(by omega)
  if hp : ∀ group, (pick group).isSome then
    let representative := fun group => (pick group).get (hp group)
    let label := labels source cycles
    if hm : ∀ group, source[representative group] ≠ target[(representative group).val]'(by omega) then
      if hr : ∀ group, label source[representative group] = some group then
        if hs : ∀ i : Fin source.length, label source[i] = label (target[i.val]'(by omega)) then
          some ⟨cycles.length, label, representative, hm, hr, hs⟩
        else none
      else none
    else none
  else none

def mismatchPositions (source target : Stack) (hlen : source.length = target.length) :
    Finset (Fin source.length) :=
  Finset.univ.filter fun i => source[i] ≠ target[i.val]'(by omega)

def LabelCertificate.bound (cert : LabelCertificate source target hlen) (hne : 0 < source.length) : Nat :=
  let top : Fin source.length := ⟨source.length - 1, by omega⟩
  ((mismatchPositions source target hlen).erase top).card +
    (Finset.univ.filter fun group : Fin cert.groups =>
      cert.label source[cert.representative group] ≠ cert.label source[top]).card

end Shuffler.Optimality.ValueGraph
