import Shuffler.Optimality.GroupEntry.Defs
import Mathlib.Data.List.FinRange

namespace Shuffler.Optimality.GroupEntry

-- Each `some group` label marks one closed value group. The `none` label
-- holds all remaining values, including the initial top and every birth.
structure Certificate (source target : Stack) (missing : Multiset Value) where
  groups : Nat
  label : Value → Option (Fin groups)
  length_le : source.length ≤ target.length
  top_none : ∀ i : Fin source.length, i.val + 1 = source.length → label source[i] = none
  position_label : ∀ i : Fin source.length,
    label source[i] = label (target[i.val]'(by omega))
  additions_none : ∀ value ∈ missing, label value = none
  representative : Fin groups → Fin (source.length - 1)
  representative_label : ∀ group,
    label (source[(representative group).val]'(by have := (representative group).isLt; omega)) = some group
  representative_mismatch : ∀ group,
    source[(representative group).val]'(by have := (representative group).isLt; omega) ≠
      target[(representative group).val]'(by have := (representative group).isLt; omega)

def slots (source : Stack) (label : Value → Option (Fin groups)) (group : Option (Fin groups)) : Finset Nat :=
  (Finset.range (source.length - 1)).filter fun i => (source[i]?).bind label = group

-- The check uses only finite initial-state data. It makes no claim about how
-- the caller found the labels.
def certificate (source target : Stack) (missing : Multiset Value) (groups : Nat)
    (label : Value → Option (Fin groups)) : Option (Certificate source target missing) :=
  if hl : source.length ≤ target.length then
    if ht : ∀ i : Fin source.length, i.val + 1 = source.length → label source[i] = none then
      if hs : ∀ i : Fin source.length, label source[i] = label (target[i.val]'(by omega)) then
        if ha : ∀ value ∈ missing, label value = none then
          let pick := fun group => (List.finRange (source.length - 1)).find? fun i =>
            label (source[i.val]'(by have := i.isLt; omega)) = some group ∧
              source[i.val]'(by have := i.isLt; omega) ≠ target[i.val]'(by have := i.isLt; omega)
          if hp : ∀ group, (pick group).isSome then
            let representative := fun group => (pick group).get (hp group)
            if hr : ∀ group,
                label (source[(representative group).val]'(by have := (representative group).isLt; omega)) = some group ∧
                source[(representative group).val]'(by have := (representative group).isLt; omega) ≠
                  target[(representative group).val]'(by have := (representative group).isLt; omega) then
              some ⟨groups, label, hl, ht, hs, ha, representative, fun group => (hr group).1,
                fun group => (hr group).2⟩
            else none
          else none
        else none
      else none
    else none
  else none

end Shuffler.Optimality.GroupEntry
