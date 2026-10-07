import Shuffler.Optimality.GroupEntry.CertificateDefs

namespace Shuffler.Optimality.GroupEntry

-- The cut is confined to unlabelled values. Thus its entry cost can be added
-- to all closed-group costs in the underlying certificate.
structure TopCutCertificate (cert : Certificate source target missing) where
  inside : Value → Bool
  nonempty : 0 < source.length
  source_none : ∀ i : Fin source.length, inside source[i] → cert.label source[i] = none
  top_outside : ¬inside (source[source.length - 1]'(by have := nonempty; omega))
  target_closed : ∀ i : Fin (source.length - 1),
    inside (source[i.val]'(by have := i.isLt; omega)) →
      inside (target[i.val]'(by have := i.isLt; have := cert.length_le; omega))
  target_top_inside : inside (target[source.length - 1]'(by have := nonempty; have := cert.length_le; omega))

def topCutCertificate (cert : Certificate source target missing) (inside : Value → Bool) :
    Option (TopCutCertificate cert) :=
  if hn : 0 < source.length then
    if hs : ∀ i : Fin source.length, inside source[i] → cert.label source[i] = none then
      if ho : ¬inside (source[source.length - 1]'(by omega)) then
        if hc : ∀ i : Fin (source.length - 1),
            inside (source[i.val]'(by have := i.isLt; omega)) →
              inside (target[i.val]'(by have := i.isLt; have := cert.length_le; omega)) then
          if ht : inside (target[source.length - 1]'(by have := cert.length_le; omega)) then
            some ⟨inside, hn, hs, ho, hc, ht⟩
          else none
        else none
      else none
    else none
  else none

def cutSlots (source : Stack) (inside : Value → Bool) : Finset Nat :=
  (Finset.range (source.length - 1)).filter fun i => (source[i]?).any inside

def extendedSlots (source : Stack) (label : Value → Option (Fin groups))
    (group : Option (Fin groups)) : Finset Nat :=
  match group with
  | none => slots source label none ∪ {source.length - 1}
  | some group => slots source label (some group)

end Shuffler.Optimality.GroupEntry
