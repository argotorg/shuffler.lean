import Shuffler.Optimality.Collective.Intervals

namespace Shuffler.Optimality.Collective

-- Copies that cannot all have been consumed by the first cut outputs.
def mandatory (source target : Stack) (cut : Nat) : Multiset Value :=
  (source : Multiset Value) - (target.take cut : Multiset Value)

def capacity (source target : Stack) (cut : Nat) : Nat :=
  16 - (mandatory source target cut).card

-- Before this threshold, one mandatory old copy can also be the reuse seed.
-- After it, a retained copy needs a separate residual slot.
def Interval.Paid (source : Stack) (gap : Interval target) : Prop :=
  source.count gap.value ≤ (target.take (gap.start.val + 1)).count gap.value

instance (source : Stack) (gap : Interval target) : Decidable (gap.Paid source) := by
  unfold Interval.Paid
  infer_instance

end Shuffler.Optimality.Collective
