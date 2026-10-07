import Shuffler.Optimality.Collective.Intervals

namespace Shuffler.Optimality.Collective.OneGap

def firstOccurrence [DecidableEq α] (values : Fin size → α) (index : Fin size) : Fin size :=
  (Finset.univ.filter fun other => values other = values index).min'
    ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

def IsRoot [DecidableEq α] (values : Fin size → α) (index : Fin size) : Prop :=
  firstOccurrence values index = index

instance [DecidableEq α] (values : Fin size → α) (index : Fin size) :
    Decidable (IsRoot values index) := by unfold IsRoot; infer_instance

def RecentCopy [DecidableEq α] (values : Fin size → α) (cut : Nat) (index : Fin size) : Prop :=
  ∃ earlier : Fin size, cut ≤ earlier.val ∧ earlier < index ∧ values earlier = values index

instance [DecidableEq α] (values : Fin size → α) (cut : Nat) (index : Fin size) :
    Decidable (RecentCopy values cut index) := by unfold RecentCopy; infer_instance

def initial (last : Fin size) : Fin size := ⟨0, Nat.zero_lt_of_lt last.isLt⟩

-- This is the restricted word shape, without any stack realization claim.
def Family (target : Stack) (reach : Nat) (last : Fin target.length) : Prop :=
  0 < reach ∧ reach < last.val ∧ last.val ≤ 2 * reach ∧ last.val + 1 = target.length ∧
    target[initial last] = target[last] ∧
    (∀ index : Fin target.length, 0 < index.val → index < last →
      target[index] ≠ target[initial last]) ∧
    (∀ gap : Interval target, gap.value ≠ target[initial last] →
      gap.stop.val - gap.start.val ≤ reach)

instance (target : Stack) (reach : Nat) (last : Fin target.length) :
    Decidable (Family target reach last) := by unfold Family; infer_instance

-- The delayed value at each carrier slot is either a root or has an
-- unchanged copy within reach of the final output. This is the condition
-- used by the paper realization proof in docs/one-gap-carrier.md.
def CarrierSlots [DecidableEq α] (values : Fin size → α) (reach : Nat)
    (last prefetch : Fin size) (middle : Option (Fin size)) : Prop :=
  0 < prefetch.val ∧ prefetch.val ≤ reach ∧ IsRoot values prefetch ∧
    match middle with
    | none => prefetch < last ∧ last.val - prefetch.val ≤ reach
    | some index => prefetch < index ∧ index < last ∧
        index.val - prefetch.val ≤ reach ∧ last.val - index.val ≤ reach ∧
        (IsRoot values index ∨ RecentCopy values (last.val - reach) index)

instance [DecidableEq α] (values : Fin size → α) (reach : Nat)
    (last prefetch : Fin size) (middle : Option (Fin size)) :
    Decidable (CarrierSlots values reach last prefetch middle) := by
  unfold CarrierSlots
  cases middle <;> infer_instance

-- Immediately after a carrier hop to position p, all lower positions
-- agree with the target and the retained value is at the top.
def checkpoint (target : Stack) (carrier : Value) (position : Nat) : Stack :=
  target.take position ++ [carrier]

-- The proposed births differ at only the carrier slots. Reachability of
-- these births is a separate part of the stack realization proof.
def birthWord (target : Stack) (last prefetch : Fin target.length)
    (middle : Option (Fin target.length)) : Stack :=
  List.ofFn fun index : Fin target.length =>
    if index = prefetch then target[initial last]
    else if some index = middle then target[prefetch]
    else if index = last then target[middle.getD prefetch]
    else target[index]

end Shuffler.Optimality.Collective.OneGap
