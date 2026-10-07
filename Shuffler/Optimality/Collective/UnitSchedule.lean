import Shuffler.Optimality.Collective.Deadlines

namespace Shuffler.Optimality.Collective

def unitOrder (jobs : List α) (deadline : α → Int) : List α :=
  jobs.mergeSort fun left right => decide (deadline left ≤ deadline right)

def MeetsDeadlines (deadline : α → Int) (order : List α) : Prop :=
  ∀ index : Fin order.length, (index.val : Int) + 1 ≤ deadline order[index]

instance (deadline : α → Int) (order : List α) : Decidable (MeetsDeadlines deadline order) := by
  unfold MeetsDeadlines
  infer_instance

def UnitCapacity [DecidableEq α] (jobs : List α) (deadline : α → Int) : Prop :=
  ∀ time : Nat, (jobs.toFinset.filter fun job => deadline job ≤ (time : Int)).card ≤ time

end Shuffler.Optimality.Collective
