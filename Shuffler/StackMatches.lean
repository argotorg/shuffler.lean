import Shuffler.Feasibility.Spec

theorem SlotMatches.refl (value : Value) : SlotMatches value value := Or.inr rfl

theorem StackMatches.refl (stack : Stack) : StackMatches stack stack := by
  induction stack with
  | nil => exact .nil
  | cons value rest ih => exact .cons (SlotMatches.refl value) ih

theorem StackMatches.length_eq (h : StackMatches actual target) :
    actual.length = target.length := List.Forall₂.length_eq h
