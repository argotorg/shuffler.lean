import Shuffler.Optimality.BirthPlacement.SourcePlan
import Shuffler.Optimality.BirthPlacement.Realize.State

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation

@[simp] theorem SourcePlan.births_length (plan : SourcePlan spills source target) :
    plan.births.length = target.length - source.length := by
  simp [SourcePlan.births]

@[simp] theorem SourcePlan.events_length (plan : SourcePlan spills source target) :
    plan.events.length = target.length - source.length := List.length_ofFn

theorem sourceEntryCost_add_remaining (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) :
    sourceEntryCost assignment height hh +
      arbitrarySwapCount (SourcePrefix.run assignment height).permutation =
        sourcePotential assignment height hh := by
  by_cases hz : height = 0
  · subst height
    simp [sourceEntryCost, sourcePotential, SourcePrefix.run]
  · simp only [sourceEntryCost, sourcePotential, dite_eq_right hz]
    exact SourcePrefix.entry_cost_add_remaining assignment height hh ⟨height - 1, by omega⟩

theorem SourcePrefix.run_deadlines (assignment : Equiv.Perm (Fin size))
    (hd : BirthDeadlines reach assignment) (height : Nat) (hh : height ≤ size) :
    BirthDeadlines reach (SourcePrefix.run assignment height).permutation := by
  induction height with
  | zero => exact hd
  | succ height ih =>
      have hlt : height < size := by omega
      simp only [SourcePrefix.run, dite_eq_left hlt]
      exact (settleTop_spec (SourcePrefix.run assignment height).permutation ⟨height, hlt⟩
        (SourcePrefix.run_spec assignment height (by omega)).1 (ih (by omega))).2.1

theorem SourcePlan.source_append_births (plan : SourcePlan spills source target) :
    source ++ plan.births = birthWord target plan.assignment := by
  calc
    source ++ plan.births = prefixValues target plan.assignment source.length ++ plan.births :=
      congrArg (fun first => first ++ plan.births) plan.source_values.symm
    _ = birthWord target plan.assignment := List.take_append_drop _ _

theorem SourcePlan.prefix_balance (plan : SourcePlan spills source target) (height : Nat)
    (hn : source.length ≤ height) :
    source ++ plan.births.take (height - source.length) = prefixValues target plan.assignment height := by
  trans prefixValues target plan.assignment source.length ++ plan.births.take (height - source.length)
  · exact congrArg (fun first => first ++ plan.births.take (height - source.length))
      plan.source_values.symm
  dsimp [SourcePlan.births, prefixValues]
  rw [← List.take_add]
  congr 1
  omega

theorem SourcePlan.births_take_succ (plan : SourcePlan spills source target) (height : Nat)
    (hn : source.length ≤ height) (hh : height < target.length) :
    plan.births.take (height + 1 - source.length) =
      plan.births.take (height - source.length) ++ [target[plan.assignment ⟨height, hh⟩]] := by
  have hi : height - source.length < plan.births.length := by rw [plan.births_length]; omega
  rw [show height + 1 - source.length = (height - source.length) + 1 by omega,
    List.take_succ_eq_append_getElem hi]
  congr 2
  simp only [SourcePlan.births, List.getElem_drop, birthWord, List.getElem_ofFn]
  congr 2
  apply Fin.ext
  simp only
  omega

theorem SourcePlan.events_take_succ (plan : SourcePlan spills source target) (height : Nat)
    (hn : source.length ≤ height) (hh : height < target.length) :
    plan.events.take (height + 1 - source.length) =
      plan.events.take (height - source.length) ++
        [(plan.method ⟨height - source.length, by omega⟩, target[plan.assignment ⟨height, hh⟩])] := by
  have hi : height - source.length < plan.events.length := by rw [plan.events_length]; omega
  rw [show height + 1 - source.length = (height - source.length) + 1 by omega,
    List.take_succ_eq_append_getElem hi]
  congr 2
  simp only [SourcePlan.events, List.getElem_ofFn, sourceSlot]
  congr 3
  apply Fin.ext
  simp only
  omega

end Shuffler.Optimality.BirthPlacement
