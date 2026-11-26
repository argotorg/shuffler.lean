module

public import Lean
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Pointwise proofs of array encodings after list, array, or vector updates.
The procedure uses checked indexing rules and splits symbolic index cases.
It contains no program names or encoding functions. -/

namespace Lift.Tactic

open Lean Meta Elab Tactic

theorem array_range_index (n i : Nat) :
    (List.range n)[i]? = if i < n then some i else none := by
  by_cases h : i < n
  · simp only [ite_eq_left h, List.getElem?_range h]
  · rw [ite_eq_right h, List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]

syntax (name := arrayUpdate) "array_update" (" [" term,* "]")? : tactic

@[tactic arrayUpdate] meta def evalArrayUpdate : Tactic := fun stx => focus <| withoutRecover do
  let extra : Array (TSyntax `term) :=
    if stx[1].isNone then #[] else stx[1][1].getSepArgs.map (⟨·⟩)
  let args ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let normalize ← `(tactic|
    simp -failIfUnchanged (disch := (first | assumption | omega)) only
      [*, Vector.toList_set, Vector.toList_setIfInBounds,
       Array.toList_set, Array.toList_setIfInBounds,
       List.getD_eq_getElem?_getD, List.getElem?_set, List.getElem?_map,
       Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_set, Vector.getElem_setIfInBounds,
       Vector.singleton_def, Vector.getElem_singleton,
       List.getElem?_append, List.getElem?_cons, List.getElem?_nil,
       List.length_append, List.length_singleton, List.length_nil, Nat.sub_self,

       array_range_index, List.getElem?_eq_none, List.length_map,
       List.length_range, Vector.length_toList, Array.length_toList,
       Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
       ite_eq_left, ite_eq_right, ite_true, ite_false,
       not_true_eq_false, not_false_eq_true, $args,*] at *)
  -- Keep concrete capacities and client encoders opaque during rule matching.
  evalTactic (← `(tactic|
    with_reducible_and_instances
    ((first | (apply Vector.ext; intro index indexBound)
            | (apply List.ext_getElem?; intro index))
     $normalize
     all_goals
       repeat' (first | (solve | rfl | assumption | contradiction | omega | (congr <;> omega)) |
         (split <;> $normalize))
     all_goals done)))

end Lift.Tactic
