import Shuffler.Optimality.BirthPlacement.SourcePlan.Theorems
import Shuffler.Optimality.BirthPlacement.TracePlan.SourceAvailability

namespace Shuffler.Optimality.BirthPlacement

theorem SourceCycles.traceSwaps_lower (size : Nat) (trace : Trace spills source target)
    (hpop : trace.noPop) (hbound : target.length ≤ size) :
    ∀ step ∈ traceSwaps size trace hpop hbound, source.length ≤ step.2.val + 17 := by
  induction trace with
  | Lit => simp [traceSwaps]
  | @Swap previous depth hlen hlo hhi earlier ih =>
    intro step hs
    simp only [traceSwaps, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact ih hpop _ step hs
    · have hl := earlier.noPop_length_le hpop
      change source.length ≤ previous.length - 1 - depth + 17
      simp only [MAX_SWAP_DEPTH] at hhi
      omega
  | Dup _ _ _ _ earlier ih | Push _ _ earlier ih | Load _ _ earlier ih =>
    simpa only [traceSwaps] using ih hpop _
  | Pop _ _ => exact False.elim hpop

theorem traceAssignment_source_frozen (trace : Trace spills source target) (hpop : trace.noPop)
    (index : Fin target.length) (hi : index.val + 17 < source.length) :
    traceAssignment trace hpop index = index := by
  let swaps := SourceCycles.traceSwaps target.length trace hpop (Nat.le_refl _)
  have avoids : ∀ step ∈ swaps, index ≠ step.1 ∧ index ≠ step.2 := by
    intro step hs
    have hl := SourceCycles.traceSwaps_lower target.length trace hpop (Nat.le_refl _) step hs
    have ht := SourceCycles.traceSwaps_top target.length trace hpop (Nat.le_refl _) step hs
    constructor <;> intro he
    · have he := congrArg Fin.val he
      omega
    · have he := congrArg Fin.val he
      omega
  have fixed : ∀ items : List (Fin target.length × Fin target.length),
      (∀ step ∈ items, index ≠ step.1 ∧ index ≠ step.2) →
        ((items.map fun step => Equiv.swap step.1 step.2).prod) index = index := by
    intro items
    induction items with
    | nil => intro _; rfl
    | cons step rest ih =>
      intro havoid
      simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      rw [ih (fun other ho => havoid other (List.mem_cons_of_mem _ ho))]
      exact Equiv.swap_apply_of_ne_of_ne (havoid step List.mem_cons_self).1
        (havoid step List.mem_cons_self).2
  have hfixed := fixed swaps avoids
  rw [SourceCycles.traceSwaps_permutation] at hfixed
  apply (extractTokens target.length trace hpop (Nat.le_refl _)).permutation.injective
  change (extractTokens target.length trace hpop (Nat.le_refl _)).permutation
    ((extractTokens target.length trace hpop (Nat.le_refl _)).permutation.symm index) = _
  rw [Equiv.apply_symm_apply, hfixed]

theorem traceSourceEvent_value (trace : Trace spills source target) (hpop : trace.noPop)
    (index : Fin (target.length - source.length)) :
    ((traceEvents trace)[index.val]'(by have := source_events_length trace hpop; have := index.isLt; omega)).2 =
      target[traceAssignment trace hpop
        (sourceSlot source.length target.length (trace.noPop_length_le hpop) index)] := by
  have hi : index.val < (traceEvents trace).length := by
    have := source_events_length trace hpop
    have := index.isLt
    omega
  have hw : source ++ (traceEvents trace).map Prod.snd =
      birthWord target (traceAssignment trace hpop) := by
    rw [traceEvents_values, traceAssignment_birthWord]
  have he := congrArg (fun values : Stack => values[source.length + index.val]?) hw
  have ha : source.length + index.val < target.length := by have := index.isLt; omega
  simp only [List.getElem?_append_right (by omega : source.length ≤ source.length + index.val),
    Nat.add_sub_cancel_left, List.getElem?_map, birthWord, List.getElem?_ofFn,
    dite_eq_left ha, List.getElem?_eq_getElem hi, Option.map_some] at he
  exact Option.some.inj he

theorem traceSource_values (trace : Trace spills source target) (hpop : trace.noPop) :
    prefixValues target (traceAssignment trace hpop) source.length = source := by
  simp only [prefixValues, traceAssignment_birthWord, List.take_left]

theorem traceSource_available (trace : Trace spills source target) (hpop : trace.noPop)
    (index : Fin (target.length - source.length)) :
    BirthAvailable spills target (birthWord target (traceAssignment trace hpop))
      (source.length + index.val)
      target[traceAssignment trace hpop
        (sourceSlot source.length target.length (trace.noPop_length_le hpop) index)]
      ((traceEvents trace)[index.val]'(by
        have := source_events_length trace hpop; have := index.isLt; omega)).1 := by
  have hi : index.val < (traceEvents trace).length := by
    have := source_events_length trace hpop
    have := index.isLt
    omega
  have ha := traceEvents_available_from trace hpop index.val hi
  rw [traceSourceEvent_value trace hpop index] at ha
  simpa only [traceAssignment_birthWord] using ha

end Shuffler.Optimality.BirthPlacement
