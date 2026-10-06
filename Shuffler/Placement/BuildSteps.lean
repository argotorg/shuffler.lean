import Shuffler.Placement.Resources
import Mathlib.Data.List.Perm.Basic

namespace Shuffler.Placement

structure PlacementStep (spills : SpillSet) (fixed working : Stack)
    (value : Value) (added : Multiset Value) where
  remaining : Stack
  trace : Trace spills (fixed ++ working) ((fixed ++ [value]) ++ remaining)
  noPop : trace.noPop
  additions : trace.additions = added
  balance : {value} + (remaining : Multiset Value) = (working : Multiset Value) + added

private theorem swap_after_prefix (fixed working : Stack) (a b : Nat) :
    (fixed ++ working).swap (fixed.length + a) (fixed.length + b) =
      fixed ++ working.swap a b := by
  induction fixed with
  | nil => simp
  | cons value fixed ih =>
    simpa only [List.cons_append, List.length_cons, Nat.add_right_comm,
      List.swap_cons] using congrArg (value :: ·) ih

-- A reachable suffix position can be exchanged with the top. A top-to-top
-- exchange emits no instruction.
private def swapSuffix (spills : SpillSet) (fixed working : Stack) (pos : Nat)
    (hpos : pos < working.length) (hsmall : working.length ≤ MAX_SWAP_DEPTH + 1) :
    { trace : Trace spills (fixed ++ working)
        (fixed ++ working.swap (working.length - 1) pos) //
      trace.noPop ∧ trace.additions = 0 } := by
  if he : pos = working.length - 1 then
    have ht : fixed ++ working = fixed ++ working.swap (working.length - 1) pos := by
      simp [he]
    exact ⟨ht ▸ .Lit (fixed ++ working),
      (Trace.noPop_cast _ _).mpr trivial, by rw [Trace.additions_cast]; rfl⟩
  else
    let depth := working.length - 1 - pos
    have hlen : depth < (fixed ++ working).length := by
      simp only [List.length_append]
      dsimp [depth]
      omega
    have hlo : 1 ≤ depth := by dsimp [depth]; omega
    have hhi : depth ≤ MAX_SWAP_DEPTH := by dsimp [depth]; omega
    let trace := Trace.Swap depth hlen hlo hhi (Trace.Lit (spills := spills) (fixed ++ working))
    have htop : (fixed ++ working).length - 1 = fixed.length + (working.length - 1) := by
      simp only [List.length_append]
      omega
    have hindex : (fixed ++ working).length - 1 - depth = fixed.length + pos := by
      simp only [List.length_append]
      dsimp [depth]
      omega
    have ht : (fixed ++ working).swap ((fixed ++ working).length - 1)
        ((fixed ++ working).length - 1 - depth) =
        fixed ++ working.swap (working.length - 1) pos := by
      rw [hindex, htop, swap_after_prefix]
    exact ⟨ht ▸ trace, (Trace.noPop_cast _ _).mpr trivial,
      by rw [Trace.additions_cast]; rfl⟩

private theorem list_eq_head_drop (values : Stack) (value : Value)
    (hlen : 0 < values.length) (hvalue : values[0] = value) :
    values = value :: values.drop 1 := by
  simpa only [hvalue, Nat.zero_add, List.drop_zero] using
    (List.getElem_cons_drop hlen).symm

-- Select a physical occurrence by a finite search, then place it with at
-- most two top swaps. The order of the remaining values is unrestricted.
def placeExisting (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_SWAP_DEPTH + 1) (hvalue : value ∈ working) :
    PlacementStep spills fixed working value 0 := by
  let pos := working.idxOf value
  have hpos : pos < working.length := List.idxOf_lt_length_iff.mpr hvalue
  have hlen : 0 < working.length := by omega
  let raised := working.swap (working.length - 1) pos
  let placed := raised.swap (raised.length - 1) 0
  have hraised : raised.length = working.length := List.length_swap
  have hplaced : placed.length = working.length := by simp only [placed, List.length_swap, hraised]
  have hhead : placed[0]'(by omega) = value := by
    dsimp [placed]
    rw [List.getElem_swap_right_of_lt (by omega)]
    simp only [raised, List.length_swap, List.getElem_swap_left_of_lt hpos]
    exact List.getElem_idxOf hpos
  have hcons : placed = value :: placed.drop 1 := list_eq_head_drop _ _ (by omega) hhead
  let first := swapSuffix spills fixed working pos hpos hsmall
  let second := swapSuffix spills fixed raised 0 (by omega) (by omega)
  let trace := first.val.concat second.val
  have ht : fixed ++ placed = (fixed ++ [value]) ++ placed.drop 1 := by
    calc
      fixed ++ placed = fixed ++ value :: placed.drop 1 := congrArg (fixed ++ ·) hcons
      _ = (fixed ++ [value]) ++ placed.drop 1 := by
        simp only [List.append_assoc, List.singleton_append]
  refine ⟨placed.drop 1, ht ▸ trace, ?_, ?_, ?_⟩
  · exact (Trace.noPop_cast _ _).mpr (first.val.noPop_concat second.val first.property.1 second.property.1)
  · rw [Trace.additions_cast]
    change (first.val.concat second.val).additions = 0
    rw [Trace.additions_concat, first.property.2, second.property.2, add_zero]
  · have hp : placed.Perm working :=
      (List.swap_perm raised _ _).trans (List.swap_perm working _ _)
    have hb := Multiset.coe_eq_coe.mpr hp
    rw [hcons] at hb
    simpa only [Multiset.cons_coe, Multiset.singleton_add, add_zero] using hb

private def appendValue (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_DUP_DEPTH + 1)
    (havailable : Free spills value ∨ value ∈ working) :
    { trace : Trace spills (fixed ++ working) ((fixed ++ working) ++ [value]) //
      trace.noPop ∧ trace.additions = {value} } := by
  if hpush : value.can_be_freely_generated then
    exact ⟨.Push value hpush (.Lit _), trivial, rfl⟩
  else if hload : spills.is_spilled value then
    match value with
    | .Var id => exact ⟨.Load id hload (.Lit _), trivial, rfl⟩
    | .Lit _ | .Wildcard | .FunctionReturnLabel => simp [SpillSet.is_spilled] at hload
  else
    have hvalue : value ∈ working := by
      rcases havailable with hf | hm
      · exact False.elim (hf.elim hpush hload)
      · exact hm
    let pos := working.idxOf value
    have hpos : pos < working.length := List.idxOf_lt_length_iff.mpr hvalue
    let index := working.length - pos
    have hlen : index ≤ (fixed ++ working).length := by
      simp only [List.length_append]
      dsimp [index]
      omega
    have hlo : 1 ≤ index := by dsimp [index]; omega
    have hhi : index ≤ MAX_DUP_DEPTH + 1 := by dsimp [index]; omega
    have hoffset : (fixed ++ working).length - index = fixed.length + pos := by
      simp only [List.length_append]
      dsimp [index]
      omega
    have hcopy : (fixed ++ working)[(fixed ++ working).length - index] = value := by
      simp only [hoffset]
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      exact List.getElem_idxOf hpos
    let trace := Trace.Dup index hlen hlo hhi (Trace.Lit (spills := spills) (fixed ++ working))
    have ht : (fixed ++ working) ++ [(fixed ++ working)[(fixed ++ working).length - index]] =
        (fixed ++ working) ++ [value] := by rw [hcopy]
    refine ⟨ht ▸ trace, (Trace.noPop_cast _ _).mpr trivial, ?_⟩
    rw [Trace.additions_cast]
    simp only [trace, Trace.additions, hcopy, zero_add]

-- Generate the next output before fixing it. The working region keeps its
-- entire previous multiset, so all remaining DUP sources are retained.
def generateAndPlace (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_DUP_DEPTH + 1)
    (havailable : Free spills value ∨ value ∈ working) :
    PlacementStep spills fixed working value {value} := by
  let grown := working ++ [value]
  have hlen : 0 < grown.length := by simp [grown]
  have hbound : grown.length ≤ MAX_SWAP_DEPTH + 1 := by
    simp only [grown, List.length_append, List.length_singleton]
    unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
    omega
  let placed := grown.swap (grown.length - 1) 0
  have hplaced : placed.length = grown.length := List.length_swap
  have hhead : placed[0]'(by omega) = value := by
    rw [List.getElem_swap_right_of_lt (by omega)]
    simp [grown]
  have hcons : placed = value :: placed.drop 1 := list_eq_head_drop _ _ (by omega) hhead
  let first := appendValue spills fixed working value hsmall havailable
  let second := swapSuffix spills fixed grown 0 hlen hbound
  have hassoc : (fixed ++ working) ++ [value] = fixed ++ grown := List.append_assoc _ _ _
  let firstTrace := hassoc ▸ first.val
  let trace := firstTrace.concat second.val
  have ht : fixed ++ placed = (fixed ++ [value]) ++ placed.drop 1 := by
    calc
      fixed ++ placed = fixed ++ value :: placed.drop 1 := congrArg (fixed ++ ·) hcons
      _ = (fixed ++ [value]) ++ placed.drop 1 := by
        simp only [List.append_assoc, List.singleton_append]
  refine ⟨placed.drop 1, ht ▸ trace, ?_, ?_, ?_⟩
  · exact (Trace.noPop_cast _ _).mpr
      (firstTrace.noPop_concat second.val ((Trace.noPop_cast _ _).mpr first.property.1) second.property.1)
  · rw [Trace.additions_cast]
    change (firstTrace.concat second.val).additions = {value}
    rw [Trace.additions_concat, second.property.2, add_zero]
    exact (Trace.additions_cast _ _).trans first.property.2
  · have hp : placed.Perm grown := List.swap_perm grown _ _
    have hb := Multiset.coe_eq_coe.mpr hp
    rw [hcons] at hb
    simpa only [grown, Multiset.cons_coe, Multiset.singleton_add,
      ← Multiset.coe_add, Multiset.coe_singleton] using hb

end Shuffler.Placement
