import Shuffler.BuildBottomUp.Lemmas.Placement.Resources
import Mathlib.Data.List.Perm.Basic

namespace Shuffler.ExactBuild

open Shuffler.Placement

structure BuiltTrace (spills : SpillSet) (source target : Stack) (missing : Multiset Value) where
  trace : Trace spills source target
  noPop : trace.noPop
  additions : trace.additions = missing

def BuiltTrace.cast {otherSource otherTarget : Stack} {otherMissing : Multiset Value}
    (result : BuiltTrace spills source target missing)
    (hs : source = otherSource) (ht : target = otherTarget) (hm : missing = otherMissing) :
    BuiltTrace spills otherSource otherTarget otherMissing := by
  subst otherSource otherTarget otherMissing
  exact result

def BuiltTrace.castTarget (result : BuiltTrace spills source target missing)
    (h : target = other) : BuiltTrace spills source other missing :=
  ⟨h ▸ result.trace, (Trace.noPop_cast _ _).mpr result.noPop,
    (Trace.additions_cast _ _).trans result.additions⟩

def BuiltTrace.trans (first : BuiltTrace spills source middle firstMissing)
    (second : BuiltTrace spills middle target secondMissing) :
    BuiltTrace spills source target (firstMissing + secondMissing) where
  trace := first.trace.concat second.trace
  noPop := first.trace.noPop_concat second.trace first.noPop second.noPop
  additions := by rw [Trace.additions_concat, first.additions, second.additions]

def BuiltTrace.lit (spills : SpillSet) (stack : Stack) : BuiltTrace spills stack stack 0 :=
  ⟨.Lit stack, trivial, rfl⟩

def BuiltTrace.swap (stack : Stack) (depth : Nat) (hlen : depth < stack.length)
    (hlo : 1 ≤ depth) (hhi : depth ≤ MAX_SWAP_DEPTH) :
    BuiltTrace spills stack (stack.swap (stack.length - 1) (stack.length - 1 - depth)) 0 :=
  ⟨.Swap depth hlen hlo hhi (.Lit stack), trivial, rfl⟩

def BuiltTrace.dup (stack : Stack) (index : Nat) (hlen : index ≤ stack.length)
    (hlo : 1 ≤ index) (hhi : index ≤ MAX_DUP_DEPTH + 1)
    (hvalue : stack[stack.length - index] = value) :
    BuiltTrace spills stack (stack ++ [value]) {value} :=
  have ht : stack ++ [stack[stack.length - index]] = stack ++ [value] := by rw [hvalue]
  ⟨ht ▸ .Dup index hlen hlo hhi (.Lit stack), (Trace.noPop_cast _ _).mpr trivial, by
    rw [Trace.additions_cast]
    simp only [Trace.additions, hvalue, zero_add]⟩

def BuiltTrace.push (stack : Stack) (value : Value) (hfree : value.can_be_freely_generated) :
    BuiltTrace spills stack (stack ++ [value]) {value} :=
  ⟨.Push value hfree (.Lit stack), trivial, rfl⟩

def BuiltTrace.load (stack : Stack) :
    (value : Value) → spills.is_spilled value → BuiltTrace spills stack (stack ++ [value]) {value}
  | .Var id, hload => ⟨.Load id hload (.Lit stack), trivial, rfl⟩
  | .Lit _, hload | .Wildcard, hload | .FunctionReturnLabel, hload => False.elim hload

structure PlacementStep (spills : SpillSet) (fixed working : Stack)
    (value : Value) (added : Multiset Value) where
  remaining : Stack
  built : BuiltTrace spills (fixed ++ working) ((fixed ++ [value]) ++ remaining) added
  balance : {value} + (remaining : Multiset Value) = (working : Multiset Value) + added

private theorem swap_after_prefix (fixed working : Stack) (a b : Nat) :
    (fixed ++ working).swap (fixed.length + a) (fixed.length + b) =
      fixed ++ working.swap a b := by
  induction fixed with
  | nil => simp
  | cons value fixed ih =>
    simpa only [List.cons_append, List.length_cons, Nat.add_right_comm,
      List.swap_cons] using congrArg (value :: ·) ih

private theorem swap_top_self (fixed working : Stack) (htop : pos = working.length - 1) :
    fixed ++ working = fixed ++ working.swap (working.length - 1) pos := by
  simp [htop]

private theorem swap_suffix (fixed working : Stack) (hpos : pos < working.length) :
    (fixed ++ working).swap ((fixed ++ working).length - 1)
        ((fixed ++ working).length - 1 - (working.length - 1 - pos)) =
      fixed ++ working.swap (working.length - 1) pos := by
  have htop : (fixed ++ working).length - 1 = fixed.length + (working.length - 1) := by
    simp only [List.length_append]
    omega
  have hindex : (fixed ++ working).length - 1 - (working.length - 1 - pos) =
      fixed.length + pos := by
    simp only [List.length_append]
    omega
  rw [hindex, htop, swap_after_prefix]

-- Exchange the top of the working suffix with position pos. A top-to-top
-- exchange emits no instruction.
def swapSuffix (spills : SpillSet) (fixed working : Stack) (pos : Nat)
    (hpos : pos < working.length) (hsmall : working.length ≤ MAX_SWAP_DEPTH + 1) :
    BuiltTrace spills (fixed ++ working) (fixed ++ working.swap (working.length - 1) pos) 0 :=
  if htop : pos = working.length - 1 then
    (BuiltTrace.lit spills (fixed ++ working)).castTarget (swap_top_self fixed working htop)
  else
    (BuiltTrace.swap (fixed ++ working) (working.length - 1 - pos)
      (by simp only [List.length_append]; omega) (by omega) (by omega)).castTarget
      (swap_suffix fixed working hpos)

private theorem list_eq_head_drop (values : Stack) (value : Value)
    (hlen : 0 < values.length) (hvalue : values[0] = value) :
    values = value :: values.drop 1 := by
  simpa only [hvalue, Nat.zero_add, List.drop_zero] using
    (List.getElem_cons_drop hlen).symm

private theorem fixed_head (fixed placed : Stack) (hlen : 0 < placed.length)
    (hhead : placed[0] = value) :
    fixed ++ placed = (fixed ++ [value]) ++ placed.drop 1 := by
  conv_lhs => rw [list_eq_head_drop placed value hlen hhead]
  simp only [List.append_assoc, List.singleton_append]

private theorem head_balance (placed : Stack) (hlen : 0 < placed.length)
    (hhead : placed[0] = value) (hperm : (placed : Multiset Value) = resources) :
    {value} + ((placed.drop 1 : Stack) : Multiset Value) = resources := by
  rw [← hperm, list_eq_head_drop placed value hlen hhead]
  simp

-- Fix the head of placed as the next output. The rest of placed is the next
-- working suffix.
def PlacementStep.ofPlaced {placed : Stack}
    (built : BuiltTrace spills (fixed ++ working) (fixed ++ placed) added)
    (hlen : 0 < placed.length) (hhead : placed[0] = value)
    (hperm : (placed : Multiset Value) = (working : Multiset Value) + added) :
    PlacementStep spills fixed working value added :=
  ⟨placed.drop 1, built.castTarget (fixed_head fixed placed hlen hhead),
    head_balance placed hlen hhead hperm⟩

private theorem existing_head (working : Stack) (hvalue : value ∈ working) :
    ((working.swap (working.length - 1) (working.idxOf value)).swap
      ((working.swap (working.length - 1) (working.idxOf value)).length - 1) 0)[0]'(by
        simpa using List.length_pos_of_mem hvalue) = value := by
  have hpos := List.idxOf_lt_length_iff.mpr hvalue
  rw [List.getElem_swap_right_of_lt (by simp; omega)]
  simp only [List.length_swap, List.getElem_swap_left_of_lt hpos]
  exact List.getElem_idxOf hpos

private theorem swap_swap_balance (values : Stack) (a b c d : Nat) :
    (((values.swap a b).swap c d : Stack) : Multiset Value) =
      (values : Multiset Value) + 0 := by
  rw [add_zero]
  exact Multiset.coe_eq_coe.mpr ((List.swap_perm _ _ _).trans (List.swap_perm _ _ _))

-- Select a physical occurrence by a finite search, then place it with at
-- most two top swaps. The order of the remaining values is unrestricted.
def placeExisting (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_SWAP_DEPTH + 1) (hvalue : value ∈ working) :
    PlacementStep spills fixed working value 0 :=
  have hpos : working.idxOf value < working.length := List.idxOf_lt_length_iff.mpr hvalue
  let raised := working.swap (working.length - 1) (working.idxOf value)
  let first := swapSuffix spills fixed working (working.idxOf value) hpos hsmall
  let second := swapSuffix spills fixed raised 0 (by simp [raised]; omega)
    (by simpa [raised] using hsmall)
  .ofPlaced (first.trans second) (by simp [raised]; omega) (existing_head working hvalue)
    (swap_swap_balance _ _ _ _ _)

private theorem dup_index (fixed working : Stack) (hvalue : value ∈ working) :
    (fixed ++ working)[(fixed ++ working).length - (working.length - working.idxOf value)]'(by
      have := List.idxOf_lt_length_iff.mpr hvalue
      simp only [List.length_append]
      omega) = value := by
  have hpos := List.idxOf_lt_length_iff.mpr hvalue
  have hoffset : (fixed ++ working).length - (working.length - working.idxOf value) =
      fixed.length + working.idxOf value := by
    simp only [List.length_append]
    omega
  simp only [hoffset]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem_idxOf hpos

private theorem mem_of_not_free {working : Stack} (hpush : ¬value.can_be_freely_generated)
    (hload : ¬spills.is_spilled value) (havailable : Free spills value ∨ value ∈ working) :
    value ∈ working :=
  havailable.resolve_left fun hf => hf.elim hpush hload

-- PUSH or LOAD a free value. Otherwise DUP its first occurrence in the
-- working suffix.
def appendValue (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_DUP_DEPTH + 1)
    (havailable : Free spills value ∨ value ∈ working) :
    BuiltTrace spills (fixed ++ working) ((fixed ++ working) ++ [value]) {value} :=
  if hpush : value.can_be_freely_generated then
    .push _ value hpush
  else if hload : spills.is_spilled value then
    .load _ value hload
  else
    have hvalue := mem_of_not_free hpush hload havailable
    have hpos : working.idxOf value < working.length := List.idxOf_lt_length_iff.mpr hvalue
    .dup (fixed ++ working) (working.length - working.idxOf value)
      (by simp only [List.length_append]; omega) (by omega) (by omega)
      (dup_index fixed working hvalue)

private theorem appended_head (working : Stack) (value : Value) :
    ((working ++ [value]).swap ((working ++ [value]).length - 1) 0)[0]'(by simp) = value := by
  rw [List.getElem_swap_right_of_lt (by simp)]
  simp

private theorem appended_balance (working : Stack) (value : Value) :
    (((working ++ [value]).swap ((working ++ [value]).length - 1) 0 : Stack) : Multiset Value) =
      (working : Multiset Value) + {value} := by
  rw [Multiset.coe_eq_coe.mpr (List.swap_perm _ _ _)]
  rw [← Multiset.coe_add, Multiset.coe_singleton]

-- Generate the next output before fixing it. The working region keeps its
-- entire previous multiset, so all remaining DUP sources are retained.
def generateAndPlace (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_DUP_DEPTH + 1)
    (havailable : Free spills value ∨ value ∈ working) :
    PlacementStep spills fixed working value {value} :=
  let grown := working ++ [value]
  let first := (appendValue spills fixed working value hsmall havailable).castTarget
    (List.append_assoc fixed working [value])
  let second := swapSuffix spills fixed grown 0 (by simp [grown])
    (by simp only [grown, List.length_append, List.length_singleton]
        unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
        omega)
  .ofPlaced (first.trans second) (by simp [grown]) (appended_head working value)
    (appended_balance working value)

end Shuffler.ExactBuild
