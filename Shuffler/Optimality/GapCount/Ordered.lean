import Shuffler.Optimality.GapCount.Defs
import Mathlib.Data.List.Sort

namespace Shuffler.Optimality.GapCount

def StartsAfter (previous : Option Nat) (positions : List Nat) : Prop :=
  ∀ before ∈ previous, ∀ next ∈ positions, before < next

theorem stepCost_split (previous : Option Nat) (middle last : Nat)
    (hprevious : ∀ before ∈ previous, before < middle) (hml : middle < last) :
    stepCost previous middle + stepCost (some middle) last ≤ stepCost previous last ∧
      stepCost previous last ≤ stepCost previous middle + stepCost (some middle) last + 1 := by
  cases previous with
  | none => simp only [stepCost]; omega
  | some before =>
      have hb := hprevious before (by simp)
      simp only [stepCost]
      omega

theorem stepCost_move (previous : Option Nat) (old next : Nat)
    (hprevious : ∀ before ∈ previous, before < old)
    (hlo : old ≤ next) (hhi : next ≤ old + 16) :
    stepCost previous old ≤ stepCost previous next ∧
      stepCost previous next ≤ stepCost previous old + 1 := by
  cases previous with
  | none => simp only [stepCost]; omega
  | some before =>
      have hb := hprevious before (by simp)
      simp only [stepCost]
      omega

theorem pathCost_append_ge (previous : Option Nat) (positions : List Nat) (last : Nat) :
    pathCost previous positions ≤ pathCost previous (positions ++ [last]) := by
  induction positions generalizing previous with
  | nil => simp [pathCost]
  | cons head tail ih =>
      simpa only [List.cons_append, pathCost] using Nat.add_le_add_left (ih (some head)) _

theorem pathCost_append_near_head (previous : Option Nat) (head : Nat) (tail : List Nat) (last : Nat)
    (hsorted : (head :: tail).Pairwise (· < ·))
    (hbound : ∀ i ∈ head :: tail, i < last) (hnear : last ≤ head + 16) :
    pathCost previous ((head :: tail) ++ [last]) = pathCost previous (head :: tail) := by
  induction tail generalizing previous head with
  | nil =>
      have hl := hbound head (by simp)
      simp only [List.cons_append, List.nil_append, pathCost, stepCost, Nat.add_zero]
      omega
  | cons next rest ih =>
      obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hsorted
      have hn := hfirst next (by simp)
      have he := ih (some head) next hrest
        (fun i hi => hbound i (List.mem_cons_of_mem _ hi)) (by omega)
      simpa only [List.cons_append, pathCost] using congrArg (stepCost previous head + ·) he

theorem pathCost_append_near (previous : Option Nat) (positions : List Nat) (last : Nat)
    (hsorted : positions.Pairwise (· < ·)) (hbound : ∀ i ∈ positions, i < last)
    (hnear : ∃ i ∈ positions, last ≤ i + 16) :
    pathCost previous (positions ++ [last]) = pathCost previous positions := by
  induction positions generalizing previous with
  | nil => simp at hnear
  | cons head tail ih =>
      obtain ⟨i, hi, hn⟩ := hnear
      rcases List.mem_cons.mp hi with he | ht
      · subst i
        exact pathCost_append_near_head previous head tail last hsorted hbound hn
      · have he := ih (some head) (List.pairwise_cons.mp hsorted).2
          (fun i hi => hbound i (List.mem_cons_of_mem _ hi)) ⟨i, ht, hn⟩
        simpa only [List.cons_append, pathCost] using congrArg (stepCost previous head + ·) he

-- Moving one occurrence to a new last position cannot reduce this potential.
-- If the movement is at most sixteen slots, it increases it by at most one.
theorem pathCost_move_last (previous : Option Nat) (positions : List Nat) (old next : Nat)
    (hstart : StartsAfter previous positions) (hsorted : positions.Pairwise (· < ·))
    (hold : old ∈ positions) (hbound : ∀ i ∈ positions, i < next) (hnear : next ≤ old + 16) :
    pathCost previous positions ≤ pathCost previous (positions.erase old ++ [next]) ∧
      pathCost previous (positions.erase old ++ [next]) ≤ pathCost previous positions + 1 := by
  induction positions generalizing previous with
  | nil => simp at hold
  | cons head tail ih =>
      obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hsorted
      by_cases he : head = old
      · subst head
        rw [List.erase_cons_head]
        have hp : ∀ before ∈ previous, before < old :=
          fun before hb => hstart before hb old (by simp)
        cases tail with
        | nil =>
            have hn := hbound old (by simp)
            simpa only [pathCost, Nat.add_zero, List.nil_append] using
              stepCost_move previous old next hp (by omega) hnear
        | cons middle rest =>
            have hom := hfirst middle (by simp)
            have hn : next ≤ middle + 16 := by omega
            rw [pathCost_append_near_head previous middle rest next hrest
              (fun i hi => hbound i (List.mem_cons_of_mem _ hi)) hn]
            have hs := stepCost_split previous old middle hp hom
            simp only [pathCost]
            omega
      · have ht : old ∈ tail := (List.mem_cons.mp hold).resolve_left (Ne.symm he)
        have hnext := ih (some head)
          (by intro before hb i hi; have hb' : before = head := by simpa using hb.symm
              subst before; exact hfirst i hi)
          hrest ht (fun i hi => hbound i (List.mem_cons_of_mem _ hi))
        have herase : (head :: tail).erase old = head :: tail.erase old := by
          simp [he]
        rw [herase]
        simp only [List.cons_append, pathCost]
        omega

end Shuffler.Optimality.GapCount
