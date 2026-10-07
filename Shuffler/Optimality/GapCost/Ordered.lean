import Shuffler.Optimality.GapCost.Defs
import Shuffler.Optimality.GapCount.Ordered

namespace Shuffler.Optimality.GapCost

theorem price_zero (swapPrice : Nat) (premium : Option Nat) : price swapPrice premium 0 = 0 := by
  cases premium <;> simp [price]

theorem price_move (swapPrice : Nat) (premium : Option Nat) (old next : Nat)
    (hlo : old ≤ next) (hhi : next ≤ old + 1) :
    price swapPrice premium old ≤ price swapPrice premium next ∧
      price swapPrice premium next ≤ price swapPrice premium old + swapPrice := by
  have hl := Nat.mul_le_mul_left swapPrice hlo
  have hh := Nat.mul_le_mul_left swapPrice hhi
  rw [Nat.mul_add, Nat.mul_one] at hh
  cases premium with
  | none => exact ⟨hl, hh⟩
  | some cap =>
      simp only [price]
      omega

theorem stepCost_near (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (old next : Nat) (hlo : old < next) (hhi : next ≤ old + 16) :
    stepCost swapPrice premium leading (some old) next = 0 := by
  have he : (next - old - 1) / 16 = 0 := by omega
  simp only [stepCost, he, price_zero]

theorem stepCost_move (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (previous : Option Nat) (old next : Nat)
    (hprevious : ∀ before ∈ previous, before < old)
    (hlo : old ≤ next) (hhi : next ≤ old + 16) :
    stepCost swapPrice premium leading previous old ≤ stepCost swapPrice premium leading previous next ∧
      stepCost swapPrice premium leading previous next ≤
        stepCost swapPrice premium leading previous old + swapPrice := by
  have hm := GapCount.stepCost_move previous old next hprevious hlo hhi
  cases previous with
  | none =>
      cases leading with
      | false => simp [stepCost]
      | true => exact price_move swapPrice premium _ _ hm.1 hm.2
  | some before => exact price_move swapPrice premium _ _ hm.1 hm.2

theorem pathCost_append_near_head (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (previous : Option Nat) (head : Nat) (tail : List Nat) (last : Nat)
    (hsorted : (head :: tail).Pairwise (· < ·))
    (hbound : ∀ i ∈ head :: tail, i < last) (hnear : last ≤ head + 16) :
    pathCost swapPrice premium leading previous ((head :: tail) ++ [last]) =
      pathCost swapPrice premium leading previous (head :: tail) := by
  induction tail generalizing previous head with
  | nil =>
      have hl := hbound head (by simp)
      simp only [List.cons_append, List.nil_append, pathCost,
        stepCost_near swapPrice premium leading head last hl hnear, Nat.add_zero]
  | cons next rest ih =>
      obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hsorted
      have hn := hfirst next (by simp)
      have he := ih (some head) next hrest
        (fun i hi => hbound i (List.mem_cons_of_mem _ hi)) (by omega)
      simpa only [List.cons_append, pathCost] using
        congrArg (stepCost swapPrice premium leading previous head + ·) he

theorem pathCost_append_near (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (previous : Option Nat) (positions : List Nat) (last : Nat)
    (hsorted : positions.Pairwise (· < ·)) (hbound : ∀ i ∈ positions, i < last)
    (hnear : ∃ i ∈ positions, last ≤ i + 16) :
    pathCost swapPrice premium leading previous (positions ++ [last]) =
      pathCost swapPrice premium leading previous positions := by
  induction positions generalizing previous with
  | nil => simp at hnear
  | cons head tail ih =>
      obtain ⟨i, hi, hn⟩ := hnear
      rcases List.mem_cons.mp hi with he | ht
      · subst i
        exact pathCost_append_near_head swapPrice premium leading previous head tail last hsorted hbound hn
      · have he := ih (some head) (List.pairwise_cons.mp hsorted).2
          (fun i hi => hbound i (List.mem_cons_of_mem _ hi)) ⟨i, ht, hn⟩
        simpa only [List.cons_append, pathCost] using
          congrArg (stepCost swapPrice premium leading previous head + ·) he

theorem pathCost_move_last (swapPrice : Nat) (premium : Option Nat) (leading : Bool)
    (previous : Option Nat) (positions : List Nat) (old next : Nat)
    (hstart : GapCount.StartsAfter previous positions) (hsorted : positions.Pairwise (· < ·))
    (hold : old ∈ positions) (hbound : ∀ i ∈ positions, i < next) (hnear : next ≤ old + 16) :
    pathCost swapPrice premium leading previous positions ≤
        pathCost swapPrice premium leading previous (positions.erase old ++ [next]) ∧
      pathCost swapPrice premium leading previous (positions.erase old ++ [next]) ≤
        pathCost swapPrice premium leading previous positions + swapPrice := by
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
              stepCost_move swapPrice premium leading previous old next hp (by omega) hnear
        | cons middle rest =>
            have hom := hfirst middle (by simp)
            have hm := hbound middle (by simp)
            have hn : next ≤ middle + 16 := by omega
            rw [pathCost_append_near_head swapPrice premium leading previous middle rest next hrest
              (fun i hi => hbound i (List.mem_cons_of_mem _ hi)) hn]
            have hs := stepCost_move swapPrice premium leading previous old middle hp (by omega) (by omega)
            simp only [pathCost, stepCost_near swapPrice premium leading old middle hom (by omega),
              Nat.zero_add]
            omega
      · have ht : old ∈ tail := (List.mem_cons.mp hold).resolve_left (Ne.symm he)
        have hnext := ih (some head)
          (by intro before hb i hi; have hb' : before = head := by simpa using hb.symm
              subst before; exact hfirst i hi)
          hrest ht (fun i hi => hbound i (List.mem_cons_of_mem _ hi))
        have herase : (head :: tail).erase old = head :: tail.erase old := by simp [he]
        rw [herase]
        simp only [List.cons_append, pathCost]
        omega

theorem pathCost_append_cap (swapPrice cap : Nat) (leading : Bool)
    (previous : Option Nat) (positions : List Nat) (last : Nat) :
    pathCost swapPrice (some cap) leading previous (positions ++ [last]) ≤
      pathCost swapPrice (some cap) leading previous positions + cap := by
  induction positions generalizing previous with
  | nil =>
      cases previous with
      | none => cases leading <;> simp [pathCost, stepCost, price]
      | some before => simp [pathCost, stepCost, price]
  | cons head tail ih =>
      have hh := ih (some head)
      simp only [List.cons_append, pathCost]
      omega

end Shuffler.Optimality.GapCost
