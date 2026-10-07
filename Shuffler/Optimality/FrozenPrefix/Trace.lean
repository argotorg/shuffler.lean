import Shuffler.Optimality.Replay
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.FrozenPrefix

open Shuffler.Placement

private theorem flatten_cast (h : target = other) (trace : Trace spills source target) :
    flatten (h ▸ trace) = flatten trace := by cases h; rfl

private theorem swap_after_prefix (fixed working : Stack) (a b : Nat) :
    (fixed ++ working).swap (fixed.length + a) (fixed.length + b) =
      fixed ++ working.swap a b := by
  induction fixed with
  | nil => simp
  | cons value fixed ih =>
      simpa only [List.cons_append, List.length_cons, Nat.add_right_comm,
        List.swap_cons] using congrArg (value :: ·) ih

private theorem drop_swap (stack : Stack) (count a b : Nat)
    (hc : count ≤ stack.length) (ha : count ≤ a) (hb : count ≤ b) :
    (stack.swap a b).drop count = (stack.drop count).swap (a - count) (b - count) := by
  have hlen : (stack.take count).length = count := by simp [List.length_take, hc]
  have hstack := List.take_append_drop count stack
  have hswap := swap_after_prefix (stack.take count) (stack.drop count) (a - count) (b - count)
  rw [hlen, Nat.add_sub_of_le ha, Nat.add_sub_of_le hb, hstack] at hswap
  rw [hswap]
  simp [hlen]

-- Removing any part of the initially frozen prefix keeps every operation.
-- There is no POP. The original length therefore remains a lower bound
-- for the length before each operation.
theorem exists_drop (trace : Trace spills source target) (hpop : trace.noPop)
    (count : Nat) (hcount : count ≤ frozen source) :
    ∃ reduced : Trace spills (source.drop count) (target.drop count),
      reduced.noPop ∧ reduced.additions = trace.additions ∧ flatten reduced = flatten trace := by
  induction trace with
  | Lit => exact ⟨.Lit _, trivial, rfl, rfl⟩
  | Pop _ _ => exact False.elim hpop
  | @Swap previous depth hlen hlo hhi trace ih =>
      obtain ⟨reduced, hr, ha, ho⟩ := ih hpop
      have hlength := trace.noPop_length_le hpop
      have hc : count ≤ previous.length := by unfold frozen at hcount; omega
      have hd : depth < (previous.drop count).length := by
        simp only [List.length_drop]
        simp only [frozen, MAX_SWAP_DEPTH] at hcount hhi
        omega
      have htop : count ≤ previous.length - 1 := by
        simp only [frozen, MAX_SWAP_DEPTH] at hcount hhi
        omega
      have hindex : count ≤ previous.length - 1 - depth := by
        simp only [frozen, MAX_SWAP_DEPTH] at hcount hhi
        omega
      let step := Trace.Swap depth hd hlo hhi reduced
      have ht : (previous.drop count).swap ((previous.drop count).length - 1)
          ((previous.drop count).length - 1 - depth) =
          (previous.swap (previous.length - 1) (previous.length - 1 - depth)).drop count := by
        rw [drop_swap previous count _ _ hc htop hindex]
        simp only [List.length_drop]
        congr 1 <;> omega
      refine ⟨ht ▸ step, (Trace.noPop_cast _ _).mpr hr, ?_, ?_⟩
      · rw [Trace.additions_cast]; exact ha
      · rw [flatten_cast]; simp only [step, flatten, ho]
  | @Dup previous index hlen hlo hhi trace ih =>
      obtain ⟨reduced, hr, ha, ho⟩ := ih hpop
      have hlength := trace.noPop_length_le hpop
      have hc : count ≤ previous.length := by unfold frozen at hcount; omega
      have hd : index ≤ (previous.drop count).length := by
        simp only [List.length_drop]
        simp only [frozen, MAX_SWAP_DEPTH, MAX_DUP_DEPTH] at hcount hhi
        omega
      have hcopy : (previous.drop count)[(previous.drop count).length - index]'(by omega) =
          previous[previous.length - index]'(by omega) := by
        rw [List.getElem_drop]
        congr 1
        simp only [List.length_drop] at hd ⊢
        omega
      let step := Trace.Dup index hd hlo hhi reduced
      have ht : previous.drop count ++
          [(previous.drop count)[(previous.drop count).length - index]'(by omega)] =
          (previous ++ [previous[previous.length - index]'(by omega)]).drop count := by
        rw [List.drop_append_of_le_length hc, hcopy]
      refine ⟨ht ▸ step, (Trace.noPop_cast _ _).mpr hr, ?_, ?_⟩
      · rw [Trace.additions_cast]
        simp only [step, Trace.additions, hcopy, ha]
      · rw [flatten_cast]; simp only [step, flatten, ho]
  | Push value hfree trace ih =>
      obtain ⟨reduced, hr, ha, ho⟩ := ih hpop
      have hc : count ≤ _ := Nat.le_trans (by unfold frozen at hcount; omega)
        (trace.noPop_length_le hpop)
      let step := Trace.Push value hfree reduced
      have ht := (List.drop_append_of_le_length hc (l₂ := [value])).symm
      refine ⟨ht ▸ step, (Trace.noPop_cast _ _).mpr hr, ?_, ?_⟩
      · rw [Trace.additions_cast]; simp only [step, Trace.additions, ha]
      · rw [flatten_cast]; simp only [step, flatten, ho]
  | Load id hspilled trace ih =>
      obtain ⟨reduced, hr, ha, ho⟩ := ih hpop
      have hc : count ≤ _ := Nat.le_trans (by unfold frozen at hcount; omega)
        (trace.noPop_length_le hpop)
      let step := Trace.Load id hspilled reduced
      have ht := (List.drop_append_of_le_length hc (l₂ := [Value.Var id])).symm
      refine ⟨ht ▸ step, (Trace.noPop_cast _ _).mpr hr, ?_, ?_⟩
      · rw [Trace.additions_cast]; simp only [step, Trace.additions, ha]
      · rw [flatten_cast]; simp only [step, flatten, ho]

-- Adding a fixed prefix needs no height or matching-prefix assumption.
-- Every operation keeps its depth relative to the top of the suffix.
theorem exists_lift (trace : Trace spills source target) (hpop : trace.noPop)
    (fixed : Stack) :
    ∃ lifted : Trace spills (fixed ++ source) (fixed ++ target),
      lifted.noPop ∧ lifted.additions = trace.additions ∧ flatten lifted = flatten trace := by
  induction trace with
  | Lit => exact ⟨.Lit _, trivial, rfl, rfl⟩
  | Pop _ _ => exact False.elim hpop
  | @Swap previous depth hlen hlo hhi trace ih =>
      obtain ⟨lifted, hr, ha, ho⟩ := ih hpop
      have hd : depth < (fixed ++ previous).length := by simp only [List.length_append]; omega
      let step := Trace.Swap depth hd hlo hhi lifted
      have ht : (fixed ++ previous).swap ((fixed ++ previous).length - 1)
          ((fixed ++ previous).length - 1 - depth) =
          fixed ++ previous.swap (previous.length - 1) (previous.length - 1 - depth) := by
        have htop : (fixed ++ previous).length - 1 = fixed.length + (previous.length - 1) := by
          simp only [List.length_append]; omega
        have hindex : (fixed ++ previous).length - 1 - depth =
            fixed.length + (previous.length - 1 - depth) := by
          simp only [List.length_append]; omega
        rw [hindex, htop, swap_after_prefix]
      refine ⟨ht ▸ step, (Trace.noPop_cast _ _).mpr hr, ?_, ?_⟩
      · rw [Trace.additions_cast]; exact ha
      · rw [flatten_cast]; simp only [step, flatten, ho]
  | @Dup previous index hlen hlo hhi trace ih =>
      obtain ⟨lifted, hr, ha, ho⟩ := ih hpop
      have hd : index ≤ (fixed ++ previous).length := by simp only [List.length_append]; omega
      have hcopy : (fixed ++ previous)[(fixed ++ previous).length - index]'(by omega) =
          previous[previous.length - index]'(by omega) := by
        rw [List.getElem_append_right (by simp only [List.length_append]; omega)]
        congr 1
        simp only [List.length_append]
        omega
      let step := Trace.Dup index hd hlo hhi lifted
      have ht : (fixed ++ previous) ++
          [(fixed ++ previous)[(fixed ++ previous).length - index]'(by omega)] =
          fixed ++ (previous ++ [previous[previous.length - index]'(by omega)]) := by
        rw [hcopy, List.append_assoc]
      refine ⟨ht ▸ step, (Trace.noPop_cast _ _).mpr hr, ?_, ?_⟩
      · rw [Trace.additions_cast]; simp only [step, Trace.additions, hcopy, ha]
      · rw [flatten_cast]; simp only [step, flatten, ho]
  | Push value hfree trace ih =>
      obtain ⟨lifted, hr, ha, ho⟩ := ih hpop
      let step := Trace.Push value hfree lifted
      refine ⟨(List.append_assoc fixed _ [value]) ▸ step,
        (Trace.noPop_cast _ _).mpr hr, ?_, ?_⟩
      · rw [Trace.additions_cast]; simp only [step, Trace.additions, ha]
      · rw [flatten_cast]; simp only [step, flatten, ho]
  | Load id hspilled trace ih =>
      obtain ⟨lifted, hr, ha, ho⟩ := ih hpop
      let step := Trace.Load id hspilled lifted
      refine ⟨(List.append_assoc fixed _ [Value.Var id]) ▸ step,
        (Trace.noPop_cast _ _).mpr hr, ?_, ?_⟩
      · rw [Trace.additions_cast]; simp only [step, Trace.additions, ha]
      · rw [flatten_cast]; simp only [step, flatten, ho]

end Shuffler.Optimality.FrozenPrefix
