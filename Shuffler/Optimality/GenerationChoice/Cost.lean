import Shuffler.Optimality.GenerationChoice.Theorems

namespace Shuffler.Optimality

theorem cheaperOp_le_left (costs : PrimitiveCosts) (weights : Weights) (a b : Op) :
    ((cheaperOp costs weights a b).cost costs).score weights ≤ (a.cost costs).score weights := by
  unfold cheaperOp
  split
  · exact Nat.le_refl _
  · rename_i h
    simp only [preferCost, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true, beq_iff_eq] at h
    omega

theorem cheaperOp_le_right (costs : PrimitiveCosts) (weights : Weights) (a b : Op) :
    ((cheaperOp costs weights a b).cost costs).score weights ≤ (b.cost costs).score weights := by
  unfold cheaperOp
  split
  · rename_i h
    simp only [preferCost, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true, beq_iff_eq] at h
    omega
  · exact Nat.le_refl _

private theorem fold_cheaperOp_le_first (costs : PrimitiveCosts) (weights : Weights)
    (first : Op) (rest : List Op) :
    ((rest.foldl (cheaperOp costs weights) first).cost costs).score weights ≤
      (first.cost costs).score weights := by
  induction rest generalizing first with
  | nil => exact Nat.le_refl _
  | cons op rest ih =>
      exact (ih _).trans (cheaperOp_le_left costs weights first op)

private theorem fold_cheaperOp_le_mem (costs : PrimitiveCosts) (weights : Weights)
    (first : Op) (rest : List Op) (op : Op) (h : op ∈ first :: rest) :
    ((rest.foldl (cheaperOp costs weights) first).cost costs).score weights ≤
      (op.cost costs).score weights := by
  induction rest generalizing first with
  | nil =>
      have he := List.mem_singleton.mp h
      subst op
      exact Nat.le_refl _
  | cons next rest ih =>
      rcases List.mem_cons.mp h with he | h
      · subst op
        exact fold_cheaperOp_le_first costs weights first (next :: rest)
      · rcases List.mem_cons.mp h with he | h
        · subst op
          exact (fold_cheaperOp_le_first costs weights _ rest).trans
            (cheaperOp_le_right costs weights first next)
        · exact ih _ (List.mem_cons_of_mem _ h)

theorem cheapestGeneration_le_mem (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack : Stack) (value : Value) (chosen other : Op)
    (hchosen : cheapestGeneration costs weights spills stack value = some chosen)
    (hother : other ∈ generationOps spills stack value) :
    (chosen.cost costs).score weights ≤ (other.cost costs).score weights := by
  unfold cheapestGeneration at hchosen
  cases hg : generationOps spills stack value with
  | nil => simp [hg] at hother
  | cons first rest =>
      simp only [hg, Option.some.injEq] at hchosen
      rw [← hchosen]
      exact fold_cheaperOp_le_mem costs weights first rest other (by simpa [hg] using hother)

end Shuffler.Optimality
