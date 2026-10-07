import Shuffler.Optimality.GenerationChoice

namespace Shuffler.Optimality

private theorem cheaperOp_mem (costs : PrimitiveCosts) (weights : Weights) (a b : Op) :
    cheaperOp costs weights a b = a ∨ cheaperOp costs weights a b = b := by
  unfold cheaperOp
  split <;> simp

private theorem fold_cheaperOp_mem (costs : PrimitiveCosts) (weights : Weights)
    (first : Op) (rest : List Op) :
    rest.foldl (cheaperOp costs weights) first ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp
  | cons op rest ih =>
      simp only [List.foldl_cons]
      rcases cheaperOp_mem costs weights first op with he | he
      · rw [he]
        rcases List.mem_cons.mp (ih first) with hm | hm
        · exact List.mem_cons.mpr (Or.inl hm)
        · exact List.mem_cons_of_mem first (List.mem_cons_of_mem op hm)
      · rw [he]
        exact List.mem_cons_of_mem first (ih op)

theorem cheapestGeneration_mem (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack : Stack) (value : Value) (op : Op)
    (h : cheapestGeneration costs weights spills stack value = some op) :
    op ∈ generationOps spills stack value := by
  unfold cheapestGeneration at h
  cases hg : generationOps spills stack value with
  | nil => simp [hg] at h
  | cons first rest =>
      simp only [hg, Option.some.injEq] at h
      rw [← h]
      exact fold_cheaperOp_mem costs weights first rest

theorem cheapestGeneration_isSome (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack : Stack) (value : Value)
    (h : generationOps spills stack value ≠ []) :
    (cheapestGeneration costs weights spills stack value).isSome := by
  unfold cheapestGeneration
  cases hg : generationOps spills stack value with
  | nil => exact False.elim (h hg)
  | cons first rest => rfl

theorem generationOps_nonempty (spills : SpillSet) (stack : Stack) (value : Value)
    (h : Shuffler.Placement.Free spills value ∨
      value ∈ stack.reverse.take (MAX_DUP_DEPTH + 1)) :
    generationOps spills stack value ≠ [] := by
  rcases h with (hf | hs) | hc
  · simp [generationOps, hf]
  · cases value with
    | Var id =>
        have hi : id ∈ spills := hs
        simp [generationOps, hi]
    | Lit _ | Wildcard | FunctionReturnLabel => simp [SpillSet.is_spilled] at hs
  · simp [generationOps, hc]

theorem generationOp_target (spills : SpillSet) (stack : Stack) (value : Value) (op : Op)
    (h : op ∈ generationOps spills stack value) :
    (replayStep spills stack op).map (fun result => result.target) = some (stack ++ [value]) := by
  simp only [generationOps, List.mem_append] at h
  rcases h with (hc | hp) | hl
  · split at hc
    next hm =>
      simp only [List.mem_singleton] at hc
      subst op
      let readable := stack.reverse.take (MAX_DUP_DEPTH + 1)
      let pos := readable.idxOf value
      have hpos : pos < readable.length := List.idxOf_lt_length_iff.mpr hm
      have hlen : readable.length = min (MAX_DUP_DEPTH + 1) stack.length := by
        simp [readable]
      have hdepth : pos + 1 ≤ stack.length ∧ 1 ≤ pos + 1 ∧ pos + 1 ≤ MAX_DUP_DEPTH + 1 := by omega
      have hvalue : stack[stack.length - (pos + 1)]'(by omega) = value := by
        have hx := List.getElem_idxOf hpos
        rw [List.getElem_take, List.getElem_reverse] at hx
        convert hx using 1
        congr 1
        omega
      change (replayStep spills stack (.dup (pos + 1))).map
        (fun result => result.target) = some (stack ++ [value])
      simp only [replayStep, dite_eq_left hdepth, Option.map_some]
      exact congrArg (fun v => some (stack ++ [v])) hvalue
    next => simp at hc
  · split at hp
    next hf =>
      simp only [List.mem_singleton] at hp
      subst op
      simp only [replayStep, dite_eq_left hf, Option.map_some]
    next => simp at hp
  · cases value with
    | Var id =>
        by_cases hs : id ∈ spills
        · simp only [hs, ↓reduceIte, List.mem_singleton] at hl
          subst op
          simp only [replayStep, dite_eq_left hs, Option.map_some]
        · simp [hs] at hl
    | Lit _ | Wildcard | FunctionReturnLabel => simp at hl

end Shuffler.Optimality
