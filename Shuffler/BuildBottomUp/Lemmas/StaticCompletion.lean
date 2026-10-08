import Shuffler.BuildBottomUp.Lemmas.StaticPermutation
import Shuffler.BuildBottomUp.Lemmas.StaticCycles

namespace Shuffler.BuildBottomUp.Success

-- These state expressions describe the effects of the existing actions.
abbrev retagged (state : State source target spills) (a b : Fin state.stack.length) :
    State source target spills :=
  {state with mapping := state.mapping.swapDestinations a b}

theorem retagged_valid (state : State source target spills) (h : state.Valid)
    (a b : Fin state.stack.length) : (retagged state a b).Valid := by
  refine ⟨h.size, ?_, h.available⟩
  simpa [retagged] using h.pending

@[simp] theorem holes_retagged (state : State source target spills)
    (a b : Fin state.stack.length) : holes (retagged state a b) = holes state := by
  ext j
  simp only [mem_holes]
  change (state.mapping.swapDestinations a b).symm j = none ↔ state.mapping.symm j = none
  rw [Mapping.swapDestinations_symm_apply]
  simp

@[simp] theorem holeList_retagged (state : State source target spills)
    (a b : Fin state.stack.length) : holeList (retagged state a b) = holeList state := by
  simp [holeList]

def stackIndex (state : State source target spills) (h : state.Valid)
    (i : Fin state.stack.length) : Fin target.length :=
  ⟨i.val, by have := h.size; omega⟩

@[simp] theorem stackIndex_val (state : State source target spills) (h : state.Valid)
    (i : Fin state.stack.length) : (stackIndex state h i).val = i.val := rfl

theorem completedPermutation_retagged (state : State source target spills) (h : state.Valid)
    (a b : Fin state.stack.length) :
    completedPermutation (retagged state a b) (retagged_valid state h a b) =
      completedPermutation state h * Equiv.swap (stackIndex state h a) (stackIndex state h b) := by
  ext i
  rw [completedPermutation_val, Equiv.Perm.mul_apply, completedPermutation_val]
  by_cases hia : i = stackIndex state h a
  · subst i
    simp only [completedNext, retagged, stackIndex_val, a.isLt, b.isLt, ↓reduceDIte,
      Equiv.swap_apply_left, Mapping.swapDestinations_apply_left]
    have hs := source_total state h b
    cases hb : state.mapping b with
    | none => simp [hb] at hs
    | some j => rfl
  by_cases hib : i = stackIndex state h b
  · subst i
    simp only [completedNext, retagged, stackIndex_val, a.isLt, b.isLt, ↓reduceDIte,
      Equiv.swap_apply_right, Mapping.swapDestinations_apply_right]
    have hs := source_total state h a
    cases ha : state.mapping a with
    | none => simp [ha] at hs
    | some j => rfl
  rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  by_cases hi : i.val < state.stack.length
  · have hia' : (⟨i.val, hi⟩ : Fin state.stack.length) ≠ a := by
      intro he
      apply hia
      apply Fin.ext
      simpa only [stackIndex_val] using congrArg (fun j : Fin state.stack.length => j.val) he
    have hib' : (⟨i.val, hi⟩ : Fin state.stack.length) ≠ b := by
      intro he
      apply hib
      apply Fin.ext
      simpa only [stackIndex_val] using congrArg (fun j : Fin state.stack.length => j.val) he
    simp only [completedNext, retagged, hi, ↓reduceDIte]
    rw [Mapping.swapDestinations_apply_of_ne _ hia' hib']
  · simp only [completedNext, show ¬i.val < (retagged state a b).stack.length from hi,
      ↓reduceDIte, holeList_retagged]


-- The trace can come from either PUSH, LOAD, or DUP.
abbrev appended (state : State source target spills) (d : Fin target.length)
    (hd : state.mapping.symm d = none) (v : Value)
    (trace : Trace spills source (state.stack ++ [v])) : State source target spills where
  planned_mapping := state.planned_mapping
  stack := state.stack ++ [v]
  trace := trace
  mapping := (show state.stack.length + 1 = (state.stack ++ [v]).length by simp) ▸
    state.mapping.push d hd
  pending_generations := state.pending_generations - 1

@[simp] theorem holes_appended (state : State source target spills) (d : Fin target.length)
    (hd : state.mapping.symm d = none) (v : Value)
    (trace : Trace spills source (state.stack ++ [v])) :
    holes (appended state d hd v trace) = (holes state).erase d := by
  ext j
  simp only [mem_holes, Finset.mem_erase, mem_holes]
  by_cases hj : j = d
  · subst j
    simp [hd]
  · simp [hj, Mapping.push_symm_apply_of_ne _ _ _ _ hj]

theorem holeList_cons_appended (state : State source target spills) (d : Fin target.length)
    (hd : state.mapping.symm d = none) (v : Value)
    (trace : Trace spills source (state.stack ++ [v]))
    (hmin : ∀ j, state.mapping.symm j = none → d ≤ j) :
    holeList state = d :: holeList (appended state d hd v trace) := by
  have hdmem : d ∈ holes state := (mem_holes state d).mpr hd
  have hsort := Finset.sort_insert (s := (holes state).erase d) (· ≤ ·)
    (fun j hj => hmin j ((mem_holes state j).mp (Finset.mem_of_mem_erase hj)))
    (Finset.notMem_erase d (holes state))
  simpa only [Finset.insert_erase hdmem, holeList, holes_appended] using hsort


private theorem castMapping_apply {n n' m : Nat} (mapping : Mapping n m) (h : n = n')
    (i : Fin n') : (h ▸ mapping) i = mapping (Fin.cast h.symm i) := by
  cases h
  rfl

theorem appended_mapping (state : State source target spills) (d : Fin target.length)
    (hd : state.mapping.symm d = none) (v : Value)
    (trace : Trace spills source (state.stack ++ [v]))
    (i : Fin (state.stack ++ [v]).length) :
    (appended state d hd v trace).mapping i =
      if hi : i.val < state.stack.length then state.mapping ⟨i.val,hi⟩ else some d := by
  change ((show state.stack.length + 1 = (state.stack ++ [v]).length by simp) ▸
    state.mapping.push d hd) i = _
  rw [castMapping_apply]
  by_cases hi : i.val < state.stack.length
  · rw [dite_eq_left hi]
    have he : Fin.cast (show (state.stack ++ [v]).length = state.stack.length + 1 by simp) i =
        (⟨i.val,hi⟩ : Fin state.stack.length).castSucc := by apply Fin.ext; rfl
    rw [he, Mapping.push_apply_castSucc]
  · rw [dite_eq_right hi]
    have he : Fin.cast (show (state.stack ++ [v]).length = state.stack.length + 1 by simp) i =
        Fin.last state.stack.length := by
      apply Fin.ext
      have := i.isLt
      simp only [List.length_append, List.length_singleton] at this
      change i.val = state.stack.length
      omega
    rw [he, Mapping.push_apply_top]

theorem completedNext_appended (state : State source target spills) (d : Fin target.length)
    (hd : state.mapping.symm d = none) (v : Value)
    (trace : Trace spills source (state.stack ++ [v]))
    (hmin : ∀ j, state.mapping.symm j = none → d ≤ j) (i : Nat) :
    completedNext (appended state d hd v trace) i = completedNext state i := by
  have hlist := holeList_cons_appended state d hd v trace hmin
  by_cases hi : i < state.stack.length
  · have hi' : i < (state.stack ++ [v]).length := by simp; omega
    simp only [completedNext, hi, hi', ↓reduceDIte]
    have hm := appended_mapping state d hd v trace ⟨i,hi'⟩
    simp only [hi, ↓reduceDIte] at hm
    exact congrArg (fun x : Option (Fin target.length) => (x.map Fin.val).getD i) hm
  by_cases he : i = state.stack.length
  · subst i
    have hi' : state.stack.length < (state.stack ++ [v]).length := by simp
    simp only [completedNext, hi, hi', ↓reduceDIte]
    have hm := appended_mapping state d hd v trace ⟨state.stack.length,hi'⟩
    simp only [Nat.lt_irrefl, ↓reduceDIte] at hm
    have he := congrArg (fun x : Option (Fin target.length) => (x.map Fin.val).getD state.stack.length) hm
    simpa only [hlist, Nat.sub_self, List.getElem?_cons_zero] using he
  · have hi' : ¬i < (state.stack ++ [v]).length := by simp; omega
    simp only [completedNext, hi, hi', ↓reduceDIte]
    rw [hlist]
    have hpos : 0 < i - state.stack.length := by omega
    have hindex : i - state.stack.length = (i - (state.stack ++ [v]).length) + 1 := by
      simp only [List.length_append, List.length_singleton]
      omega
    simp only [hindex, List.getElem?_cons_succ]

-- Taking the first remaining hole consumes the first preallocated coordinate.
theorem completedPermutation_appended (state : State source target spills) (h : state.Valid)
    (d : Fin target.length) (hd : state.mapping.symm d = none) (v : Value)
    (trace : Trace spills source (state.stack ++ [v]))
    (hnext : (appended state d hd v trace).Valid)
    (hmin : ∀ j, state.mapping.symm j = none → d ≤ j) :
    completedPermutation (appended state d hd v trace) hnext = completedPermutation state h := by
  ext i
  simp only [completedPermutation_val]
  exact completedNext_appended state d hd v trace hmin i.val


theorem holes_eq_of_inverse_eq (state next : State source target spills)
    (hm : ∀ j, (state.mapping.symm j).map Fin.val = (next.mapping.symm j).map Fin.val) :
    holes state = holes next := by
  ext j
  simp only [mem_holes]
  have he := hm j
  cases hs : state.mapping.symm j <;> cases hn : next.mapping.symm j <;> simp_all

theorem mapping_eq_of_inverse_eq (state next : State source target spills)
    (hm : ∀ j, (state.mapping.symm j).map Fin.val = (next.mapping.symm j).map Fin.val)
    (i : Fin state.stack.length) (i' : Fin next.stack.length) (hi : i.val = i'.val) :
    state.mapping i = next.mapping i' := by
  have transfer (j : Fin target.length) : state.mapping i = some j ↔ next.mapping i' = some j := by
    rw [← state.mapping.eq_some_iff, ← next.mapping.eq_some_iff]
    have he := hm j
    cases hs : state.mapping.symm j <;> cases hn : next.mapping.symm j <;>
      simp_all [Fin.ext_iff]
  cases hs : state.mapping i with
  | some j => exact ((transfer j).mp hs).symm
  | none =>
    cases hn : next.mapping i' with
    | none => rfl
    | some j => have := (transfer j).mpr hn; simp [hs] at this

theorem completedNext_congr (state next : State source target spills)
    (hlen : state.stack.length = next.stack.length)
    (hm : ∀ j, (state.mapping.symm j).map Fin.val = (next.mapping.symm j).map Fin.val)
    (i : Nat) : completedNext state i = completedNext next i := by
  by_cases hi : i < state.stack.length
  · have hi' : i < next.stack.length := by omega
    simp only [completedNext, hi, hi', ↓reduceDIte]
    rw [mapping_eq_of_inverse_eq state next hm ⟨i,hi⟩ ⟨i,hi'⟩ rfl]
  · have hi' : ¬i < next.stack.length := by omega
    have hh : holeList state = holeList next := congrArg (fun s => s.sort) (holes_eq_of_inverse_eq state next hm)
    simp only [completedNext, hi', ↓reduceDIte, hh, hlen]

-- Traces, planned mappings, and stack values do not affect this permutation.
theorem completedPermutation_congr (state next : State source target spills)
    (hstate : state.Valid) (hnext : next.Valid)
    (hlen : state.stack.length = next.stack.length)
    (hm : ∀ j, (state.mapping.symm j).map Fin.val = (next.mapping.symm j).map Fin.val) :
    completedPermutation state hstate = completedPermutation next hnext := by
  ext i
  simp only [completedPermutation_val]
  exact completedNext_congr state next hlen hm i.val

end Shuffler.BuildBottomUp.Success
