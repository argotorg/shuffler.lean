import Shuffler.BuildBottomUp.Lemmas.StaticData

namespace Shuffler.BuildBottomUp

namespace Success

def boundTargets (initial : State source target spills) : Finset (Fin target.length) :=
  Finset.univ.filter (fun j => (initial.mapping.symm j).isSome)

theorem boundTargets_card (initial : State source target spills) (h : initial.Valid) :
    (boundTargets initial).card = initial.stack.length := by
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun j : Fin target.length => initial.mapping.symm j = none)
  have hp := h.pending
  have hs := h.size
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hn : (Finset.univ.filter (fun j => ¬initial.mapping.symm j = none)) =
      boundTargets initial := by
    ext j
    simp [boundTargets, Option.isSome_iff_ne_none]
  rw [hn] at hc
  change initial.mapping.unmapped_target_slots + _ = _ at hc
  omega

theorem source_total (initial : State source target spills) (h : initial.Valid) :
    ∀ i, (initial.mapping i).isSome := by
  let position : boundTargets initial → Fin initial.stack.length := fun j =>
    (initial.mapping.symm j.val).get (by
      have hj := j.property
      simpa [boundTargets] using hj)
  have hposition (j : boundTargets initial) : initial.mapping (position j) = some j.val :=
    initial.mapping.eq_some_iff.mp (Option.some_get _).symm
  have hinj : Function.Injective position := by
    intro j k hjk
    apply Subtype.ext
    apply Option.some.inj
    rw [← hposition j, ← hposition k, hjk]
  have hsurj : Function.Surjective position :=
    ((Fintype.bijective_iff_injective_and_card position).mpr
      ⟨hinj, by simp [boundTargets_card initial h]⟩).2
  intro i
  obtain ⟨j, rfl⟩ := hsurj i
  rw [hposition]
  rfl

def holeOrder (initial : State source target spills) (h : initial.Valid) :
    Fin initial.pending_generations ≃o holes initial :=
  (holes initial).orderIsoOfFin h.pending

-- This is the completed assignment on the old and the added coordinates.
def completedDestination (initial : State source target spills) (h : initial.Valid) :
    Fin (initial.stack.length + initial.pending_generations) → Fin target.length :=
  Fin.addCases
    (fun i => (initial.mapping i).get (source_total initial h i))
    (fun k => (holeOrder initial h k).val)

theorem completedDestination_surjective (initial : State source target spills) (h : initial.Valid) :
    Function.Surjective (completedDestination initial h) := by
  intro j
  cases hj : initial.mapping.symm j with
  | some i =>
    refine ⟨Fin.castAdd initial.pending_generations i, ?_⟩
    simp only [completedDestination, Fin.addCases_left]
    apply Option.some.inj
    rw [Option.some_get]
    exact initial.mapping.eq_some_iff.mp hj
  | none =>
    let hole : holes initial := ⟨j, (mem_holes initial j).mpr hj⟩
    refine ⟨Fin.natAdd initial.stack.length ((holeOrder initial h).symm hole), ?_⟩
    simp only [completedDestination, Fin.addCases_right, OrderIso.apply_symm_apply]
    rfl

noncomputable def completedPermutation (initial : State source target spills) (h : initial.Valid) :
    Equiv.Perm (Fin target.length) :=
  (finCongr h.size.symm).trans
    (Equiv.ofBijective (completedDestination initial h)
      ((Fintype.bijective_iff_surjective_and_card _).mpr
        ⟨completedDestination_surjective initial h, by simp [h.size]⟩))

theorem completedDestination_val (initial : State source target spills) (h : initial.Valid)
    (i : Fin (initial.stack.length + initial.pending_generations)) :
    (completedDestination initial h i).val = completedNext initial i.val := by
  refine Fin.addCases ?_ ?_ i
  · intro pos
    simp only [completedDestination, Fin.addCases_left, Fin.val_castAdd, completedNext,
      pos.isLt, ↓reduceDIte]
    have hs := Option.some_get (source_total initial h pos)
    conv_rhs => rw [← hs]
    rfl
  · intro k
    simp only [completedDestination, Fin.addCases_right, Fin.val_natAdd, completedNext,
      show ¬initial.stack.length + k.val < initial.stack.length by omega, ↓reduceDIte,
      Nat.add_sub_cancel_left]
    have hk : k.val < (holeList initial).length := by
      rw [length_holeList, h.pending]
      exact k.isLt
    simp only [List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
    rfl

theorem completedPermutation_val (initial : State source target spills) (h : initial.Valid)
    (i : Fin target.length) :
    (completedPermutation initial h i).val = completedNext initial i.val := by
  exact completedDestination_val initial h (Fin.cast h.size.symm i)

theorem completedNext_lt (initial : State source target spills) (h : initial.Valid)
    (i : Nat) (hi : i < target.length) : completedNext initial i < target.length := by
  rw [← completedPermutation_val initial h ⟨i, hi⟩]
  exact (completedPermutation initial h ⟨i, hi⟩).isLt

end Success

end Shuffler.BuildBottomUp
