module

public import ShufflerBridge.Emission.Statements
import all ShufflerBridge.Emission.Statements
import all Shuffler.BuildBottomUp.Lemmas.Invariants

@[expose] public section

/-!
The initial original state of valid model inputs is valid.
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

-- A mapping that binds every source slot leaves `n - m` target slots unbound.
private theorem initValid_unmapped {m n : Nat} (f : Mapping m n) (h : ∀ i, (f i).isSome) :
    f.unmapped_target_slots = n - m := by
  let g : Fin m → Fin n := fun i => (f i).get (h i)
  have hg : ∀ i, f i = some (g i) := fun i => by simp [g]
  have hinj : Function.Injective g := fun a b hab =>
    f.inj (hg a) (by rw [hg b, hab]; rfl)
  -- The bound target slots are the image of `g`.
  have himg : Finset.univ.filter (fun j => ¬ f.symm j = none) = Finset.univ.image g := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hj
      exact ⟨i, Option.some_inj.mp ((hg i).symm.trans ((PEquiv.eq_some_iff f).mp hi))⟩
    · rintro ⟨i, rfl⟩
      rw [(PEquiv.eq_some_iff f).mpr (hg i)]
      simp
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun j => f.symm j = none)
  rw [himg, Finset.card_image_of_injective _ hinj] at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  unfold Mapping.unmapped_target_slots
  omega

theorem initValid : InitValidStmt := by
  intro e source dests h
  have hle := h.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [initState, List.length_map, FlatShuffler.Env.n] at hle ⊢
    omega
  · simp only [initState]
    rw [initValid_unmapped _ (fun i => by simp [ofDests]), tgt_length]
    simp
  · intro i
    have hi : i.val < e.target.length := by simpa using i.isLt
    have ht : (decodedTargetStack e)[i] = decodeStackSlot e.target[i.val] := by simp [decodedTargetStack]
    simp only [State.isAvailable, Stack.shallowestCopyPosition_isSome]
    rw [ht, ← isFree_iff, ← isSpilled_iff e _ _
      (List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hi)))]
    rcases h.available _ (List.getElem_mem hi) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (List.mem_map_of_mem h1))
  · -- A slot is bound for each function return label of the target.
    intro j hj
    have hjl : j.val < e.target.length := by simpa using j.isLt
    have ht : (decodedTargetStack e)[j] = decodeStackSlot e.target[j.val] := by simp [decodedTargetStack]
    rw [ht, isFRL_iff (h.canonTarget _ (List.getElem_mem hjl))] at hj
    obtain ⟨i, hi, hid⟩ := List.getElem_of_mem (h.labels j.val hjl hj)
    have hil : i < (source.map decodeStackSlot).length := by simpa [← h.length] using hi
    refine Option.isSome_iff_exists.mpr ⟨⟨i, hil⟩, (PEquiv.eq_some_iff _).mpr ?_⟩
    simp only [initState, ofDests]
    exact congrArg some (Fin.ext hid)

end ShufflerBridge.Emission
