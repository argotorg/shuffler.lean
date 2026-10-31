import BbuBridge.PermuteExplicit
import BbuKraken.ModelLowest
import Shuffler.PermuteAtLowestHeight.Lemmas

/-!
The list `Bbu.lowest` (`BbuKraken/ModelLowest.lean`) is the original
`Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight`. The list model does not keep the planned
mapping: it gets the planned `positionOf` as a list `pl` with the same holes (`PlanCorr`).
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The list `pl` has the holes of the planned mapping: the target offsets that no slot is planned
-- for.
def PlanCorr {e : Bbu.Env} {source : Stack} (state : OState e source) (pl : List (Option Nat)) :
    Prop :=
  ∀ j : Fin (tgt e).length, (pl[j.val]?.join).isSome = (state.planned_mapping.positionOf j).isSome

/-! ## Binds and loops -/

theorem rescorr_of_corr {α β : Type} {source target : Stack} {spills : SpillSet}
    {R : α → β → Prop} {S : Bbu.St → State source target spills → Prop} {x : Bbu.M α}
    {y : Except ShuffleErr β} {f : α → Bbu.M Bbu.St}
    {g : β → Except ShuffleErr (Result source target spills)}
    (h : Corr R x y) (hf : ∀ a b, R a b → ResCorr S (f a) (g b)) :
    ResCorr S (x.bind f) (y >>= g) := by
  rcases x with (_ | _) | a <;> rcases y with (_ | _) | b <;> simp_all [Corr, ResCorr, Except.bind, bind]

theorem bind_assoc' {α β γ : Type} (x : Bbu.M α) (f : α → Bbu.M β) (g : β → Bbu.M γ) :
    (x.bind f).bind g = x.bind fun a => (f a).bind g := by
  cases x <;> rfl

-- A model `foldlM` over the values of a list of `Fin n` and an original `forIn` that only yields.
theorem corr_foldlM_forIn {α β : Type} {n : Nat} {R : α → β → Prop} (f : α → Nat → Bbu.M α)
    (g : Fin n → β → Except ShuffleErr (ForInStep β))
    (hstep : ∀ i a b, R a b → Corr (fun a' s => ∃ b', s = .yield b' ∧ R a' b') (f a i.val) (g i b)) :
    ∀ (xs : List (Fin n)) a b, R a b → Corr R ((xs.map Fin.val).foldlM f a) (forIn xs b g) := by
  intro xs
  induction xs with
  | nil => intro a b hab; exact hab
  | cons x xs ih =>
    intro a b hab
    rw [List.map_cons, List.foldlM_cons, List.forIn_cons]
    have hs := hstep x a b hab
    generalize f a x.val = u at hs ⊢
    generalize g x b = v at hs ⊢
    rcases u with (_ | _) | a' <;> rcases v with (_ | _) | s <;> simp only [Corr] at hs
    · exact trivial
    · obtain ⟨b', rfl, hr⟩ := hs
      exact ih a' b' hr

theorem destList_one (n : Nat) : destList (1 : Equiv.Perm (Fin n)) = List.range n := by
  apply List.ext_getElem <;> simp [destList]

/-! ## `permuteAtLowestHeight` -/

theorem lowest_corr {e : Bbu.Env} {source : Stack} {st : Bbu.St} {state : OState e source}
    (h : Rel e st state) {pl : List (Option Nat)} (hpl : PlanCorr state pl) :
    ResCorr (Rel e) (Bbu.lowest e.n pl st) (PermuteAtLowestHeight.permuteAtLowestHeight state) := by
  unfold Bbu.lowest Bbu.lowestPerm PermuteAtLowestHeight.permuteAtLowestHeight
  dsimp only
  rw [bind_assoc']
  have hl := h.len
  refine rescorr_of_corr (R := fun (a : Bbu.LScan)
      (b : Permute.Permutation state.stack × List (Fin state.stack.length) ×
        List (Fin state.stack.length)) =>
      a.perm = destList b.1 ∧ a.holes = b.2.1.map Fin.val ∧ a.parked = b.2.2.map Fin.val) ?_ ?_
  · rw [← map_val_finRange, ← hl]
    refine corr_foldlM_forIn _ _ ?_ _ _ _ ⟨by rw [destList_one, map_val_finRange], rfl, rfl⟩
    intro i a b ⟨hp, hh, hk⟩
    obtain ⟨j, hj, hjd⟩ := h.mapping i
    have hs : (state.mapping.destinationOf i).isSome = true := by simp [Mapping.destinationOf, hj]
    simp only [requires_of_true _ hs, except_ok_bind]
    unfold Bbu.lowestStep
    by_cases hn : e.n ≤ i.val
    · rw [ite_eq_left hn]
      have : ¬ i.val < (tgt e).length := by rw [tgt_length]; omega
      simp only [index, dite_eq_right this]
      exact trivial
    · rw [ite_eq_right hn]
      have hi : i.val < (tgt e).length := by rw [tgt_length]; omega
      rw [show index (tgt e).length i.val = .ok ⟨i.val, hi⟩ from index_eq ⟨i.val, hi⟩, except_ok_bind]
      simp only [Mapping.destinationOf, hj, Option.get_some]
      have hhole : Bbu.isHole pl i = !(state.planned_mapping.positionOf ⟨i.val, hi⟩).isSome := by
        have := hpl ⟨i.val, hi⟩
        unfold Bbu.isHole
        rw [← this]
        cases (pl[i.val]?).join <;> rfl
      have SS := And.intro hjd hl
      by_cases hP : st.len ≤ st.dest i
      · have hpar : Bbu.isParked st i = true := by simp [Bbu.isParked, hP]
        have hP' : (j : Nat) ≥ state.stack.length := by omega
        cases hH : (state.planned_mapping.positionOf ⟨i.val, hi⟩).isSome <;>
          simp only [hpar, hhole, hH, hP', not_true_eq_false, not_false_eq_true, and_true,
            and_false, Bool.not_true,
            Bool.not_false, Bool.and_true, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte]
        · exact ⟨_, rfl, by rw [destList_setValue, hp], hh, hk⟩
        · exact ⟨_, rfl, hp, hh, by rw [hk, List.map_append]; rfl⟩
      · have hpar : Bbu.isParked st i = false := by simp [Bbu.isParked, hP]
        have hP' : ¬(j : Nat) ≥ state.stack.length := by omega
        have hj' : (j : Nat) < state.stack.length := by omega
        cases hH : (state.planned_mapping.positionOf ⟨i.val, hi⟩).isSome <;>
          simp only [hpar, hhole, hH, hP', not_true_eq_false, not_false_eq_true, and_true,
            and_false, Bool.not_true,
            Bool.not_false, Bool.and_true, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte,
            show index state.stack.length j.val = .ok ⟨j.val, hj'⟩ from index_eq ⟨j.val, hj'⟩,
            except_ok_bind]
        · exact ⟨_, rfl, by rw [destList_setValue, hp, ← hjd], by rw [hh, List.map_append]; rfl, hk⟩
        · exact ⟨_, rfl, by rw [destList_setValue, hp, ← hjd], hh, hk⟩
  · intro a b ⟨hp, hh, hk⟩
    have hlen : a.parked.length = b.2.2.length ∧ a.holes.length = b.2.1.length := by
      rw [hk, hh]; simp
    by_cases hs : b.2.2.length = b.2.1.length
    · have hne : ¬(a.parked.length ≠ a.holes.length) := by rw [hlen.1, hlen.2]; exact not_not.mpr hs
      rw [ite_eq_right hne, requires_of_true _ hs, except_ok_bind, List.forIn_pure_yield_eq_foldl]
      have hM : (b.2.2.mergeSort fun x1 x2 => decide (x1 ≤ x2)).map Fin.val =
          a.parked.mergeSort fun a b => decide (a ≤ b) := by
        rw [hk, List.map_mergeSort (s := fun a b => decide (a ≤ b))
          (fun a _ b _ => by simp only [Fin.le_def])]
      show ResCorr (Rel e) (Bbu.permute st _) (Permute.permute state _)
      convert permute_corr h _ using 2
      rw [show List.range a.holes.length = (List.finRange b.2.1.length).map Fin.val by
        rw [map_val_finRange, hlen.2], List.foldl_map, hp]
      apply List.foldl_hom destList
      intro x i
      have hi : i.val < (b.2.2.mergeSort fun x1 x2 => decide (x1 ≤ x2)).length := by
        rw [List.length_mergeSort, hs]; exact i.isLt
      rw [destList_setValue, ← hM, hh, getElem!_map_val _ i hi, getElem!_map_val _ i i.isLt]
      rfl
    · rw [ite_eq_left (by rw [hlen.1, hlen.2]; exact hs)]
      simp only [requires, dite_eq_right hs]
      exact trivial

end BbuBridge
