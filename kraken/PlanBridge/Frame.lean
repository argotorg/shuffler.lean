import BbuKraken.FlatSurplus

/-!
The members of the flat state that `removeSurplus` does not write: the target, the target size,
the spills and the pending generations. The size does not grow.
-/

namespace Bbu.Flat

structure SFrame (st st' : St) : Prop where
  target : st'.target = st.target
  tsize : st'.targetSize = st.targetSize
  spills : st'.spills = st.spills
  pend : st'.pend = st.pend
  size : st'.size.toNat ≤ st.size.toNat

theorem SFrame.refl (st : St) : SFrame st st := ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem SFrame.trans {a b c : St} (h : SFrame a b) (h' : SFrame b c) : SFrame a c :=
  ⟨h'.target.trans h.target, h'.tsize.trans h.tsize, h'.spills.trans h.spills,
    h'.pend.trans h.pend, Nat.le_trans h'.size h.size⟩

theorem swapDestinations_frame (st : St) (a b : Word) : SFrame st (swapDestinations st a b) :=
  ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem swapWith_frame (st : St) (pos : Word) : SFrame st (swapWith st pos).2 := by
  unfold swapWith; dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem pop_frame (st : St) : SFrame st (pop st).2 := by
  unfold pop stackPop mappingPop; dsimp only
  by_cases h : st.size = 0
  · simp only [h, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]; exact SFrame.refl _
  · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false]
    split <;> exact ⟨rfl, rfl, rfl, rfl, by bv_omega⟩

theorem blockSwapUnreachable_frame (st : St) (p : Word) :
    SFrame st (blockSwapUnreachable st p).2 := by
  unfold blockSwapUnreachable block
  split <;> exact ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

-- One pass: the state after the pass, or the result.
theorem surplusPass_frame (st : St) :
    (∀ st', surplusPass st = .ok st' → SFrame st st') ∧
      ∀ r, surplusPass st = .error r → SFrame st r.2 := by
  unfold surplusPass; dsimp only
  refine ⟨fun st' h => ?_, fun r h => ?_⟩
  all_goals
    repeat' split at h
    all_goals cases h
    all_goals first
      | exact SFrame.refl st
      | exact blockSwapUnreachable_frame _ _
      | exact swapDestinations_frame _ _ _
      | exact swapWith_frame _ _
      | exact pop_frame st
      | exact (swapDestinations_frame _ _ _).trans (pop_frame _)
      | exact (swapWith_frame _ _).trans (pop_frame _)

theorem surplusLoop_frame (st : St) (fuel : Nat) : SFrame st (surplusLoop st fuel).2 := by
  induction fuel generalizing st with
  | zero => exact SFrame.refl st
  | succ k ih =>
    unfold surplusLoop
    split
    · exact SFrame.refl st
    · split
      · next r h => exact (surplusPass_frame st).2 r h
      · next st' h => exact ((surplusPass_frame st).1 st' h).trans (ih st')

theorem removeSurplus_frame (st : St) : SFrame st (removeSurplus st).2 :=
  surplusLoop_frame st _

end Bbu.Flat
