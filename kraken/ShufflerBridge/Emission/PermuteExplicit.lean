module

public import ShufflerBridge.Emission.Permute
import all ShufflerBridge.Emission.Permute
public import Shuffler.Permute.Normalization
import all Shuffler.Permute.Normalization

@[expose] public section

/-!
The list `FlatShuffler.permute` with an explicit permutation is the original
`Shuffler.Permute.permute`. The model gets the permutation as the list of the destinations
(`destList`).
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

theorem permute_corr {e : FlatShuffler.Env} {source : Stack} {st : FlatShuffler.St} {state : OState e source}
    (h : Rel e st state) (perm : Permute.Permutation state.stack) :
    ResCorr (Rel e) (FlatShuffler.permute st (destList perm)) (Permute.permute state perm) := by
  have hl := h.len
  have hvals : state.stack = (st.slots.map FlatShuffler.Slot.val).map decodeStackSlot := by
    rw [h.stack, List.map_map]
    rfl
  have hcan : ∀ v ∈ st.slots.map FlatShuffler.Slot.val, StackSlotHasCanonicalEncoding v := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
    exact h.canon s hs
  rw [Permute.permute_eq_normalize]
  unfold FlatShuffler.permute
  have hN := normalize_corr _ hcan state.stack hvals perm
  generalize FlatShuffler.normalize _ _ = x at hN ⊢
  generalize Permute.normalize _ _ = y at hN ⊢
  rcases x with (_ | _) | p <;> rcases y with (_ | _) | r <;> simp only [Corr] at hN
  · exact trivial
  subst hN
  rw [except_ok_bind]
  show ResCorr (Rel e) ((Except.ok (destList r) : FlatShuffler.M _).bind _) _
  simp only [Except.bind]
  rw [dite_eq_left (isPerm_destList r)]
  by_cases h0 : st.len = 0
  · rw [ite_eq_left h0, dite_eq_right (by omega)]
    exact ⟨rfl, h⟩
  · rw [ite_eq_right h0, dite_eq_left (by omega)]
    exact go_corr st state _ r _ h rfl

-- A done `FlatShuffler.permute` keeps the stackSlotIdentity of slots.
theorem permute_len {st st' : FlatShuffler.St} {p : List Nat} (h : FlatShuffler.permute st p = .ok st') :
    st'.len = st.len := by
  unfold FlatShuffler.permute at h
  rcases hn : FlatShuffler.normalize (st.slots.map FlatShuffler.Slot.val) p with _ | q <;> rw [hn] at h
  · cases h
  · simp only [Except.bind] at h
    by_cases hq : FlatShuffler.IsPerm q
    · rw [dite_eq_left hq] at h
      by_cases h0 : st.len = 0
      · rw [ite_eq_left h0] at h
        cases h
        rfl
      · rw [ite_eq_right h0] at h
        exact go_len _ _ h
    · rw [dite_eq_right hq] at h
      cases h

end ShufflerBridge.Emission
