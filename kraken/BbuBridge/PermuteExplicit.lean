module

public import BbuBridge.Permute
import all BbuBridge.Permute
public import Shuffler.Permute.Normalization
import all Shuffler.Permute.Normalization

@[expose] public section

/-!
The list `Bbu.permute` with an explicit permutation is the original
`Shuffler.Permute.permute`. The model gets the permutation as the list of the destinations
(`destList`).
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

theorem permute_corr {e : Bbu.Env} {source : Stack} {st : Bbu.St} {state : OState e source}
    (h : Rel e st state) (perm : Permute.Permutation state.stack) :
    ResCorr (Rel e) (Bbu.permute st (destList perm)) (Permute.permute state perm) := by
  have hl := h.len
  have hvals : state.stack = (st.slots.map Bbu.Slot.val).map decode := by
    rw [h.stack, List.map_map]
    rfl
  have hcan : ∀ v ∈ st.slots.map Bbu.Slot.val, Canon v := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
    exact h.canon s hs
  rw [Permute.permute_eq_normalize]
  unfold Bbu.permute
  have hN := normalize_corr _ hcan state.stack hvals perm
  generalize Bbu.normalize _ _ = x at hN ⊢
  generalize Permute.normalize _ _ = y at hN ⊢
  rcases x with (_ | _) | p <;> rcases y with (_ | _) | r <;> simp only [Corr] at hN
  · exact trivial
  subst hN
  rw [except_ok_bind]
  show ResCorr (Rel e) ((Except.ok (destList r) : Bbu.M _).bind _) _
  simp only [Except.bind]
  rw [dite_eq_left (isPerm_destList r)]
  by_cases h0 : st.len = 0
  · rw [ite_eq_left h0, dite_eq_right (by omega)]
    exact ⟨rfl, h⟩
  · rw [ite_eq_right h0, dite_eq_left (by omega)]
    exact go_corr st state _ r _ h rfl

-- A done `Bbu.permute` keeps the number of slots.
theorem permute_len {st st' : Bbu.St} {p : List Nat} (h : Bbu.permute st p = .ok st') :
    st'.len = st.len := by
  unfold Bbu.permute at h
  rcases hn : Bbu.normalize (st.slots.map Bbu.Slot.val) p with _ | q <;> rw [hn] at h
  · cases h
  · simp only [Except.bind] at h
    by_cases hq : Bbu.IsPerm q
    · rw [dite_eq_left hq] at h
      by_cases h0 : st.len = 0
      · rw [ite_eq_left h0] at h
        cases h
        rfl
      · rw [ite_eq_right h0] at h
        exact go_len _ _ h
    · rw [dite_eq_right hq] at h
      cases h

end BbuBridge
