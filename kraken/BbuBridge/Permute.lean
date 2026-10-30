import BbuBridge.Statements

/-!
The final permutation of the model (`Bbu.normalize`, then `Bbu.go`) is the
original `Shuffler.Permute.permute` (`normalize`, then `permute.go`). The model
gets a permutation as the list of the destinations (`destList`).
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The model of a permutation: entry `i` is the destination of position `i`.
def destList {n : Nat} (perm : Equiv.Perm (Fin n)) : List Nat :=
  List.ofFn fun i => (perm i).val

theorem length_destList {n : Nat} (perm : Equiv.Perm (Fin n)) : (destList perm).length = n := by
  simp [destList]

theorem getElem_destList {n : Nat} (perm : Equiv.Perm (Fin n)) (i : Nat)
    (h : i < (destList perm).length) :
    (destList perm)[i] = (perm ⟨i, by simpa [length_destList] using h⟩).val := by
  simp [destList]

theorem isPerm_destList {n : Nat} (perm : Equiv.Perm (Fin n)) : Bbu.IsPerm (destList perm) := by
  refine ⟨fun i h => ?_, fun i hi j hj hij => ?_⟩
  · rw [getElem_destList]; simp only [length_destList]
    exact (perm _).isLt
  · rw [getElem_destList, getElem_destList] at hij
    have := perm.injective (Fin.ext hij)
    simpa using this

/-! ## `normalize` -/

-- `Bbu.normalize` is `Permute.normalize`. The slots are canonical, so equal
-- values are equal slots.
theorem normalize_corr (vals : List Bbu.StackSlot) (hc : ∀ v ∈ vals, Canon v) (stack : Stack)
    (hs : stack = vals.map decode) (perm : Permute.Permutation stack) :
    Corr (fun p r => p = destList r) (Bbu.normalize vals (destList perm))
      (Permute.normalize stack perm) := by
  sorry -- wf:todo

/-! ## `permute.go` -/

theorem swapPos_len (st : Bbu.St) (pos : Nat) : (Bbu.swapPos st pos).len = st.len := by
  simp [Bbu.swapPos, Bbu.swapDestinations, Bbu.St.len]

-- `Bbu.go` keeps the number of slots.
theorem go_len (st : Bbu.St) (p : PermuteKraken.Perm) {st' : Bbu.St} (h : Bbu.go st p = .ok st') :
    st'.len = st.len := by
  sorry -- wf:todo

-- `Bbu.go` is `permute.go`.
theorem go_corr {e : Bbu.Env} {source : Stack} (st : Bbu.St) (state : OState e source)
    (p : PermuteKraken.Perm) (perm : Permute.Permutation state.stack) (hne : 0 < state.stack.length)
    (h : Rel e st state) (hp : p.toList = destList perm) :
    ResCorr (Rel e) (Bbu.go st p) (Permute.permute.go state perm hne) := by
  sorry -- wf:todo

end BbuBridge
