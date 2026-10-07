import Shuffler.Optimality.BirthPlacement.Realize.Lemmas

namespace Shuffler.Optimality.BirthPlacement

-- The permutation maps each current position back to its birth position.
structure TokenFrame (births current : Stack) (swaps size : Nat) where
  permutation : Equiv.Perm (Fin size)
  length : births.length = current.length
  bound : current.length ≤ size
  outside : ∀ index : Fin size, current.length ≤ index.val → permutation index = index
  values : ∀ index : Fin size, current[index.val]? = births[(permutation index).val]?
  backwards : ∀ index : Fin size, (permutation index).val ≤ index.val + 16
  moved : permutation.support.card ≤ 2 * swaps

theorem permutation_inside (permutation : Equiv.Perm (Fin size)) (height : Nat)
    (houtside : ∀ index : Fin size, height ≤ index.val → permutation index = index)
    (index : Fin size) (hindex : index.val < height) : (permutation index).val < height := by
  by_contra h
  have he := houtside (permutation index) (by omega)
  have hi : permutation index = index := permutation.injective he
  rw [hi] at h
  omega

theorem getElem?_swap_fin (values : Stack) (left right index : Fin size)
    (hleft : left.val < values.length) (hright : right.val < values.length) :
    (values.swap left.val right.val)[index.val]? = values[(Equiv.swap left right index).val]? := by
  by_cases hl : index = left
  · subst index
    simp [hleft, hright]
  · by_cases hr : index = right
    · subst index
      simp [hleft, hright]
    · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
      by_cases hi : index.val < values.length
      · simp [hi, Fin.val_ne_of_ne hl, Fin.val_ne_of_ne hr]
      · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi),
          List.getElem?_eq_none (Nat.le_of_not_gt hi)]

theorem getElem?_append_permutation (births current : Stack)
    (permutation : Equiv.Perm (Fin size)) (hlen : births.length = current.length)
    (houtside : ∀ index : Fin size, current.length ≤ index.val → permutation index = index)
    (hvalues : ∀ index : Fin size, current[index.val]? = births[(permutation index).val]?)
    (value : Value) (index : Fin size) :
    (current ++ [value])[index.val]? = (births ++ [value])[(permutation index).val]? := by
  by_cases hi : index.val < current.length
  · rw [List.getElem?_append_left hi,
      List.getElem?_append_left (by rw [hlen]; exact permutation_inside permutation _ houtside index hi)]
    exact hvalues index
  · rw [houtside index (Nat.le_of_not_gt hi),
      List.getElem?_append_right (Nat.le_of_not_gt hi),
      List.getElem?_append_right (by omega), hlen]

theorem support_card_mul_swap_le (permutation : Equiv.Perm (Fin size)) (left right : Fin size) :
    (permutation * Equiv.swap left right).support.card ≤ permutation.support.card + 2 := by
  have hsub := Finset.card_le_card (Equiv.Perm.support_mul_le permutation (Equiv.swap left right))
  change (permutation * Equiv.swap left right).support.card ≤
    (permutation.support ∪ (Equiv.swap left right).support).card at hsub
  have hunion := Finset.card_union_le permutation.support (Equiv.swap left right).support
  have hswap : (Equiv.swap left right).support.card ≤ 2 := by
    by_cases he : left = right
    · simp [he]
    · exact (Equiv.Perm.card_support_swap he).le
  omega

def TokenFrame.initial (current : Stack) (size : Nat) (hbound : current.length ≤ size) :
    TokenFrame current current 0 size where
  permutation := 1
  length := rfl
  bound := hbound
  outside := fun _ _ => rfl
  values := fun _ => rfl
  backwards := fun index => by change index.val ≤ index.val + 16; omega
  moved := by simp

def TokenFrame.grow (frame : TokenFrame births current swaps size) (value : Value)
    (hbound : current.length + 1 ≤ size) :
    TokenFrame (births ++ [value]) (current ++ [value]) swaps size where
  permutation := frame.permutation
  length := by simp [frame.length]
  bound := by simpa using hbound
  outside := fun index hi => frame.outside index (by simp only [List.length_append, List.length_singleton] at hi; omega)
  values := getElem?_append_permutation births current frame.permutation frame.length frame.outside frame.values value
  backwards := frame.backwards
  moved := frame.moved

def TokenFrame.swap (frame : TokenFrame births current swaps size)
    (depth : Nat) (hdepth : depth < current.length) (hlow : 1 ≤ depth) (hhigh : depth ≤ 16) :
    TokenFrame births (current.swap (current.length - 1) (current.length - 1 - depth)) (swaps + 1) size := by
  let top : Fin size := ⟨current.length - 1, by have := frame.bound; omega⟩
  let lower : Fin size := ⟨current.length - 1 - depth, by have := frame.bound; omega⟩
  have ht : top.val < current.length := by dsimp [top]; omega
  have hl : lower.val < current.length := by dsimp [lower]; omega
  refine ⟨frame.permutation * Equiv.swap top lower, by simpa using frame.length,
    by simpa using frame.bound, ?_, ?_, ?_, ?_⟩
  · intro index hi
    simp only [List.length_swap] at hi
    have hit : index ≠ top := by intro he; subst index; omega
    have hil : index ≠ lower := by intro he; subst index; omega
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hit hil] using frame.outside index hi
  · intro index
    change (current.swap top.val lower.val)[index.val]? =
      births[(frame.permutation (Equiv.swap top lower index)).val]?
    rw [getElem?_swap_fin current top lower index ht hl, frame.values]
  · intro index
    by_cases hit : index = top
    · subst index
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have hp := permutation_inside frame.permutation current.length frame.outside lower hl
      dsimp [top]
      omega
    · by_cases hil : index = lower
      · subst index
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have hp := permutation_inside frame.permutation current.length frame.outside top ht
        dsimp [lower]
        omega
      · simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hit hil] using frame.backwards index
  · have hs := support_card_mul_swap_le frame.permutation top lower
    have hm := frame.moved
    omega

end Shuffler.Optimality.BirthPlacement
