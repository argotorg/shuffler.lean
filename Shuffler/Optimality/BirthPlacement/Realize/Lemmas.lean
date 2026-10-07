import Shuffler.Optimality.BirthPlacement.Plan
import Shuffler.Optimality.BirthPlacement.Schedule.Theorems

namespace Shuffler.Optimality.BirthPlacement

@[simp] theorem birthWord_length (target : Stack)
    (permutation : Equiv.Perm (Fin target.length)) :
    (birthWord target permutation).length = target.length := List.length_ofFn

@[simp] theorem prefixValues_length (target : Stack)
    (permutation : Equiv.Perm (Fin target.length)) (height : Nat) :
    (prefixValues target permutation height).length = min height target.length := by
  simp [prefixValues]

theorem prefixValues_swap (target : Stack) (permutation : Equiv.Perm (Fin target.length))
    (height : Nat) (left right : Fin target.length) (hleft : left.val < height)
    (hright : right.val < height) :
    prefixValues target (permutation * Equiv.swap left right) height =
      (prefixValues target permutation height).swap left.val right.val := by
  apply List.ext_getElem
  · simp
  · intro index hi hj
    have hn : index < target.length := by
      have hh : index < min height target.length := by simpa only [prefixValues_length] using hi
      omega
    let slot : Fin target.length := ⟨index, hn⟩
    by_cases hl : slot = left
    · subst left
      simp [prefixValues, birthWord, List.getElem_take, slot, hright, right.isLt,
        Fin.getElem_fin]
    · by_cases hr : slot = right
      · subst right
        simp [prefixValues, birthWord, List.getElem_take, slot, hleft, left.isLt,
          Fin.getElem_fin]
      · have hln : index ≠ left.val := by intro he; exact hl (Fin.ext he)
        have hrn : index ≠ right.val := by intro he; exact hr (Fin.ext he)
        simp only [prefixValues, birthWord, List.getElem_take, List.getElem_ofFn, Fin.getElem_fin,
          Equiv.Perm.mul_apply, List.getElem_swap_of_ne hln hrn]
        exact congrArg (fun position : Fin target.length => target[(permutation position).val])
          (Equiv.swap_apply_of_ne_of_ne hl hr)

theorem prefixValues_succ (target : Stack) (permutation : Equiv.Perm (Fin target.length))
    (height : Nat) (hheight : height < target.length) :
    prefixValues target permutation (height + 1) =
      prefixValues target permutation height ++ [target[permutation ⟨height, hheight⟩]] := by
  simpa only [prefixValues, birthWord, List.getElem_ofFn] using
    (List.take_succ_eq_append_getElem (l := birthWord target permutation) (by simpa using hheight))

theorem prefixValues_frozen (target : Stack) (permutation : Equiv.Perm (Fin target.length))
    (height : Nat) (hheight : height ≤ target.length)
    (hforward : ForwardBefore permutation height) (hdeadline : BirthDeadlines 16 permutation) :
    (prefixValues target permutation height).take (height - 16) = target.take (height - 16) := by
  apply List.ext_getElem
  · simp only [List.length_take, prefixValues_length]
    omega
  · intro index hi hj
    have hi' : index < height - 16 := by
      simp only [List.length_take, prefixValues_length, lt_min_iff] at hi
      exact hi.1
    have hn : index < target.length := by omega
    have he := ForwardBefore.fixed permutation (height := height) (reach := 16)
      hforward hdeadline ⟨index, hn⟩ (by change index + 16 < height; omega)
    simp only [prefixValues, birthWord, List.getElem_take, List.getElem_ofFn, he,
      Fin.getElem_fin]

@[simp] theorem prefixValues_one (target : Stack) :
    prefixValues target 1 target.length = target := by
  apply List.ext_getElem <;> simp [prefixValues, birthWord]

theorem swapCount_cast (he : target = other) (trace : Trace spills source target) :
    (he ▸ trace : Trace spills source other).swapCount = trace.swapCount := by
  cases he
  rfl

theorem swapCount_concat (first : Trace spills source middle) (second : Trace spills middle target) :
    (first.concat second).swapCount = first.swapCount + second.swapCount := by
  induction second with
  | Lit => simp [Trace.concat, Trace.swapCount]
  | Swap _ _ _ _ _ ih => simp only [Trace.concat, Trace.swapCount, ih, Nat.add_assoc]
  | Dup _ _ _ _ _ ih | Pop _ _ ih | Push _ _ _ ih | Load _ _ _ ih => exact ih

theorem built_cast_swapCount (built : Shuffler.Placement.BuiltTrace spills source target missing)
    (hs : source = otherSource) (ht : target = otherTarget) (hm : missing = otherMissing) :
    (built.cast hs ht hm).trace.swapCount = built.trace.swapCount := by
  cases hs
  cases ht
  cases hm
  rfl

end Shuffler.Optimality.BirthPlacement
