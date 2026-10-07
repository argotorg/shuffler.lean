import Shuffler.Optimality.BirthPlacement.Realize.Lemmas

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation

structure SettledTrace (spills : SpillSet) (target : Stack)
    (before : Equiv.Perm (Fin target.length)) (top : Fin target.length) where
  permutation : Equiv.Perm (Fin target.length)
  trace : Trace spills (prefixValues target before (top.val + 1))
    (prefixValues target permutation (top.val + 1))
  noPop : trace.noPop
  additions : trace.additions = 0
  count : trace.swapCount + arbitrarySwapCount permutation = arbitrarySwapCount before
  forward : ForwardBefore permutation (top.val + 1)
  deadlines : BirthDeadlines 16 permutation
  above : ∀ index : Fin target.length, top < index → permutation index = before index

private def placeTopTrace (spills : SpillSet) (target : Stack)
    (permutation : Equiv.Perm (Fin target.length)) (top : Fin target.length)
    (hback : permutation top < top) (hdeadline : BirthDeadlines 16 permutation) :
    { trace : Trace spills (prefixValues target permutation (top.val + 1))
        (prefixValues target (permutation * Equiv.swap top (permutation top)) (top.val + 1)) //
      trace.noPop ∧ trace.additions = 0 ∧ trace.swapCount = 1 } := by
  let current := prefixValues target permutation (top.val + 1)
  let depth := top.val - (permutation top).val
  have hlen : current.length = top.val + 1 := by
    simp only [current, prefixValues_length]
    omega
  have hd := hdeadline top
  have hdepth : depth ≤ MAX_SWAP_DEPTH := by unfold depth MAX_SWAP_DEPTH; omega
  let first := Trace.Swap (spills := spills) depth (by dsimp [depth]; omega)
    (by dsimp [depth]; omega) hdepth (.Lit current)
  have he : current.swap (current.length - 1) (current.length - 1 - depth) =
      prefixValues target (permutation * Equiv.swap top (permutation top)) (top.val + 1) := by
    rw [hlen]
    have hi : top.val + 1 - 1 - depth = (permutation top).val := by dsimp [depth]; omega
    rw [hi, Nat.add_sub_cancel]
    exact (prefixValues_swap target permutation (top.val + 1) top (permutation top)
      (by omega) (by omega)).symm
  exact ⟨he ▸ first, (Trace.noPop_cast _ _).mpr trivial,
    by rw [Trace.additions_cast]; rfl, by rw [swapCount_cast]; rfl⟩

private def SettledTrace.prepend (spills : SpillSet) (target : Stack)
    (permutation : Equiv.Perm (Fin target.length)) (top : Fin target.length)
    (hback : permutation top < top) (hdeadline : BirthDeadlines 16 permutation)
    (rest : SettledTrace spills target (permutation * Equiv.swap top (permutation top)) top) :
    SettledTrace spills target permutation top := by
  let first := placeTopTrace spills target permutation top hback hdeadline
  refine ⟨rest.permutation, first.val.concat rest.trace,
    first.val.noPop_concat rest.trace first.property.1 rest.noPop, ?_, ?_,
    rest.forward, rest.deadlines, ?_⟩
  · rw [Trace.additions_concat, first.property.2.1, rest.additions, zero_add]
  · rw [swapCount_concat, first.property.2.2]
    have hr := rest.count
    have hdrop := arbitrarySwapCount_place_top permutation top (ne_of_lt hback)
    omega
  · intro index hi
    have hit : index ≠ top := ne_of_gt hi
    have hid : index ≠ permutation top := ne_of_gt (hback.trans hi)
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hit hid] using
      rest.above index hi

private def SettledTrace.done (spills : SpillSet) (target : Stack)
    (permutation : Equiv.Perm (Fin target.length)) (top : Fin target.length)
    (hforward : ForwardBefore permutation top.val) (hdeadline : BirthDeadlines 16 permutation)
    (hback : ¬permutation top < top) : SettledTrace spills target permutation top := by
  refine ⟨permutation, .Lit _, trivial, rfl, by simp [Trace.swapCount], ?_, hdeadline,
    fun _ _ => rfl⟩
  intro index hi
  by_cases he : index = top
  · subst index
    exact le_of_not_gt hback
  · exact hforward index (by have := Fin.val_ne_of_ne he; omega)

-- Compile each backwards top placement to a production Trace.Swap.
def settleTrace (spills : SpillSet) (target : Stack)
    (permutation : Equiv.Perm (Fin target.length)) (top : Fin target.length)
    (hforward : ForwardBefore permutation top.val) (hdeadline : BirthDeadlines 16 permutation) :
    SettledTrace spills target permutation top :=
  if hback : permutation top < top then
    SettledTrace.prepend spills target permutation top hback hdeadline
      (settleTrace spills target (permutation * Equiv.swap top (permutation top)) top
        (ForwardBefore.placeTop permutation top hforward hback)
        (BirthDeadlines.placeTop permutation top hforward hback hdeadline))
  else SettledTrace.done spills target permutation top hforward hdeadline hback
termination_by arbitrarySwapCount permutation
decreasing_by
  exact Nat.lt_of_succ_le
    (arbitrarySwapCount_place_top permutation top (ne_of_lt hback)).le

end Shuffler.Optimality.BirthPlacement
