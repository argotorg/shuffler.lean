import Shuffler.Optimality.BirthPlacement.Schedule

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation

theorem ForwardBefore.placeTop (permutation : Equiv.Perm (Fin size)) (top : Fin size)
    (hforward : ForwardBefore permutation top.val) (_hback : permutation top < top) :
    ForwardBefore (permutation * Equiv.swap top (permutation top)) top.val := by
  intro index hi
  have hit : index ≠ top := by intro he; subst index; omega
  by_cases hid : index = permutation top
  · subst index
    simp
  · simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hit hid] using
      hforward index hi

theorem BirthDeadlines.placeTop (permutation : Equiv.Perm (Fin size)) (top : Fin size)
    (hforward : ForwardBefore permutation top.val) (hback : permutation top < top)
    (hdeadline : BirthDeadlines reach permutation) :
    BirthDeadlines reach (permutation * Equiv.swap top (permutation top)) := by
  intro index
  by_cases hit : index = top
  · subst index
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have hf := hforward (permutation top) hback
    have hd := hdeadline top
    exact hd.trans (Nat.add_le_add_right hf reach)
  · by_cases hid : index = permutation top
    · subst index
      simp
    · simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hit hid] using
        hdeadline index

theorem settleTop_spec (permutation : Equiv.Perm (Fin size)) (top : Fin size)
    (hforward : ForwardBefore permutation top.val) (hdeadline : BirthDeadlines reach permutation) :
    ForwardBefore (settleTop permutation top).permutation (top.val + 1) ∧
    BirthDeadlines reach (settleTop permutation top).permutation ∧
    (∀ index : Fin size, top < index →
      (settleTop permutation top).permutation index = permutation index) ∧
    arbitrarySwapCount (settleTop permutation top).permutation +
      (settleTop permutation top).swaps.length = arbitrarySwapCount permutation ∧
    permutation * ((settleTop permutation top).swaps.map
      (fun pair => Equiv.swap pair.1 pair.2)).prod = (settleTop permutation top).permutation ∧
    (∀ pair ∈ (settleTop permutation top).swaps,
      pair.1 = top ∧ pair.2 < top ∧ top.val ≤ pair.2.val + reach) := by
  induction hn : arbitrarySwapCount permutation using Nat.strong_induction_on
      generalizing permutation with
  | h count ih =>
    rw [settleTop]
    split_ifs with hback
    · let next := permutation * Equiv.swap top (permutation top)
      have hdrop : arbitrarySwapCount next + 1 = arbitrarySwapCount permutation :=
        arbitrarySwapCount_place_top permutation top (ne_of_lt hback)
      obtain ⟨hf, hd, ha, hc, hp, hr⟩ := ih (arbitrarySwapCount next) (by omega) next
        (ForwardBefore.placeTop permutation top hforward hback)
        (BirthDeadlines.placeTop permutation top hforward hback hdeadline) rfl
      refine ⟨hf, hd, ?_, ?_, ?_, ?_⟩
      · intro index hi
        have hit : index ≠ top := ne_of_gt hi
        have hid : index ≠ permutation top := ne_of_gt (hback.trans hi)
        simpa only [next, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hit hid] using
          ha index hi
      · simp only [List.length_cons]
        dsimp only [next] at hc hdrop
        omega
      · simpa only [next, List.map_cons, List.prod_cons, mul_assoc] using hp
      · intro pair hm
        rcases List.mem_cons.mp hm with he | hm
        · subst pair
          exact ⟨rfl, hback, hdeadline top⟩
        · exact hr pair hm
    · refine ⟨?_, hdeadline, ?_, ?_, ?_, ?_⟩
      · intro index hi
        by_cases he : index = top
        · subst index
          exact le_of_not_gt hback
        · exact hforward index (by have := Fin.val_ne_of_ne he; omega)
      · intro index _
        rfl
      · simpa using hn
      · simp
      · simp

theorem ForwardBefore.fixed (permutation : Equiv.Perm (Fin size))
    (hforward : ForwardBefore permutation height) (hdeadline : BirthDeadlines reach permutation)
    (index : Fin size) (hindex : index.val + reach < height) : permutation index = index := by
  induction hn : index.val using Nat.strong_induction_on generalizing index with
  | h value ih =>
    let earlier := permutation.symm index
    have he : permutation earlier = index := permutation.apply_symm_apply index
    have hd := hdeadline earlier
    rw [he] at hd
    have hf : earlier ≤ index := by
      have hf := hforward earlier (by omega)
      simpa only [he] using hf
    by_cases heq : earlier = index
    · simpa only [heq] using he
    · have hlt : earlier.val < index.val := by
        have hne := Fin.val_ne_of_ne heq
        omega
      have hfixed := ih earlier.val (by omega) earlier (by omega) rfl
      exact False.elim (heq (hfixed.symm.trans he))

theorem ForwardBefore.eq_one (permutation : Equiv.Perm (Fin size))
    (hforward : ForwardBefore permutation size) : permutation = 1 := by
  apply Equiv.ext
  intro index
  exact ForwardBefore.fixed permutation hforward
    (reach := 0) (fun other => by simpa using hforward other other.isLt) index
    (by simpa only [Nat.add_zero] using index.isLt)

theorem scheduleFrom_spec (height : Nat) (permutation : Equiv.Perm (Fin size))
    (hforward : ForwardBefore permutation height) (hdeadline : BirthDeadlines reach permutation) :
    (scheduleFrom height permutation).permutation = 1 ∧
    (scheduleFrom height permutation).swaps.length = arbitrarySwapCount permutation ∧
    permutation * ((scheduleFrom height permutation).swaps.map
      (fun pair => Equiv.swap pair.1 pair.2)).prod = 1 ∧
    (∀ pair ∈ (scheduleFrom height permutation).swaps,
      height ≤ pair.1.val ∧ pair.2 < pair.1 ∧ pair.1.val ≤ pair.2.val + reach) := by
  induction hn : size - height using Nat.strong_induction_on generalizing height permutation with
  | h remaining ih =>
    rw [scheduleFrom]
    split_ifs with hheight
    · let top : Fin size := ⟨height, hheight⟩
      let step := settleTop permutation top
      obtain ⟨hf, hd, _, hc, hp, hr⟩ := settleTop_spec permutation top hforward hdeadline
      obtain ⟨he, hl, hprod, hreach⟩ := ih (size - (height + 1)) (by omega) (height + 1)
        step.permutation hf hd rfl
      refine ⟨he, ?_, ?_, ?_⟩
      · change (step.swaps ++ (scheduleFrom (height + 1) step.permutation).swaps).length = _
        rw [List.length_append, hl]
        simpa only [step, Nat.add_comm] using hc
      · change permutation * (List.map (fun pair => Equiv.swap pair.1 pair.2)
          (step.swaps ++ (scheduleFrom (height + 1) step.permutation).swaps)).prod = 1
        rw [List.map_append, List.prod_append, ← mul_assoc, hp]
        exact hprod
      · intro pair hm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨ht, hb, hd⟩ := hr pair hm
          exact ⟨by simp only [ht, top, le_refl],
            by simpa only [ht] using hb, by simpa only [ht] using hd⟩
        · obtain ⟨hh, hb, hd⟩ := hreach pair hm
          exact ⟨by omega, hb, hd⟩
    · have he : permutation = 1 := ForwardBefore.eq_one permutation
        (fun index hi => hforward index (by omega))
      subst permutation
      simp

theorem schedule_permutation (permutation : Equiv.Perm (Fin size))
    (hdeadline : BirthDeadlines reach permutation) : (schedule permutation).permutation = 1 :=
  (scheduleFrom_spec 0 permutation (fun _ hi => by omega) hdeadline).1

theorem schedule_swaps_length (permutation : Equiv.Perm (Fin size))
    (hdeadline : BirthDeadlines reach permutation) :
    (schedule permutation).swaps.length = arbitrarySwapCount permutation :=
  (scheduleFrom_spec 0 permutation (fun _ hi => by omega) hdeadline).2.1

theorem schedule_swaps_le_moved (permutation : Equiv.Perm (Fin size))
    (hdeadline : BirthDeadlines reach permutation) :
    (schedule permutation).swaps.length ≤ permutation.support.card := by
  rw [schedule_swaps_length permutation hdeadline]
  exact Nat.sub_le _ _

end Shuffler.Optimality.BirthPlacement
