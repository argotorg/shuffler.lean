import Shuffler.Optimality.PrefixIntroduction.LateDup
import Shuffler.Optimality.Replay
import Shuffler.Optimality.Collective.TraceCuts
import Mathlib.Data.Finset.Card

namespace Shuffler.Optimality.Collective

open Shuffler.Placement Shuffler.Optimality.PrefixIntroduction

-- The fresh fresh contains no initial kind. The old suffix retains the
-- whole initial multiset, including repeated copies.
def FreshPrefix (source fresh old : Stack) : Prop :=
  old.Perm source ∧ ∀ value ∈ fresh, value ∉ source

theorem FreshPrefix.oldCount_prefix (h : FreshPrefix source fresh old) :
    oldCount source fresh = 0 := by
  apply List.countP_eq_zero.mpr
  intro value hv
  simpa only [Bool.not_eq_true] using decide_eq_false (h.2 value hv)

theorem FreshPrefix.oldCount_target (h : FreshPrefix source fresh old) :
    oldCount source (fresh ++ old) = source.length := by
  unfold oldCount
  rw [List.countP_append, h.1.countP_eq]
  change oldCount source fresh + oldCount source source = source.length
  rw [h.oldCount_prefix, oldCount_source, Nat.zero_add]

theorem FreshPrefix.oldCount_take (h : FreshPrefix source fresh old)
    (hcut : cut ≤ fresh.length) :
    oldCount source ((fresh ++ old).take cut) = 0 := by
  rw [List.take_append_of_le_length hcut]
  have hh : oldCount source (fresh.take cut) ≤ oldCount source fresh :=
    (List.take_sublist cut fresh).countP_le
  rw [h.oldCount_prefix] at hh
  omega

theorem FreshPrefix.oldCount_drop (h : FreshPrefix source fresh old)
    (hcut : cut ≤ fresh.length) :
    oldCount source ((fresh ++ old).drop cut) = source.length := by
  have hh : oldCount source ((fresh ++ old).take cut) +
      oldCount source ((fresh ++ old).drop cut) = oldCount source (fresh ++ old) := by
    unfold oldCount
    rw [← List.countP_append, List.take_append_drop]
  rw [h.oldCount_take hcut, h.oldCount_target] at hh
  omega

-- A real output is fixed just before a birth. Its boundary copy is outside
-- the readable sixteen slots. All old copies remain in those slots.
theorem real_cut_oldCount (hfamily : FreshPrefix source fresh old)
    (before : Trace spills source current) (hbefore : before.noPop)
    (tail : Trace spills (current ++ [added]) (fresh ++ old)) (htail : tail.noPop)
    (hheight : current.length = cut + 16) (hcut : cut ≤ fresh.length) :
    (current.drop cut).length = 16 ∧
      oldCount source (current.drop cut) = source.length := by
  have hlower := oldCount_mono source before hbefore
  rw [oldCount_source] at hlower
  have hupper := oldCount_mono source tail htail
  rw [hfamily.oldCount_target] at hupper
  have hcurrent : oldCount source current = source.length := by
    unfold oldCount at hupper hlower ⊢
    rw [List.countP_append] at hupper
    omega
  have hfrozen : frozen (current ++ [added]) = cut := by
    simp only [frozen, MAX_SWAP_DEPTH, List.length_append, List.length_singleton, hheight]
    omega
  have hfixed := tail.noPop_frozen htail
  rw [hfrozen, List.take_append_of_le_length (l₁ := current) (by omega)] at hfixed
  have hprefix : oldCount source (current.take cut) = 0 := by
    rw [← hfixed]
    exact hfamily.oldCount_take hcut
  have hsplit : oldCount source (current.take cut) + oldCount source (current.drop cut) =
      oldCount source current := by
    unfold oldCount
    rw [← List.countP_append, List.take_append_drop]
  constructor
  · simp only [List.length_drop, hheight]
    omega
  · omega

-- After the last real freeze, the remaining outputs are read from the
-- finished target. Removing one of them leaves at most sixteen values.
theorem virtual_cut_oldCount (hfamily : FreshPrefix source fresh old)
    (hheight : (fresh ++ old).length ≤ cut + 16) (hcut : cut ≤ fresh.length) :
    ((fresh ++ old).drop cut).length ≤ 16 ∧
      oldCount source ((fresh ++ old).drop cut) = source.length := by
  exact ⟨by simp only [List.length_drop]; omega, hfamily.oldCount_drop hcut⟩

def freshKinds (source residual : Stack) : Finset Value :=
  (residual.filter (fun value => decide (value ∉ source))).toFinset

theorem freshKinds_card_le (hlen : residual.length ≤ 16)
    (hold : oldCount source residual = source.length) :
    (freshKinds source residual).card ≤ 16 - source.length := by
  have hc := List.toFinset_card_le
    (l := residual.filter (fun value => decide (value ∉ source)))
  have hs (values : Stack) : oldCount source values +
      (values.filter (fun value => decide (value ∉ source))).length = values.length := by
    induction values with
    | nil => rfl
    | cons value rest ih =>
        by_cases hv : value ∈ source <;> simp [oldCount, hv] at ih ⊢ <;> omega
  have hs := hs residual
  unfold freshKinds
  omega

-- Every nonempty fresh-output cut has one of the two residual witnesses.
-- The real witness comes from the actual birth at height cut+17.
theorem exists_output_residual (trace : Trace spills source (fresh ++ old))
    (hpop : trace.noPop) (hfamily : FreshPrefix source fresh old)
    (hsource : source.length ≤ 16) (hpositive : 0 < cut) (hcut : cut ≤ fresh.length) :
    ∃ residual : Stack, residual.length ≤ 16 ∧
      oldCount source residual = source.length ∧
      (freshKinds source residual).card ≤ 16 - source.length := by
  by_cases hh : (fresh ++ old).length ≤ cut + 16
  · have hr := virtual_cut_oldCount hfamily hh hcut
    exact ⟨(fresh ++ old).drop cut, hr.1, hr.2, freshKinds_card_le hr.1 hr.2⟩
  · obtain ⟨current, value, before, birth, tail, hc, hb, _, ht, _, _, _⟩ :=
      split_at_birth trace hpop (cut + 17) (by omega) (by omega)
    have hr := real_cut_oldCount hfamily before hb tail ht (by omega) hcut
    exact ⟨current.drop cut, hr.1.le, hr.2, freshKinds_card_le hr.1.le hr.2⟩

end Shuffler.Optimality.Collective
