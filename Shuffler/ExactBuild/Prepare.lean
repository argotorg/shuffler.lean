import Shuffler.ExactBuild.Steps

namespace Shuffler.ExactBuild

open Shuffler.Placement

-- The working suffix and the missing values give the rest of the target. The
-- suffix is in SWAP reach, is in DUP reach while values are missing, and holds
-- all seeds.
structure Working (spills : SpillSet) (working target : Stack) (missing : Multiset Value) :
    Prop where
  small : working.length ≤ MAX_SWAP_DEPTH + 1
  space : missing ≠ 0 → working.length ≤ MAX_DUP_DEPTH + 1
  balance : (target : Multiset Value) = (working : Multiset Value) + missing
  seeds : seeds spills missing ≤ (working : Multiset Value)

structure PreparedProblem (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) where
  fixed : Stack
  working : Stack
  tail : Stack
  built : BuiltTrace spills source (fixed ++ working) 0
  target_eq : target = fixed ++ tail
  valid : Working spills working tail missing

private theorem reserve_target (h : Reserve spills source target missing) :
    target = source.take (frozen source) ++ target.drop (frozen source) := by
  calc
    target = target.take (frozen source) ++ target.drop (frozen source) :=
      (List.take_append_drop _ _).symm
    _ = source.take (frozen source) ++ target.drop (frozen source) := by rw [h.2.1]

private theorem frozen_small (source : Stack) :
    (source.drop (frozen source)).length ≤ MAX_SWAP_DEPTH + 1 := by
  simp only [List.length_drop, frozen]
  omega

private theorem reserve_balance (h : Reserve spills source target missing) :
    ((target.drop (frozen source) : Stack) : Multiset Value) =
      ((source.drop (frozen source) : Stack) : Multiset Value) + missing := by
  have hb := h.1
  have hs : (source : Multiset Value) = ((source.take (frozen source) : Stack) : Multiset Value) +
      ((source.drop (frozen source) : Stack) : Multiset Value) := by
    rw [Multiset.coe_add, List.take_append_drop]
  rw [reserve_target h, hs, ← Multiset.coe_add, add_assoc] at hb
  exact add_left_cancel hb

private theorem reserve_seeds (h : Reserve spills source target missing) :
    seeds spills missing ≤ ((source.drop (frozen source) : Stack) : Multiset Value) :=
  (Multiset.le_add_left _ _).trans h.2.2

private theorem reserve_working (h : Reserve spills source target missing)
    (hspace : missing ≠ 0 → (source.drop (frozen source)).length ≤ MAX_DUP_DEPTH + 1) :
    Working spills (source.drop (frozen source)) (target.drop (frozen source)) missing :=
  ⟨frozen_small source, hspace, reserve_balance h, reserve_seeds h⟩

private theorem boundary_large {source : Stack} (hspace : ¬(source.drop (frozen source)).length ≤ MAX_DUP_DEPTH + 1) :
    MAX_SWAP_DEPTH + 1 ≤ source.length := by
  have hw : (source.drop (frozen source)).length ≤ source.length := by
    simp only [List.length_drop]
    omega
  unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
  omega

private theorem boundary_lt (h : Reserve spills source target missing)
    (hspace : ¬(source.drop (frozen source)).length ≤ MAX_DUP_DEPTH + 1) :
    frozen source < target.length := by
  have hlarge := boundary_large hspace
  have hcard := congrArg Multiset.card h.1
  simp only [Multiset.card_add, Multiset.coe_card] at hcard
  dsimp [frozen]
  unfold MAX_SWAP_DEPTH at hlarge ⊢
  omega

private theorem boundary_reserve (h : Reserve spills source target missing) (hzero : missing ≠ 0)
    (hspace : ¬(source.drop (frozen source)).length ≤ MAX_DUP_DEPTH + 1) :
    {target[frozen source]'(boundary_lt h hspace)} + seeds spills missing ≤
      ((source.drop (frozen source) : Stack) : Multiset Value) := by
  have hboundary : boundary source target missing =
      {target[frozen source]'(boundary_lt h hspace)} := by
    simp [boundary, hzero, boundary_large hspace,
      List.getElem?_eq_getElem (boundary_lt h hspace)]
  simpa only [hboundary, window] using h.2.2

private theorem boundary_mem (h : Reserve spills source target missing) (hzero : missing ≠ 0)
    (hspace : ¬(source.drop (frozen source)).length ≤ MAX_DUP_DEPTH + 1) :
    target[frozen source]'(boundary_lt h hspace) ∈ source.drop (frozen source) :=
  Multiset.mem_of_le (boundary_reserve h hzero hspace) (by simp)

private theorem boundary_target (h : Reserve spills source target missing)
    (hindex : frozen source < target.length) :
    target = (source.take (frozen source) ++ [target[frozen source]]) ++
      target.drop (frozen source + 1) := by
  conv_lhs => rw [reserve_target h, List.drop_eq_getElem_cons hindex]
  simp only [List.append_assoc, List.singleton_append]

private theorem boundary_working (h : Reserve spills source target missing) (hzero : missing ≠ 0)
    (hspace : ¬(source.drop (frozen source)).length ≤ MAX_DUP_DEPTH + 1)
    (step : PlacementStep spills (source.take (frozen source)) (source.drop (frozen source))
      (target[frozen source]'(boundary_lt h hspace)) 0) :
    Working spills step.remaining (target.drop (frozen source + 1)) missing := by
  have hindex := boundary_lt h hspace
  have hstep : {target[frozen source]} + (step.remaining : Multiset Value) =
      ((source.drop (frozen source) : Stack) : Multiset Value) := by
    simpa only [add_zero] using step.balance
  have hcard := congrArg Multiset.card hstep
  simp only [Multiset.card_add, Multiset.card_singleton, Multiset.coe_card] at hcard
  have hsmall := frozen_small source
  have hbalance := reserve_balance h
  have hreserve := boundary_reserve h hzero hspace
  rw [List.drop_eq_getElem_cons hindex] at hbalance
  change {target[frozen source]} + ((target.drop (frozen source + 1) : Stack) : Multiset Value) =
    _ at hbalance
  rw [← hstep, add_assoc] at hbalance
  rw [← hstep] at hreserve
  refine ⟨?_, fun _ => ?_, add_left_cancel hbalance, (add_le_add_iff_left _).mp hreserve⟩
  · unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
    omega
  · unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
    omega

-- Keep the initially frozen prefix. Before any required growth from a full
-- seventeen-slot window, place its reserved output and retain all seeds.
def prepare (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (h : Reserve spills source target missing) : PreparedProblem spills source target missing :=
  let count := frozen source
  let fixed := source.take count
  let working := source.drop count
  have hsource : fixed ++ working = source := List.take_append_drop _ _
  let initial := (BuiltTrace.lit spills source).castTarget hsource.symm
  if hzero : missing = 0 then
    ⟨fixed, working, target.drop count, initial, reserve_target h,
      reserve_working h fun hne => absurd hzero hne⟩
  else if hspace : working.length ≤ MAX_DUP_DEPTH + 1 then
    ⟨fixed, working, target.drop count, initial, reserve_target h,
      reserve_working h fun _ => hspace⟩
  else
    let value := target[count]'(boundary_lt h hspace)
    let step := placeExisting spills fixed working value (frozen_small source)
      (boundary_mem h hzero hspace)
    ⟨fixed ++ [value], step.remaining, target.drop (count + 1), step.built.cast hsource rfl rfl,
      boundary_target h (boundary_lt h hspace), boundary_working h hzero hspace step⟩

end Shuffler.ExactBuild
