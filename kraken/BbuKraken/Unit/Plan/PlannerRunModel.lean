module

public import BbuKraken.FlatPlan
import all BbuKraken.FlatPlan

@[expose] public section

/-! Loop equations used by the assembly proof of `Planner::run`.
Each equation follows the exit or the next iteration of one source loop. -/

namespace Bbu.Unit.PlannerRunU

section
variable {pl : Flat.Planner} {sp : BitVec 32 → BitVec 8}
    {data : Vector StackSlot MAX_N} {M : Flat.Mapping}
    {sources : Vector Word MAX_N} {d : Vector (BitVec 8) MAX_N}
    {i j m count : Word} {slot : StackSlot}

theorem contains_end (hi : ¬ i < m) :
    Flat.containsFrom data m slot i = false := by
  rw [Flat.containsFrom, dite_eq_right hi]

theorem contains_found (hi : i < m) (hs : Flat.get data i = slot) :
    Flat.containsFrom data m slot i = true := by
  rw [Flat.containsFrom, dite_eq_left hi, ite_eq_left hs]

theorem contains_next (hi : i < m) (hs : Flat.get data i ≠ slot) :
    Flat.containsFrom data m slot i = Flat.containsFrom data m slot (i + 1) := by
  rw [Flat.containsFrom, dite_eq_left hi, ite_eq_right hs]

theorem targets_end (hj : ¬ j < pl.n) : Flat.targetsFrom pl sp j = true := by
  rw [Flat.targetsFrom, dite_eq_right hj]

theorem targets_next (hj : j < pl.n)
    (hs : (isJunk (Flat.get pl.target j) || canBeFreelyGenerated (Flat.get pl.target j) ||
      Flat.containsFrom pl.source pl.m (Flat.get pl.target j) 0 ||
      Flat.spillIsSpilled sp (Flat.get pl.target j)) = true) :
    Flat.targetsFrom pl sp j = Flat.targetsFrom pl sp (j + 1) := by
  rw [Flat.targetsFrom, dite_eq_left hj]
  dsimp only
  rw [hs, Bool.true_and]

theorem targets_fail (hj : j < pl.n)
    (hs : (isJunk (Flat.get pl.target j) || canBeFreelyGenerated (Flat.get pl.target j) ||
      Flat.containsFrom pl.source pl.m (Flat.get pl.target j) 0 ||
      Flat.spillIsSpilled sp (Flat.get pl.target j)) = false) :
    Flat.targetsFrom pl sp j = false := by
  rw [Flat.targetsFrom, dite_eq_left hj]
  dsimp only
  rw [hs, Bool.false_and]

theorem dropped_end (hi : ¬ i < m) : Flat.droppedFrom m d i count = count := by
  rw [Flat.droppedFrom, dite_eq_right hi]

theorem dropped_zero (hi : i < m) (hd : Flat.get d i = 0#8) :
    Flat.droppedFrom m d i count = Flat.droppedFrom m d (i + 1) count := by
  rw [Flat.droppedFrom, dite_eq_left hi]
  simp only [show Flat.get d i = (0 : BitVec 8) from hd, ne_eq, not_true_eq_false, ↓reduceIte]

theorem dropped_nonzero (hi : i < m) (hd : Flat.get d i ≠ 0#8) :
    Flat.droppedFrom m d i count = Flat.droppedFrom m d (i + 1) (count + 1) := by
  rw [Flat.droppedFrom, dite_eq_left hi]
  change Flat.droppedFrom m d (i + 1) (if Flat.get d i ≠ (0 : BitVec 8) then count + 1 else count) = _
  rw [ite_eq_left (show Flat.get d i ≠ (0 : BitVec 8) from hd)]

theorem copy_end (hi : ¬ i < pl.m) : Flat.copyFrom pl i data = data := by
  rw [Flat.copyFrom, dite_eq_right hi]

theorem copy_next (hi : i < pl.m) :
    Flat.copyFrom pl i data =
      Flat.copyFrom pl (i + 1) (Flat.put data i (Flat.get pl.source i)) := by
  rw [Flat.copyFrom, dite_eq_left hi]

theorem sources_end (hj : ¬ j < m) : Flat.sourcesFrom m j M sources = sources := by
  rw [Flat.sourcesFrom, dite_eq_right hj]

theorem sources_next (hj : j < m) :
    Flat.sourcesFrom m j M sources =
      Flat.sourcesFrom m (j + 1) M (Flat.put sources j (Flat.get M.pos j)) := by
  rw [Flat.sourcesFrom, dite_eq_left hj]

end

-- Failed target validation resets `saw` before it returns.
theorem plannerRun_bad_target (pl : Flat.Planner) (take : Bool) (s : Flat.PSt)
    (us : Nat → Flat.RunU) (h : Flat.targetsFrom pl s.spills 0 = false) :
    Flat.plannerRun pl take s us = (.assertionFailed, { s with saw := false }) := by
  simp only [Flat.plannerRun, h, Bool.not_false, ↓reduceIte]

theorem plannerRun_targets_ok (pl : Flat.Planner) (take : Bool) (s : Flat.PSt)
    (us : Nat → Flat.RunU) (h : Flat.targetsFrom pl s.spills 0 = true) :
    Flat.plannerRun pl take s us = Flat.runLoop pl take { s with saw := false } us := by
  simp only [Flat.plannerRun, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem runLoop_mapping_fail (pl : Flat.Planner) (take : Bool) (s : Flat.PSt)
    (us : Nat → Flat.RunU)
    (h : Flat.buildMapping ⟨pl.source, pl.m, pl.target, pl.n, s.dropped, take⟩
      ((us 0).mapping.init pl.m pl.n) = none) :
    Flat.runLoop pl take s us = (.assertionFailed, s) := by
  rw [Flat.runLoop, h]

end Bbu.Unit.PlannerRunU
