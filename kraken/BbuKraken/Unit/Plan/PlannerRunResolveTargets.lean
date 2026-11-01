module

public import BbuKraken.FlatPlan
import all BbuKraken.FlatPlan
public import BbuKraken.Unit.Plan.ResolveInitModel
import all BbuKraken.Unit.Plan.ResolveInitModel

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Flat

def SpillExtends (before after : BitVec 32 → BitVec 8) : Prop :=
  ∀ i, before i ≠ 0 → after i ≠ 0

theorem SpillExtends.refl (sp : BitVec 32 → BitVec 8) : SpillExtends sp sp :=
  fun _ h => h

theorem SpillExtends.trans {a b c : BitVec 32 → BitVec 8}
    (hab : SpillExtends a b) (hbc : SpillExtends b c) : SpillExtends a c :=
  fun i h => hbc i (hab i h)

theorem spillAdd_extends (sp : BitVec 32 → BitVec 8) (x : StackSlot) :
    SpillExtends sp (Flat.spillAdd sp x).2 := by
  unfold Flat.spillAdd
  split
  · exact .refl sp
  · split
    · exact .refl sp
    · intro i hi
      dsimp only [Flat.setByte]
      split
      · decide
      · exact hi

theorem passFrom_spills_extends (pl : Flat.Planner) (M : Flat.Mapping)
    (cand : Vector Word MAX_N) (count excess k : Word) (s : Flat.RState) :
    SpillExtends s.spills (Flat.passFrom pl M cand count excess k s).2.spills := by
  rw [Flat.passFrom]
  split
  · rename_i hk
    dsimp only
    split
    · exact .refl s.spills
    · split
      · exact .refl s.spills
      · have hs : SpillExtends s.spills
            (if (Flat.pickFrom pl s.spills M s.droppedNow cand count 0 NONE 0).2 = Flat.SPILL
             then (Flat.spillAdd s.spills
               (Flat.get pl.source (Flat.pickFrom pl s.spills M s.droppedNow cand count 0 NONE 0).1)).2
             else s.spills) := by
          split
          · exact spillAdd_extends _ _
          · exact .refl s.spills
        exact hs.trans (passFrom_spills_extends pl M cand count excess (k + 1)
          ⟨_, put s.dropped (Flat.pickFrom pl s.spills M s.droppedNow cand count 0 NONE 0).1 1,
            put s.droppedNow (Flat.pickFrom pl s.spills M s.droppedNow cand count 0 NONE 0).1 1⟩)
  · exact .refl s.spills
termination_by (excess - k).toNat
decreasing_by exact Flat.sub_succ_lt ‹k < excess›

theorem resolve_spills_extends (pl : Flat.Planner) (sp : BitVec 32 → BitVec 8)
    (dropped : Vector (BitVec 8) MAX_N) (M : Flat.Mapping)
    (blockedOffset excess : Word) (current : Flat.Mapping) (currentSize : Word)
    (u : Flat.ResolveU) :
    SpillExtends sp (Flat.resolve pl sp dropped M blockedOffset excess current currentSize u).2.1 := by
  unfold Flat.resolve
  split
  · exact .refl sp
  · dsimp only
    exact passFrom_spills_extends pl M _ _ excess 0 ⟨sp, dropped, _⟩

theorem spillIsSpilled_mono {sp sp' : BitVec 32 → BitVec 8}
    (h : SpillExtends sp sp') (x : StackSlot)
    (hx : Flat.spillIsSpilled sp x = true) : Flat.spillIsSpilled sp' x = true := by
  simp only [Flat.spillIsSpilled, Bool.and_eq_true, bne_iff_ne] at hx ⊢
  exact ⟨hx.1, h _ hx.2⟩

theorem targetsFrom_mono (pl : Flat.Planner) {sp sp' : BitVec 32 → BitVec 8}
    (h : SpillExtends sp sp') (j : Word)
    (ht : Flat.targetsFrom pl sp j = true) : Flat.targetsFrom pl sp' j = true := by
  rw [Flat.targetsFrom] at ht ⊢
  by_cases hj : j < pl.n
  · simp only [dite_eq_left hj] at ht ⊢
    simp only [Bool.and_eq_true, Bool.or_eq_true] at ht ⊢
    refine ⟨?_, targetsFrom_mono pl h (j + 1) ht.2⟩
    rcases ht.1 with h0 | hsp
    · exact Or.inl h0
    · exact Or.inr (spillIsSpilled_mono h _ hsp)
  · simp only [dite_eq_right hj]
termination_by (pl.n - j).toNat
decreasing_by exact Flat.sub_succ_lt hj

theorem resolve_targetsFrom (pl : Flat.Planner) (sp : BitVec 32 → BitVec 8)
    (dropped : Vector (BitVec 8) MAX_N) (M : Flat.Mapping)
    (blockedOffset excess : Word) (current : Flat.Mapping) (currentSize : Word)
    (u : Flat.ResolveU) {resolution : Flat.Resolution}
    {sp' : BitVec 32 → BitVec 8} {dropped' : Vector (BitVec 8) MAX_N}
    (hr : Flat.resolve pl sp dropped M blockedOffset excess current currentSize u =
      (resolution, sp', dropped'))
    (ht : Flat.targetsFrom pl sp 0 = true) : Flat.targetsFrom pl sp' 0 = true := by
  have hm := resolve_spills_extends pl sp dropped M blockedOffset excess current currentSize u
  rw [hr] at hm
  exact targetsFrom_mono pl hm 0 ht

end Bbu.Unit.PlannerRunU
