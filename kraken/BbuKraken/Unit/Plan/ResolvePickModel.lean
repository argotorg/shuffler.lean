import BbuKraken.Unit.Plan.ResolveCandidates

namespace Bbu.Unit.ResolveU
open Flat

def CandidatesLive (M : Mapping) (cand : Vector Word MAX_N) (count : Word) : Prop :=
  ∀ i : Word, i < count → get M.dest (get cand i) ≠ NONE

def BestValid (p : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (dn : Vector (BitVec 8) MAX_N) (best : Word) (cls : BitVec 8) : Prop :=
  best = NONE ∨
    best < p.m ∧ get M.dest best ≠ NONE ∧
      cls = classify p sp M dn best ∧ cls ≠ NOCLASS

theorem candidatesLive_extend {M : Mapping} {cand : Vector Word MAX_N}
    {count off : Word} (hc : CandidatesLive M cand count)
    (hn : count.toNat < MAX_N) (ho : get M.dest off ≠ NONE) :
    CandidatesLive M (put cand count off) (count + 1) := by
  intro i hi
  rw [get_put _ _ _ hn]
  split
  · exact ho
  · exact hc i (by bv_omega)

theorem pickFrom_valid (p : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (dn : Vector (BitVec 8) MAX_N) (cand : Vector Word MAX_N)
    (count i best : Word) (cls : BitVec 8)
    (hc : CandidatesBound p.m cand count) (hl : CandidatesLive M cand count)
    (hb : BestValid p sp M dn best cls) :
    let q := pickFrom p sp M dn cand count i best cls
    BestValid p sp M dn q.1 q.2 := by
  rw [pickFrom]
  split
  · rename_i hi
    dsimp only
    split
    · exact pickFrom_valid p sp M dn cand count (i + 1) _ _ hc hl hb
    · split
      · exact pickFrom_valid p sp M dn cand count (i + 1) _ _ hc hl hb
      · rename_i hcls
        split
        · exact pickFrom_valid p sp M dn cand count (i + 1) _ _ hc hl
            (Or.inr ⟨hc i hi, hl i hi, rfl, hcls⟩)
        · exact pickFrom_valid p sp M dn cand count (i + 1) _ _ hc hl hb
  · exact hb
termination_by (count - i).toNat
decreasing_by all_goals exact Flat.sub_succ_lt ‹i < count›

theorem picked_valid (p : Planner) (M : Mapping) (cand : Vector Word MAX_N)
    (count : Word) (s : RState) (hc : CandidatesBound p.m cand count)
    (hl : CandidatesLive M cand count) :
    BestValid p s.spills M s.droppedNow (picked p M cand count s).1
      (picked p M cand count s).2 :=
  pickFrom_valid p s.spills M s.droppedNow cand count 0 NONE 0 hc hl (Or.inl rfl)

theorem picked_spill (p : Planner) (M : Mapping) (cand : Vector Word MAX_N)
    (count : Word) (s : RState) (hc : CandidatesBound p.m cand count)
    (hl : CandidatesLive M cand count)
    (hb : (picked p M cand count s).1 ≠ NONE)
    (hs : (picked p M cand count s).2 = SPILL) :
    p.allowed = true ∧ isVariable (get p.source (picked p M cand count s).1) = true := by
  have hv := (picked_valid p M cand count s hc hl).resolve_left hb
  exact classify_spill p s.spills M s.droppedNow _ (hv.2.2.1.symm.trans hs)

end Bbu.Unit.ResolveU
