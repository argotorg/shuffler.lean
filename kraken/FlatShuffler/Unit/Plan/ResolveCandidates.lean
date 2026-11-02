module

public import FlatShuffler.Unit.Plan.ResolveCongruence
import all FlatShuffler.Unit.Plan.ResolveCongruence

@[expose] public section

namespace FlatShuffler.Unit.ResolveU
open Flat

theorem small_succ (w : Word) (hw : w.toNat < maxStackSize) :
    (w + 1).toNat = w.toNat + 1 := by
  have hw' : w.toNat < 1024 := hw
  bv_omega

theorem candidatesBound_extend {m count off : Word} {cand : Vector Word maxStackSize}
    (hc : CandidatesBound m cand count) (hn : count.toNat < maxStackSize) (ho : off < m) :
    CandidatesBound m (put cand count off) (count + 1) := by
  intro i hi
  rw [get_put _ _ _ hn]
  split
  · exact ho
  · exact hc i (by bv_omega)

def CandidatesRel (m : Word) :
    Option (Vector Word maxStackSize × Word) → Option (Vector Word maxStackSize × Word) → Prop
  | none, none => True
  | some (a, n), some (b, n') =>
      n = n' ∧ n.toNat ≤ maxStackSize ∧ SameBelow n a b ∧ CandidatesBound m a n
  | _, _ => False

theorem candidatesFrom_congr (r : RG) (hok : r.Ok) (size pos count : Word)
    (a b : Vector Word maxStackSize) (hsize : size.toNat ≤ maxStackSize)
    (hcount : count ≤ pos) (hpos : pos.toNat ≤ maxStackSize)
    (hcur : ∀ o : Word, o.toNat < size.toNat →
      get r.current.dest o = NONE ∨ (get r.current.dest o).toNat < r.p.targetSize.toNat)
    (hc : SameBelow count a b) (hb : CandidatesBound r.p.sourceSize a count) :
    CandidatesRel r.p.sourceSize (candidatesFrom r.M r.current size pos a count)
      (candidatesFrom r.M r.current size pos b count) := by
  by_cases h : pos < size
  · have hpN : pos.toNat < maxStackSize :=
      Nat.lt_of_lt_of_le (BitVec.lt_def.mp h) hsize
    have hpos' : (pos + 1).toNat ≤ maxStackSize := by rw [small_succ pos hpN]; omega
    by_cases hd : get r.current.dest pos = NONE
    · rw [candidates_skip_dest (cand := a) h hd, candidates_skip_dest (cand := b) h hd]
      exact candidatesFrom_congr r hok size (pos + 1) count a b hsize
        (by bv_omega) hpos' hcur hc hb
    · by_cases hp : get r.M.pos (get r.current.dest pos) = NONE
      · rw [candidates_skip_source (cand := a) h hp, candidates_skip_source (cand := b) h hp]
        exact candidatesFrom_congr r hok size (pos + 1) count a b hsize
          (by bv_omega) hpos' hcur hc hb
      · by_cases hr : get r.M.dest (get r.M.pos (get r.current.dest pos)) = NONE
        · rw [candidates_fail (cand := a) h hd hp hr, candidates_fail (cand := b) h hd hp hr]
          trivial
        · have hdN := (hcur pos (BitVec.lt_def.mp h)).resolve_left hd
          have hsN := (hok.planPos _ hdN).resolve_left hp
          have hs : get r.M.pos (get r.current.dest pos) < r.p.sourceSize := BitVec.lt_def.mpr hsN
          have hcN : count.toNat < maxStackSize := by
            have hcp := BitVec.le_def.mp hcount
            omega
          rw [candidates_add (cand := a) h hd hp hr, candidates_add (cand := b) h hd hp hr]
          exact candidatesFrom_congr r hok size (pos + 1) (count + 1) _ _ hsize
            (by bv_omega) hpos' hcur (sameBelow_extend hc hcN _)
            (candidatesBound_extend hb hcN hs)
  · rw [candidates_done (cand := a) h, candidates_done (cand := b) h]
    refine ⟨rfl, ?_, hc, hb⟩
    have hcp := BitVec.le_def.mp hcount
    omega
termination_by (size - pos).toNat
decreasing_by all_goals exact Flat.sub_succ_lt h

-- The caller does not need to choose the initial contents of resolve's locals.
theorem resolve_independent (r : RG) (hok : r.Ok) (s : MachineData) (ha : resolveA r s)
    (a b : Flat.ResolveU) :
    Flat.resolve r.p.fl r.spills r.dropped r.M (rdx s) (rcx s) r.current (r9 s) a =
      Flat.resolve r.p.fl r.spills r.dropped r.M (rdx s) (rcx s) r.current (r9 s) b := by
  obtain ⟨_, _, hsize, hblocked, _, hcur⟩ := ha
  have hpos : (rdx s + 1).toNat ≤ maxStackSize := by rw [small_succ _ hblocked]; omega
  have hcr := candidatesFrom_congr r hok (r9 s) (rdx s + 1) 0 a.candidates b.candidates
    hsize (by bv_omega) hpos hcur (by intro i hi; bv_omega) (by intro i hi; bv_omega)
  cases ha : candidatesFrom r.M r.current (r9 s) (rdx s + 1) a.candidates 0 with
  | none =>
    cases hb : candidatesFrom r.M r.current (r9 s) (rdx s + 1) b.candidates 0 with
    | none => simp only [Flat.resolve, ha, hb]
    | some c => simp only [ha, hb, CandidatesRel] at hcr
  | some c =>
    obtain ⟨ca, count⟩ := c
    cases hb : candidatesFrom r.M r.current (r9 s) (rdx s + 1) b.candidates 0 with
    | none => simp only [ha, hb, CandidatesRel] at hcr
    | some c' =>
      obtain ⟨cb, count'⟩ := c'
      simp only [ha, hb, CandidatesRel] at hcr
      obtain ⟨he, _, hc, hbound⟩ := hcr
      subst count'
      have hpass := passFrom_congr r.p.fl r.M ca cb count (rcx s) 0
        ⟨r.spills, r.dropped, zeroFrom r.p.sourceSize 0 a.droppedNow⟩
        ⟨r.spills, r.dropped, zeroFrom r.p.sourceSize 0 b.droppedNow⟩ hok.planner.sourceSizeFitsBuffer
        ⟨rfl, rfl, zeroFrom_independent r.p.sourceSize hok.planner.sourceSizeFitsBuffer a.droppedNow b.droppedNow⟩ hc hbound
      simp only [Flat.resolve, ha, hb]
      exact Prod.ext hpass.1 (Prod.ext hpass.2.spills hpass.2.dropped)

end FlatShuffler.Unit.ResolveU
