module

public import FlatShuffler.Unit.Plan.ResolveMem
import all FlatShuffler.Unit.Plan.ResolveMem
public import FlatShuffler.FlatList.Basic
import all FlatShuffler.FlatList.Basic

@[expose] public section

/-! The live part of a resolve local array determines every result. Bytes and
words outside the live ranges may have any value. -/

namespace FlatShuffler.Unit.ResolveU
open Flat

def SameBelow {α : Type} [Inhabited α] (n : Word)
    (a b : Vector α MAX_N) : Prop :=
  ∀ i : Word, i < n → get a i = get b i

def CandidatesBound (m : Word) (c : Vector Word MAX_N) (n : Word) : Prop :=
  ∀ i : Word, i < n → get c i < m

theorem sameBelow_put {α : Type} [Inhabited α] {n i : Word}
    {a b : Vector α MAX_N} (h : SameBelow n a b) (hi : i.toNat < MAX_N) (x : α) :
    SameBelow n (put a i x) (put b i x) := by
  intro j hj
  rw [get_put _ _ _ hi, get_put _ _ _ hi]
  split
  · rfl
  · exact h j hj

theorem sameBelow_extend {α : Type} [Inhabited α] {n : Word}
    {a b : Vector α MAX_N} (h : SameBelow n a b) (hn : n.toNat < MAX_N) (x : α) :
    SameBelow (n + 1) (put a n x) (put b n x) := by
  intro i hi
  rw [get_put _ _ _ hn, get_put _ _ _ hn]
  split
  · rfl
  · exact h i (by bv_omega)

theorem zeroFrom_before (m o q : Word) (dn : Vector (BitVec 8) MAX_N) (hq : q < o) :
    get (zeroFrom m o dn) q = get dn q := by
  rw [zeroFrom]
  split
  · rw [zeroFrom_before m (o + 1) q _ (by bv_omega), get_put_ne _ _ (by bv_omega)]
  · rfl
termination_by (m - o).toNat
decreasing_by exact Flat.sub_succ_lt ‹o < m›

theorem zeroFrom_zero (m o q : Word) (dn : Vector (BitVec 8) MAX_N)
    (hm : m.toNat ≤ MAX_N) (ho : o ≤ q) (hq : q < m) :
    get (zeroFrom m o dn) q = 0#8 := by
  have hom : o < m := by bv_omega
  rw [zeroFrom, dite_eq_left hom]
  by_cases he : q = o
  · rw [zeroFrom_before m (o + 1) q _ (by bv_omega), he,
      get_put_self _ _ (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hom) hm)]
    rfl
  · exact zeroFrom_zero m (o + 1) q _ hm (by bv_omega) hq
termination_by (m - o).toNat
decreasing_by exact Flat.sub_succ_lt hom

theorem zeroFrom_independent (m : Word) (hm : m.toNat ≤ MAX_N)
    (a b : Vector (BitVec 8) MAX_N) : SameBelow m (zeroFrom m 0 a) (zeroFrom m 0 b) := by
  intro q hq
  rw [zeroFrom_zero m 0 q a hm (by bv_omega) hq,
    zeroFrom_zero m 0 q b hm (by bv_omega) hq]

theorem otherFrom_congr (p : Planner) (M : Mapping) (a b : Vector (BitVec 8) MAX_N)
    (h : SameBelow p.m a b) (off o : Word) :
    otherFrom p M a off o = otherFrom p M b off o := by
  conv => lhs; rw [otherFrom]
  conv => rhs; rw [otherFrom]
  by_cases ho : o < p.m
  · simp only [dite_eq_left ho, h o ho]
    split
    · rfl
    · exact otherFrom_congr p M a b h off (o + 1)
  · simp only [dite_eq_right ho]
termination_by (p.m - o).toNat
decreasing_by exact Flat.sub_succ_lt ho

theorem classify_congr (p : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (a b : Vector (BitVec 8) MAX_N) (h : SameBelow p.m a b) (off : Word) :
    classify p sp M a off = classify p sp M b off := by
  have he : hasOtherRetainedCopy p M a off = hasOtherRetainedCopy p M b off :=
    otherFrom_congr p M a b h off 0
  simp only [classify, he]

theorem pickFrom_bound (p : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (dn : Vector (BitVec 8) MAX_N) (cand : Vector Word MAX_N) (count i best : Word)
    (cls : BitVec 8) (hc : CandidatesBound p.m cand count)
    (hb : best = NONE ∨ best < p.m) :
    (pickFrom p sp M dn cand count i best cls).1 = NONE ∨
      (pickFrom p sp M dn cand count i best cls).1 < p.m := by
  rw [pickFrom]
  split
  · rename_i hi
    dsimp only
    split
    · exact pickFrom_bound p sp M dn cand count (i + 1) _ _ hc hb
    · split
      · exact pickFrom_bound p sp M dn cand count (i + 1) _ _ hc hb
      · split
        · exact pickFrom_bound p sp M dn cand count (i + 1) _ _ hc (Or.inr (hc i hi))
        · exact pickFrom_bound p sp M dn cand count (i + 1) _ _ hc hb
  · exact hb
termination_by (count - i).toNat
decreasing_by all_goals exact Flat.sub_succ_lt ‹i < count›

theorem pickFrom_congr (p : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (a b : Vector (BitVec 8) MAX_N) (cand cand' : Vector Word MAX_N)
    (count i best : Word) (cls : BitVec 8)
    (hd : SameBelow p.m a b) (hc : SameBelow count cand cand')
    (hb : CandidatesBound p.m cand count) :
    pickFrom p sp M a cand count i best cls = pickFrom p sp M b cand' count i best cls := by
  conv => lhs; rw [pickFrom]
  conv => rhs; rw [pickFrom]
  by_cases hi : i < count
  · simp only [dite_eq_left hi]
    rw [← hc i hi, hd _ (hb i hi), classify_congr p sp M a b hd]
    split
    · exact pickFrom_congr p sp M a b cand cand' count (i + 1) _ _ hd hc hb
    · split
      · exact pickFrom_congr p sp M a b cand cand' count (i + 1) _ _ hd hc hb
      · split
        · exact pickFrom_congr p sp M a b cand cand' count (i + 1) _ _ hd hc hb
        · exact pickFrom_congr p sp M a b cand cand' count (i + 1) _ _ hd hc hb
  · simp only [dite_eq_right hi]
termination_by (count - i).toNat
decreasing_by all_goals exact Flat.sub_succ_lt hi

structure StateRel (m : Word) (a b : RState) : Prop where
  spills : a.spills = b.spills
  dropped : a.dropped = b.dropped
  droppedNow : SameBelow m a.droppedNow b.droppedNow

def PassRel (m : Word) (a b : Resolution × RState) : Prop :=
  a.1 = b.1 ∧ StateRel m a.2 b.2

theorem passFrom_congr (p : Planner) (M : Mapping) (cand cand' : Vector Word MAX_N)
    (count excess k : Word) (a b : RState) (hm : p.m.toNat ≤ MAX_N)
    (hs : StateRel p.m a b) (hc : SameBelow count cand cand')
    (hb : CandidatesBound p.m cand count) :
    PassRel p.m (passFrom p M cand count excess k a) (passFrom p M cand' count excess k b) := by
  have hp : pickFrom p a.spills M a.droppedNow cand count 0 NONE 0 =
      pickFrom p b.spills M b.droppedNow cand' count 0 NONE 0 := by
    rw [← hs.spills]
    exact pickFrom_congr p a.spills M _ _ _ _ count 0 NONE 0 hs.droppedNow hc hb
  have hbound := pickFrom_bound p a.spills M a.droppedNow cand count 0 NONE 0 hb (Or.inl rfl)
  conv => arg 2; rw [passFrom]
  conv => arg 3; rw [passFrom]
  by_cases hk : k < excess
  · simp only [dite_eq_left hk]
    rw [← hp, ← hs.spills]
    split
    · exact ⟨rfl, hs⟩
    · rename_i hbest
      have hlt : (pickFrom p a.spills M a.droppedNow cand count 0 NONE 0).1 < p.m :=
        hbound.resolve_left hbest
      split
      · exact ⟨rfl, hs⟩
      · apply passFrom_congr p M cand cand' count excess (k + 1) _ _ hm
        · refine ⟨rfl, ?_, ?_⟩
          · rw [hs.dropped]
          · exact sameBelow_put hs.droppedNow
              (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hlt) hm) 1
        · exact hc
        · exact hb
  · simp only [dite_eq_right hk]
    exact ⟨rfl, hs⟩
termination_by (excess - k).toNat
decreasing_by exact Flat.sub_succ_lt hk

end FlatShuffler.Unit.ResolveU
