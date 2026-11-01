module

public import BbuKraken.FlatPlan
import all BbuKraken.FlatPlan
public import BbuKraken.FlatPopRel
import all BbuKraken.FlatPopRel
public import BbuKraken.FlatList.Basic
import all BbuKraken.FlatList.Basic

@[expose] public section

/-! Bounds and inverse relations of the mapping built by the planner.
Only the live source and target ranges are constrained. The unused local-array
entries can keep any initial value. -/

namespace Bbu.Unit.PlannerRunU
open Flat

structure MapInv (m n : Word) (M : Flat.Mapping) : Prop where
  m_bound : m.toNat ≤ MAX_N
  n_bound : n.toNat ≤ MAX_N
  dest : ∀ p, p < m → get M.dest p = NONE ∨ get M.dest p < n
  pos : ∀ t, t < n → get M.pos t = NONE ∨ get M.pos t < m
  dest_inv : ∀ p, p < m → get M.dest p ≠ NONE → get M.pos (get M.dest p) = p
  pos_inv : ∀ t, t < n → get M.pos t ≠ NONE → get M.dest (get M.pos t) = t

theorem init_dest_none (u : Flat.Mapping) {m n p : Word}
    (hm : m.toNat ≤ MAX_N) (hp : p < m) : get (u.init m n).dest p = NONE := by
  have hpN : p.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hm
  simp only [Flat.Mapping.init, offsets, List.foldl_map]
  rw [get_toNat _ hpN, fold_put_get' (fun _ => NONE) _ hm hpN]
  exact ite_eq_left (BitVec.lt_def.mp hp)

theorem init_pos_none (u : Flat.Mapping) {m n t : Word}
    (hn : n.toNat ≤ MAX_N) (ht : t < n) : get (u.init m n).pos t = NONE := by
  have htN : t.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp ht) hn
  simp only [Flat.Mapping.init, offsets, List.foldl_map]
  rw [get_toNat _ htN, fold_put_get' (fun _ => NONE) _ hn htN]
  exact ite_eq_left (BitVec.lt_def.mp ht)

theorem mapInv_init (u : Flat.Mapping) {m n : Word}
    (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N) : MapInv m n (u.init m n) := by
  refine ⟨hm, hn, fun p hp => Or.inl (init_dest_none u hm hp),
    fun t ht => Or.inl (init_pos_none u hn ht), ?_, ?_⟩
  · intro p hp hne
    exact False.elim (hne (init_dest_none u hm hp))
  · intro t ht hne
    exact False.elim (hne (init_pos_none u hn ht))

theorem MapInv.bind {m n : Word} {M : Flat.Mapping} (h : MapInv m n M)
    {p t : Word} (hp : p < m) (ht : t < n)
    (hpd : get M.dest p = NONE) (htp : get M.pos t = NONE) :
    MapInv m n (M.bind p t) := by
  have hpN : p.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) h.m_bound
  have htN : t.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp ht) h.n_bound
  refine ⟨h.m_bound, h.n_bound, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change get (put M.dest p t) i = NONE ∨ get (put M.dest p t) i < n
    rw [get_put _ _ _ hpN]
    split
    · exact Or.inr ht
    · exact h.dest i hi
  · intro j hj
    change get (put M.pos t p) j = NONE ∨ get (put M.pos t p) j < m
    rw [get_put _ _ _ htN]
    split
    · exact Or.inr hp
    · exact h.pos j hj
  · intro i hi hne
    change get (put M.dest p t) i ≠ NONE at hne
    change get (put M.pos t p) (get (put M.dest p t) i) = i
    by_cases hip : i = p
    · subst i
      rw [get_put_self _ _ hpN, get_put_self _ _ htN]
    · rw [get_put_ne _ _ hip] at hne ⊢
      have hit : get M.dest i ≠ t := by
        intro he
        have hii := h.dest_inv i hi hne
        rw [he, htp] at hii
        have hn := h.dest i hi
        have hn' := hn.resolve_left hne
        have him : i.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) h.m_bound
        have hnone : i ≠ NONE := ne_NONE (by simp only [MAX_N] at him; omega)
        exact hnone hii.symm
      rw [get_put_ne _ _ hit, h.dest_inv i hi hne]
  · intro j hj hne
    change get (put M.pos t p) j ≠ NONE at hne
    change get (put M.dest p t) (get (put M.pos t p) j) = j
    by_cases hjt : j = t
    · subst j
      rw [get_put_self _ _ htN, get_put_self _ _ hpN]
    · rw [get_put_ne _ _ hjt] at hne ⊢
      have hjp : get M.pos j ≠ p := by
        intro he
        have hjj := h.pos_inv j hj hne
        rw [he, hpd] at hjj
        have hjn : j.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) h.n_bound
        have hnone : j ≠ NONE := ne_NONE (by simp only [MAX_N] at hjn; omega)
        exact hnone hjj.symm
      rw [get_put_ne _ _ hjp, h.pos_inv j hj hne]

theorem mapInv_mbMap {b : Flat.Builder} {M : Flat.Mapping} (h : MapInv b.m b.n M)
    {p t : Word} (hp : p < b.m) (ht : t < b.n) :
    MapInv b.m b.n (Flat.mbMap b M p t).2 := by
  unfold Flat.mbMap
  split
  · exact h
  · split
    · exact h
    · rename_i hpd
      split
      · exact h
      · rename_i htp
        exact h.bind hp ht (Classical.byContradiction hpd)
          (Classical.byContradiction htp)

theorem mbMap_none (b : Flat.Builder) (M : Flat.Mapping) (t : Word) :
    Flat.mbMap b M NONE t = (.assertionFailed, M) := by
  have hd : get M.dest NONE = 0#64 := by
    rw [Flat.get, dite_eq_right (by decide : ¬NONE.toNat < MAX_N)]
    rfl
  have hne : get M.dest NONE ≠ NONE := by rw [hd]; decide
  unfold Flat.mbMap
  split
  · rfl
  · rfl

theorem mapInv_mbMap_maybe {b : Flat.Builder} {M : Flat.Mapping} (h : MapInv b.m b.n M)
    {p t : Word} (hp : p = NONE ∨ p < b.m) (ht : t < b.n) :
    MapInv b.m b.n (Flat.mbMap b M p t).2 := by
  rcases hp with rfl | hp
  · rw [mbMap_none]; exact h
  · exact mapInv_mbMap h hp ht

theorem closestFrom_bound (b : Flat.Builder) (M : Flat.Mapping) (t : Word) (inW : Bool)
    (i best : Word) (hbest : best = NONE ∨ best < b.m) :
    Flat.closestFrom b M t inW i best = NONE ∨ Flat.closestFrom b M t inW i best < b.m := by
  rw [Flat.closestFrom]
  split
  · rename_i hi
    apply closestFrom_bound
    split
    · split
      · exact Or.inr hi
      · exact hbest
    · exact hbest
  · exact hbest
termination_by (b.m - i).toNat
decreasing_by exact Flat.sub_succ_lt ‹i < b.m›

theorem closestCopy_bound (b : Flat.Builder) (M : Flat.Mapping) (t : Word) (inW : Bool) :
    Flat.closestCopy b M t inW = NONE ∨ Flat.closestCopy b M t inW < b.m :=
  closestFrom_bound b M t inW 0 NONE (Or.inl rfl)

theorem absorbBest_bound (b : Flat.Builder) (M : Flat.Mapping) (j o best : Word)
    (hbest : best = NONE ∨ best < b.m) :
    Flat.absorbBest b M j o best = NONE ∨ Flat.absorbBest b M j o best < b.m := by
  rw [Flat.absorbBest]
  split
  · rename_i ho
    apply absorbBest_bound
    split
    · exact Or.inr ho
    · exact hbest
  · exact hbest
termination_by (b.m - o).toNat
decreasing_by exact Flat.sub_succ_lt ‹o < b.m›

theorem common_le_m (b : Flat.Builder) : Flat.commonSize b ≤ b.m := by
  unfold Flat.commonSize
  split <;> bv_omega

theorem common_le_n (b : Flat.Builder) : Flat.commonSize b ≤ b.n := by
  unfold Flat.commonSize
  split <;> bv_omega

theorem mapInv_inPlaceFrom (b : Flat.Builder) (M : Flat.Mapping) (j : Word)
    (h : MapInv b.m b.n M) : MapInv b.m b.n (Flat.inPlaceFrom b M j).2 := by
  rw [Flat.inPlaceFrom]
  split
  · rename_i hj
    have hjm : j < b.m := by have hm := common_le_m b; bv_omega
    have hjn : j < b.n := by have hn := common_le_n b; bv_omega
    split
    · have hm := mapInv_mbMap h hjm hjn
      dsimp only
      split
      · exact hm
      · exact mapInv_inPlaceFrom b _ _ hm
    · exact mapInv_inPlaceFrom b M _ h
  · exact h
termination_by (Flat.commonSize b - j).toNat
decreasing_by all_goals exact Flat.sub_succ_lt ‹j < Flat.commonSize b›

theorem mapInv_closestCopiesFrom (b : Flat.Builder) (M : Flat.Mapping) (j : Word)
    (h : MapInv b.m b.n M) : MapInv b.m b.n (Flat.closestCopiesFrom b M j).2 := by
  rw [Flat.closestCopiesFrom]
  split
  · rename_i hj
    split
    · have hm := mapInv_mbMap_maybe h (closestCopy_bound b M j false) hj
      dsimp only
      split
      · exact hm
      · exact mapInv_closestCopiesFrom b _ _ hm
    · exact mapInv_closestCopiesFrom b M _ h
  · exact h
termination_by (b.n - j).toNat
decreasing_by all_goals exact Flat.sub_succ_lt ‹j < b.n›

theorem mapInv_wildcardFrom (b : Flat.Builder) (M : Flat.Mapping) (saw : Bool) (j : Word)
    (h : MapInv b.m b.n M) : MapInv b.m b.n (Flat.wildcardFrom b M saw j).2.1 := by
  rw [Flat.wildcardFrom]
  split
  · rename_i hj
    split
    · dsimp only
      have hm := mapInv_mbMap_maybe h (closestCopy_bound b M j true) hj
      split
      · split
        · exact hm
        · exact mapInv_wildcardFrom b _ _ _ hm
      · split
        · split
          · exact hm
          · exact mapInv_wildcardFrom b _ _ _ hm
        · exact mapInv_wildcardFrom b M true _ h
    · exact mapInv_wildcardFrom b M saw _ h
  · exact h
termination_by (b.n - j).toNat
decreasing_by all_goals exact Flat.sub_succ_lt ‹j < b.n›

theorem mapInv_keepFrom (b : Flat.Builder) (M : Flat.Mapping) (j : Word)
    (h : MapInv b.m b.n M) : MapInv b.m b.n (Flat.keepFrom b M j).2 := by
  rw [Flat.keepFrom]
  split
  · rename_i hj
    have hjm : j < b.m := by have hm := common_le_m b; bv_omega
    have hjn : j < b.n := by have hn := common_le_n b; bv_omega
    split
    · have hm := mapInv_mbMap h hjm hjn
      dsimp only
      split
      · exact hm
      · exact mapInv_keepFrom b _ _ hm
    · exact mapInv_keepFrom b M _ h
  · exact h
termination_by (Flat.commonSize b - j).toNat
decreasing_by all_goals exact Flat.sub_succ_lt ‹j < Flat.commonSize b›

theorem mapInv_absorbFrom (b : Flat.Builder) (M : Flat.Mapping) (j : Word)
    (h : MapInv b.m b.n M) : MapInv b.m b.n (Flat.absorbFrom b M j).2 := by
  rw [Flat.absorbFrom]
  split
  · rename_i hj
    split
    · have hm := mapInv_mbMap_maybe h (absorbBest_bound b M j 0 NONE (Or.inl rfl)) hj
      dsimp only
      split
      · exact hm
      · exact mapInv_absorbFrom b _ _ hm
    · exact mapInv_absorbFrom b M _ h
  · exact h
termination_by (b.n - j).toNat
decreasing_by all_goals exact Flat.sub_succ_lt ‹j < b.n›

theorem mapInv_buildMapping {b : Flat.Builder} {M M' : Flat.Mapping} {saw : Bool}
    (h : MapInv b.m b.n M) (hr : Flat.buildMapping b M = some (M', saw)) :
    MapInv b.m b.n M' := by
  unfold Flat.buildMapping at hr
  dsimp only at hr
  have h1 := mapInv_inPlaceFrom b M 0 h
  split at hr
  · cases hr
  · try dsimp only at hr
    have h2 := mapInv_closestCopiesFrom b _ 0 h1
    split at hr
    · cases hr
    · try dsimp only at hr
      have h3 := mapInv_wildcardFrom b _ false 0 h2
      split at hr
      · cases hr
      · try dsimp only at hr
        have h4 := mapInv_keepFrom b _ 0 h3
        split at hr
        · cases hr
        · try dsimp only at hr
          have h5 := mapInv_absorbFrom b _ 0 h4
          split at hr
          · cases hr
          · cases hr
            exact h5

theorem planner_mapping_inv (b : Flat.Builder) (u : Flat.Mapping)
    (hm : b.m.toNat ≤ MAX_N) (hn : b.n.toNat ≤ MAX_N)
    {M : Flat.Mapping} {saw : Bool}
    (hr : Flat.buildMapping b (u.init b.m b.n) = some (M, saw)) : MapInv b.m b.n M :=
  mapInv_buildMapping (mapInv_init u hm hn) hr

end Bbu.Unit.PlannerRunU
