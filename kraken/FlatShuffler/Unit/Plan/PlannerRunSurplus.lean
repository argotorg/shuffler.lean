module

public import FlatShuffler.Unit.Plan.PlannerRunSafety
import all FlatShuffler.Unit.Plan.PlannerRunSafety

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open Flat

def SurplusPick (st : Flat.St) (i : Word) : Prop :=
  i = NONE ∨ (i < st.size ∧ get st.dest i = NONE)

theorem surplus_scan_pick (st : Flat.St) (p sh dp : Word) (hp : p ≤ st.size)
    (hsh : SurplusPick st sh) (hdp : SurplusPick st dp) :
    SurplusPick st (Flat.surplusScan st p sh dp).1 ∧
      SurplusPick st (Flat.surplusScan st p sh dp).2 := by
  rw [Flat.surplusScan]
  simp only [BitVec.ofNat_eq_ofNat]
  split
  · exact ⟨hsh, hdp⟩
  · rename_i h0
    have hq : p - 1#64 < st.size := by bv_omega
    split
    · rename_i hs
      have hsur : get st.dest (p - 1#64) = NONE := by
        simpa only [Flat.isSurplus, beq_iff_eq, BitVec.ofNat_eq_ofNat] using hs
      apply surplus_scan_pick st (p - 1#64) _ _ (by bv_omega)
      · split
        · exact Or.inr ⟨hq, hsur⟩
        · exact hsh
      · split
        · exact Or.inr ⟨hq, hsur⟩
        · exact hdp
    · exact surplus_scan_pick st (p - 1#64) sh dp (by bv_omega) hsh hdp
termination_by p.toNat
decreasing_by all_goals bv_omega

theorem surplus_scan_none (st : Flat.St) (p sh dp : Word)
    (hn : (Flat.surplusScan st p sh dp).1 = NONE) :
    sh = NONE ∧ ∀ i, i < p → get st.dest i ≠ NONE := by
  rw [Flat.surplusScan] at hn
  simp only [BitVec.ofNat_eq_ofNat] at hn
  split at hn
  · rename_i h0
    exact ⟨hn, fun i hi => by rw [h0] at hi; exact False.elim (by bv_omega)⟩
  · rename_i h0
    split at hn
    · obtain ⟨hs, _⟩ := surplus_scan_none st (p - 1#64) _ _ hn
      have hnq : p - 1#64 ≠ NONE := by
        intro he
        have heN := congrArg BitVec.toNat he
        rw [Flat.toNat_NONE] at heN
        bv_omega
      split at hs
      · exact False.elim (hnq hs)
      · exact False.elim (‹¬sh = NONE› hs)
    · rename_i hsur
      obtain ⟨hs, hall⟩ := surplus_scan_none st (p - 1#64) sh dp hn
      refine ⟨hs, fun i hi => ?_⟩
      by_cases he : i = p - 1#64
      · subst i
        simpa only [Flat.isSurplus, beq_iff_eq, BitVec.ofNat_eq_ofNat] using hsur
      · exact hall i (by bv_omega)
termination_by p.toNat
decreasing_by all_goals bv_omega

theorem equalBelow_pick (st : Flat.St) (p : Word) (hp : p ≤ st.size) :
    SurplusPick st (Flat.equalBelow st p) := by
  rw [Flat.equalBelow]
  simp only [BitVec.ofNat_eq_ofNat]
  split
  · exact Or.inl rfl
  · rename_i h0
    split
    · rename_i hs
      exact Or.inr ⟨by bv_omega, by simpa only [Flat.isSurplus, beq_iff_eq] using hs.1⟩
    · exact equalBelow_pick st (p - 1#64) (by bv_omega)
termination_by p.toNat
decreasing_by all_goals bv_omega

def PlannedSupport (planned : Vector Word maxStackSize) (st : Flat.St) : Prop :=
  ∀ i, i < st.size → get st.dest i ≠ NONE → get planned (get st.dest i) ≠ NONE

theorem PlannedSupport.swapDestinations {planned : Vector Word maxStackSize} {st : Flat.St}
    (hs : PlannedSupport planned st) (hm : st.size.toNat ≤ maxStackSize) {a b : Word}
    (ha : a < st.size) (hb : b < st.size) :
    PlannedSupport planned (Flat.swapDestinations st a b) := by
  intro i hi hn
  have ma := Nat.lt_of_lt_of_le (BitVec.lt_def.mp ha) hm
  have mb := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hb) hm
  rw [swap_dest_read ma mb] at hn ⊢
  exact hs _ (exchangeAt_lt ha hb hi) hn

structure Prep (planned : Vector Word maxStackSize) (m : Nat) (st : Flat.St) : Prop where
  map : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩
  support : PlannedSupport planned st
  pend : st.pend.toNat ≤ st.targetSize.toNat
  size : st.size.toNat ≤ m
  trace : st.trace.length + 2 * st.size.toNat ≤ 2 * m

theorem Prep.swapDestinations {planned : Vector Word maxStackSize} {m : Nat} {st : Flat.St}
    (h : Prep planned m st) {a b : Word} (ha : a < st.size) (hb : b < st.size) :
    Prep planned m (Flat.swapDestinations st a b) :=
  ⟨h.map.swapDestinations ha hb, h.support.swapDestinations h.map.m_bound ha hb,
    h.pend, h.size, h.trace⟩

theorem Prep.pop_none {planned : Vector Word maxStackSize} {m : Nat} {st : Flat.St}
    (h : Prep planned m st) (h0 : st.size ≠ 0#64)
    (hn : get st.dest (st.size - 1#64) = NONE) : Prep planned m (Flat.pop st).2 := by
  have hm := h.map.pop_none h0 hn
  rw [Pop.pop_none st h0 hn] at hm ⊢
  simp only [BitVec.ofNat_eq_ofNat] at hm ⊢
  refine ⟨hm, ?_, h.pend, ?_, ?_⟩
  · intro i hi hne
    exact h.support i (by bv_omega) hne
  · change (st.size - 1#64).toNat ≤ m
    have hs := h.size
    bv_omega
  · change (st.trace ++ [Op.pop]).length + 2 * (st.size - 1#64).toNat ≤ 2 * m
    have hs : (st.size - 1#64).toNat + 1 = st.size.toNat := by bv_omega
    have ht := h.trace
    simp only [List.length_append, List.length_singleton]
    omega

theorem Prep.swap_pop {planned : Vector Word maxStackSize} {m : Nat} {st : Flat.St}
    (h : Prep planned m st) {i : Word} (hi : i < st.size)
    (hn : get st.dest i = NONE) (hd : (Flat.swapWith st i).1 = .done) :
    Prep planned m (Flat.pop (Flat.swapWith st i).2).2 := by
  have h0 : st.size ≠ 0#64 := by bv_omega
  have ht : st.size - 1#64 < st.size := by bv_omega
  have hmap : MapInv (Flat.stackSwap st i).size (Flat.stackSwap st i).targetSize
      ⟨(Flat.stackSwap st i).dest, (Flat.stackSwap st i).pos⟩ := h.map
  have hsupport : PlannedSupport planned (Flat.stackSwap st i) := h.support
  have hm := hmap.swapDestinations hi ht
  have hs := hsupport.swapDestinations h.map.m_bound hi ht
  have htop : get (Flat.swapDestinations (Flat.stackSwap st i) i (st.size - 1#64)).dest
      (st.size - 1#64) = NONE := by
    rw [swap_dest_read
      (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) h.map.m_bound)
      (Nat.lt_of_lt_of_le (BitVec.lt_def.mp ht) h.map.m_bound)]
    by_cases he : st.size - 1#64 = i <;> simp [exchangeAt, he, hn, Flat.stackSwap]
  have hsw : (Flat.swapWith st i).2 =
      Flat.swapDestinations (Flat.stackSwap st i) i (st.size - 1#64) := by
    simpa only [BitVec.ofNat_eq_ofNat] using (Surplus.swap_done hd).2
  rw [hsw]
  let sw := Flat.swapDestinations (Flat.stackSwap st i) i (st.size - 1#64)
  have hp := MapInv.pop_none (st := sw) hm h0 htop
  have he := Pop.pop_none sw h0 htop
  rw [he] at hp ⊢
  simp only [BitVec.ofNat_eq_ofNat] at hp ⊢
  refine ⟨hp, ?_, h.pend, ?_, ?_⟩
  · intro j hj hne
    exact hs j (by
      change j < st.size - 1#64 at hj
      change j < st.size
      bv_omega) hne
  · change (st.size - 1#64).toNat ≤ m
    have hb := h.size
    bv_omega
  · change ((st.trace ++ [_]) ++ [Op.pop]).length + 2 * (st.size - 1#64).toNat ≤ 2 * m
    have hs : (st.size - 1#64).toNat + 1 = st.size.toNat := by bv_omega
    have ht := h.trace
    simp only [List.length_append, List.length_singleton]
    omega

theorem Prep.pop_step {planned : Vector Word maxStackSize} {m : Nat} {st : Flat.St}
    (h : Prep planned m st) (h0 : st.size ≠ 0#64)
    (hn : get st.dest (st.size - 1#64) = NONE) :
    (Flat.pop st).1 = .done ∧ Prep planned m (Flat.pop st).2 ∧
      (Flat.pop st).2.size.toNat + 1 = st.size.toNat := by
  refine ⟨?_, h.pop_none h0 hn, ?_⟩
  · rw [Pop.pop_none st h0 hn]
  · rw [Pop.pop_none st h0 hn]
    simp only [BitVec.ofNat_eq_ofNat]
    change (st.size - 1#64).toNat + 1 = st.size.toNat
    bv_omega

theorem Prep.ctorP {m n : Word} {M : Flat.Mapping} (h : MapInv m n M)
    (data target : Vector StackSlot maxStackSize) (spills : BitVec 32 → BitVec 8)
    (u : Flat.Uninit) : Prep M.pos m.toNat (Flat.ctorP data m target n M spills u) := by
  have hm := h.copy ⟨u.dest, u.pos⟩
  simp only [Flat.ctorP, Flat.pend_fold]
  refine ⟨hm, ?_, ?_, Nat.le_refl _, ?_⟩
  · intro i hi hn
    change get M.pos (get (Flat.Mapping.copy ⟨u.dest, u.pos⟩ M m n).dest i) ≠ NONE
    rw [copy_dest ⟨u.dest, u.pos⟩ h.m_bound hi] at hn ⊢
    intro he
    have hp := h.dest_inv i hi hn
    rw [he] at hp
    exact Flat.ne_none (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) h.m_bound) hp.symm
  · simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_add, BitVec.toNat_ofNat]
    apply Nat.le_trans (Nat.mod_le _ _)
    have hc := List.countP_le_length (p := fun d =>
      get (Flat.Mapping.copy ⟨u.dest, u.pos⟩ M m n).pos d = NONE) (l := Flat.offsets n)
    simpa only [Flat.offsets, List.length_map, List.length_range] using hc
  · simp only [List.length_nil]
    omega

def HasNoSurplus (st : Flat.St) : Prop := ∀ i, i < st.size → get st.dest i ≠ NONE

theorem Prep.surplus_pass {planned : Vector Word maxStackSize} {m : Nat} {st : Flat.St}
    (h : Prep planned m st) (h0 : st.size ≠ 0#64) :
    match Flat.surplusPass st with
    | .error r => r.1 = .done → Prep planned m r.2 ∧ HasNoSurplus r.2
    | .ok u => Prep planned m u ∧ u.size.toNat + 1 = st.size.toNat := by
  have hv := surplus_scan_pick st st.size NONE NONE (BitVec.le_refl _)
    (Or.inl rfl) (Or.inl rfl)
  unfold Flat.surplusPass
  generalize hsc : Flat.surplusScan st st.size NONE NONE = sc at hv ⊢
  obtain ⟨sh, dp⟩ := sc
  dsimp only at hv ⊢
  by_cases hsh : sh = NONE
  · simp only [hsh, ↓reduceIte]
    intro _
    refine ⟨h, ?_⟩
    apply (surplus_scan_none st st.size NONE NONE ?_).2
    rw [hsc]
    exact hsh
  by_cases hdp : dp = NONE
  · simp only [hsh, hdp, ↓reduceIte]
    intro hd
    unfold Flat.blockSwapUnreachable Flat.block at hd
    split at hd <;> cases hd
  have hshv := hv.1.resolve_left hsh
  have hdpv := hv.2.resolve_left hdp
  simp only [hsh, hdp, ↓reduceIte]
  have ht : st.size - 1#64 < st.size := by bv_omega
  simp only [BitVec.ofNat_eq_ofNat]
  by_cases htop : sh = st.size - 1#64
  · rw [ite_eq_left htop]
    dsimp only
    have hn : get st.dest (st.size - 1#64) = NONE := htop ▸ hshv.2
    obtain ⟨hd, hp, hs⟩ := h.pop_step h0 hn
    simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte]
    exact ⟨hp, hs⟩
  rw [ite_eq_right htop]
  by_cases heq : Flat.equalBelow st (st.size - 1#64) ≠ NONE
  · rw [ite_eq_left heq]
    dsimp only
    have hq := (equalBelow_pick st (st.size - 1#64) (by bv_omega)).resolve_left heq
    let u := Flat.swapDestinations st (Flat.equalBelow st (st.size - 1#64)) (st.size - 1#64)
    have hu := h.swapDestinations hq.1 ht
    have hn : get u.dest (u.size - 1#64) = NONE := by
      change get (Flat.swapDestinations st (Flat.equalBelow st (st.size - 1#64))
        (st.size - 1#64)).dest (st.size - 1#64) = NONE
      rw [swap_dest_read
        (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hq.1) h.map.m_bound)
        (Nat.lt_of_lt_of_le (BitVec.lt_def.mp ht) h.map.m_bound)]
      have hx : exchangeAt (Flat.equalBelow st (st.size - 1#64)) (st.size - 1#64)
          (st.size - 1#64) = Flat.equalBelow st (st.size - 1#64) := by
        unfold exchangeAt
        split
        · assumption
        · simp only [↓reduceIte]
      rw [hx]
      exact hq.2
    obtain ⟨hd, hp, hs⟩ := Prep.pop_step (st := u) hu h0 hn
    dsimp only [u] at hd hp hs
    simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte]
    exact ⟨hp, hs⟩
  · rw [ite_eq_right heq]
    by_cases hd : (Flat.swapWith st dp).1 = .done
    · have hp := h.swap_pop hdpv.1 hdpv.2 hd
      have hs := Surplus.swap_done hd
      have hsz : (Flat.swapWith st dp).2.size = st.size := by rw [hs.2]; rfl
      have hpop : (Flat.pop (Flat.swapWith st dp).2).1 = .done := by
        simp only [Flat.pop, Flat.stackPop, BitVec.ofNat_eq_ofNat, hsz, h0,
          ne_eq, not_true_eq_false, ↓reduceIte]
      simp only [hd, hpop, ne_eq, not_true_eq_false, ↓reduceIte]
      refine ⟨hp, ?_⟩
      have hz := (Surplus.pop_done hpop).2.1
      rw [hz, hsz]
      simp only [BitVec.ofNat_eq_ofNat]
      bv_omega
    · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
      exact False.elim

theorem Prep.surplusLoop {planned : Vector Word maxStackSize} {m : Nat}
    (fuel : Nat) {st : Flat.St} (h : Prep planned m st) (hf : st.size.toNat ≤ fuel)
    (hd : (Flat.surplusLoop st fuel).1 = .done) :
    Prep planned m (Flat.surplusLoop st fuel).2 ∧
      HasNoSurplus (Flat.surplusLoop st fuel).2 := by
  cases fuel with
  | zero =>
    change Prep planned m st ∧ HasNoSurplus st
    exact ⟨h, fun i hi => by have hb := BitVec.lt_def.mp hi; omega⟩
  | succ fuel =>
    rw [Flat.surplusLoop] at hd ⊢
    by_cases h0 : st.size = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, h0, ↓reduceIte] at hd ⊢
      exact ⟨h, fun i hi => by rw [h0] at hi; exact False.elim (by bv_omega)⟩
    simp only [BitVec.ofNat_eq_ofNat, h0, ↓reduceIte] at hd ⊢
    have hp := h.surplus_pass h0
    cases hr : Flat.surplusPass st with
    | error r =>
      rw [hr] at hp hd
      dsimp only at hd ⊢
      exact hp hd
    | ok u =>
      rw [hr] at hp hd
      dsimp only at hd ⊢
      exact hp.1.surplusLoop fuel (by omega) hd
termination_by fuel

theorem Prep.removeSurplus {planned : Vector Word maxStackSize} {m : Nat} {st : Flat.St}
    (h : Prep planned m st) (hd : (Flat.removeSurplus st).1 = .done) :
    Prep planned m (Flat.removeSurplus st).2 ∧ HasNoSurplus (Flat.removeSurplus st).2 :=
  h.surplusLoop st.size.toNat (Nat.le_refl _) hd

end FlatShuffler.Unit.PlannerRunU
