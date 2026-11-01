module

public import BbuKraken.Unit.Plan.PlannerRunSurplus
import all BbuKraken.Unit.Plan.PlannerRunSurplus
public import BbuKraken.Unit.PermuteModel
import all BbuKraken.Unit.PermuteModel

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Flat

theorem swapDestinations_noSurplus {st : Flat.St}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    {a b : Word} (ha : a < st.size) (hb : b < st.size) :
    HasNoSurplus (Flat.swapDestinations st a b) := by
  intro i hi
  rw [swap_dest_read
    (Nat.lt_of_lt_of_le (BitVec.lt_def.mp ha) hm.m_bound)
    (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hb) hm.m_bound)]
  exact hn _ (exchangeAt_lt ha hb hi)

theorem exchange_cont_state {st st' : Flat.St} {top pos : Word}
    {p p' : Vector Word MAX_N} (he : Flat.exchange st top p pos = .cont st' p') :
    st' = Flat.swapDestinations st pos top ∨
      st' = Flat.swapDestinations (Flat.stackSwap st pos) pos top := by
  unfold Flat.exchange at he
  split at he
  · cases he; exact Or.inl rfl
  · split at he
    · cases he
    · cases he; exact Or.inr rfl

theorem exchange_cont_safe {st st' : Flat.St} {top pos : Word}
    {p p' : Vector Word MAX_N}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (ht : top < st.size) (hp : pos < st.size)
    (he : Flat.exchange st top p pos = .cont st' p') :
    MapInv st'.size st'.targetSize ⟨st'.dest, st'.pos⟩ ∧ HasNoSurplus st' ∧
      st'.size = st.size ∧ st'.targetSize = st.targetSize ∧ st'.pend = st.pend ∧
      st'.trace.length ≤ st.trace.length + 1 := by
  rcases exchange_cont_state he with rfl | rfl
  · exact ⟨hm.swapDestinations hp ht, swapDestinations_noSurplus hm hn hp ht,
      rfl, rfl, rfl, Nat.le_add_right _ _⟩
  · have hm' : MapInv (Flat.stackSwap st pos).size (Flat.stackSwap st pos).targetSize
        ⟨(Flat.stackSwap st pos).dest, (Flat.stackSwap st pos).pos⟩ := hm
    have hn' : HasNoSurplus (Flat.stackSwap st pos) := hn
    refine ⟨hm'.swapDestinations hp ht, swapDestinations_noSurplus hm' hn' hp ht,
      rfl, rfl, rfl, ?_⟩
    change (st.trace ++ [_]).length ≤ st.trace.length + 1
    simp only [List.length_append, List.length_singleton, Nat.le_refl]

theorem permuteStep_done {st st' : Flat.St} {top : Word} {p : Vector Word MAX_N}
    (he : Flat.permuteStep st top p = .ret (.done, st')) : st' = st := by
  unfold Flat.permuteStep at he
  dsimp only at he
  split at he
  · split at he
    · cases he; rfl
    · unfold Flat.exchange at he
      split at he
      · cases he
      · split at he
        · unfold Flat.blockSwapUnreachable Flat.block at he
          split at he <;> cases he
        · cases he
  · unfold Flat.exchange at he
    split at he
    · cases he
    · split at he
      · unfold Flat.blockSwapUnreachable Flat.block at he
        split at he <;> cases he
      · cases he

theorem permuteStep_cont_safe {st st' : Flat.St} {p p' : Vector Word MAX_N}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (h0 : 0#64 < st.size) (hb : Bij st.size p)
    (he : Flat.permuteStep st (st.size - 1#64) p = .cont st' p') :
    MapInv st'.size st'.targetSize ⟨st'.dest, st'.pos⟩ ∧ HasNoSurplus st' ∧
      st'.size = st.size ∧ st'.targetSize = st.targetSize ∧ st'.pend = st.pend ∧
      st'.trace.length ≤ st.trace.length + 1 := by
  have ht : st.size - 1#64 < st.size := by bv_omega
  unfold Flat.permuteStep at he
  dsimp only at he
  split at he
  · split at he
    · cases he
    · rename_i hne
      rcases Permute.misplacedBelow_spec p (st.size - 1#64) (st.size - 1#64) with h | ⟨hp, _⟩
      · exact False.elim (hne h)
      · exact exchange_cont_safe hm hn ht (by bv_omega) he
  · exact exchange_cont_safe hm hn ht (hb.1 _ ht) he

theorem permuteLoop_safe {fuel : Nat} {st st' : Flat.St} {p : Vector Word MAX_N}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (h0 : 0#64 < st.size) (hb : Bij st.size p)
    (he : Flat.permuteLoop fuel st (st.size - 1#64) p = (.done, st')) :
    MapInv st'.size st'.targetSize ⟨st'.dest, st'.pos⟩ ∧ HasNoSurplus st' ∧
      st'.size = st.size ∧ st'.targetSize = st.targetSize ∧ st'.pend = st.pend ∧
      st'.trace.length ≤ st.trace.length + fuel := by
  induction fuel generalizing st st' p with
  | zero => cases he
  | succ fuel ih =>
    rw [Flat.permuteLoop] at he
    cases hs : Flat.permuteStep st (st.size - 1#64) p with
    | ret r =>
      rw [hs] at he
      dsimp only at he
      have hr : Flat.permuteStep st (st.size - 1#64) p = .ret (.done, st') := by
        rw [hs, he]
      have heq := permuteStep_done hr
      subst st'
      exact ⟨hm, hn, rfl, rfl, rfl, Nat.le_add_right _ _⟩
    | cont mid p' =>
      rw [hs] at he
      dsimp only at he
      obtain ⟨hm', hn', hsz, hnt, hpend, htrace⟩ := permuteStep_cont_safe hm hn h0 hb hs
      have hb' : Bij mid.size p' := by
        rw [hsz]
        exact (Permute.permuteStep_cont hm.m_bound h0 hb hs).1
      have h0' : 0#64 < mid.size := by rw [hsz]; exact h0
      have he' : Flat.permuteLoop fuel mid (mid.size - 1#64) p' = (.done, st') := by
        simpa only [hsz] using he
      obtain ⟨hm'', hn'', hsz', hnt', hpend', htrace'⟩ := ih hm' hn' h0' hb' he'
      exact ⟨hm'', hn'', hsz'.trans hsz, hnt'.trans hnt, hpend'.trans hpend, by omega⟩

theorem permute_safe {st st' : Flat.St} {p : Vector Word MAX_N}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (hb : Bij st.size p) (he : Flat.permute st p = (.done, st')) :
    MapInv st'.size st'.targetSize ⟨st'.dest, st'.pos⟩ ∧ HasNoSurplus st' ∧
      st'.size = st.size ∧ st'.targetSize = st.targetSize ∧ st'.pend = st.pend ∧
      st'.trace.length ≤ st.trace.length + 2 * st.size.toNat := by
  unfold Flat.permute at he
  split at he
  · cases he
    exact ⟨hm, hn, rfl, rfl, rfl, Nat.le_add_right _ _⟩
  · rename_i h0
    dsimp only at he
    split at he
    · cases he
    · rename_i p' hp'
      exact permuteLoop_safe hm hn (by bv_omega)
        (Permute.regroup_bij hm.m_bound hb hp') he

theorem lowest_preserves {planned : Vector Word MAX_N} {l : Flat.Locals}
    {st st' : Flat.St}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (hlow : Flat.LowOk planned st)
    (he : Flat.permuteAtLowestHeight planned l st = (.done, st')) :
    MapInv st'.size st'.targetSize ⟨st'.dest, st'.pos⟩ ∧ HasNoSurplus st' ∧
      st'.size = st.size ∧ st'.targetSize = st.targetSize ∧ st'.pend = st.pend ∧
      st'.trace.length ≤ st.trace.length + 2 * st.size.toNat := by
  unfold Flat.permuteAtLowestHeight at he
  split at he
  · cases he
  · rename_i sc hsc
    split at he
    · cases he
    · rename_i hc
      exact permute_safe hm hn (hlow l sc hsc (Classical.byContradiction hc)) he

end Bbu.Unit.PlannerRunU
