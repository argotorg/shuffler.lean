import BbuKraken.Unit.Plan.PlannerRunBlockedBasic

namespace Bbu.Unit.PlannerRunU
open Flat

theorem mapInv_of_finv {st : Flat.St} (hf : Flat.FInv st) :
    MapInv st.size st.targetSize ⟨st.dest, st.pos⟩ := by
  refine ⟨Nat.le_trans hf.size_le hf.n, hf.n, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact Or.inr (hf.dest i hi)
  · intro d hd
    exact (hf.pos d hd).imp_right And.left
  · intro i hi _
    exact hf.inv i hi
  · intro d hd hn
    exact ((hf.pos d hd).resolve_left hn).2

theorem noSurplus_of_finv {st : Flat.St} (hf : Flat.FInv st) : HasNoSurplus st := by
  intro i hi
  exact Flat.ne_none (Nat.lt_of_lt_of_le (BitVec.lt_def.mp (hf.dest i hi)) hf.n)

theorem exchange_blocked {st out : Flat.St} {top pos : Word}
    {p : Vector Word MAX_N} (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩)
    (hp : pos < st.size) (hr : Flat.exchange st top p pos = .ret (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  unfold Flat.exchange at hr
  split at hr
  · cases hr
  · split at hr
    · rename_i hu
      exact blockSwap_bounds hm.m_bound hm.destOk hp
        (by simpa only [Bool.not_eq_true'] using hu) (Flat.PNext.ret.inj hr)
    · cases hr

theorem permuteStep_blocked {st out : Flat.St} {p : Vector Word MAX_N}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩)
    (h0 : 0#64 < st.size) (hb : Bij st.size p)
    (hr : Flat.permuteStep st (st.size - 1#64) p = .ret (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  have ht : st.size - 1#64 < st.size := by bv_omega
  unfold Flat.permuteStep at hr
  dsimp only at hr
  split at hr
  · split at hr
    · cases hr
    · rename_i hn
      rcases Permute.misplacedBelow_spec p (st.size - 1#64) (st.size - 1#64) with he | ⟨hp, _⟩
      · exact False.elim (hn he)
      · exact exchange_blocked hm (by bv_omega) hr
  · exact exchange_blocked hm (hb.1 _ ht) hr

theorem permuteLoop_blocked {fuel : Nat} {st out : Flat.St} {p : Vector Word MAX_N}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (h0 : 0#64 < st.size) (hb : Bij st.size p)
    (he : Flat.permuteLoop fuel st (st.size - 1#64) p = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  induction fuel generalizing st out p with
  | zero => cases he
  | succ fuel ih =>
    rw [Flat.permuteLoop] at he
    cases hs : Flat.permuteStep st (st.size - 1#64) p with
    | ret r =>
      rw [hs] at he
      exact permuteStep_blocked hm h0 hb (by rw [hs]; exact congrArg Flat.PNext.ret he)
    | cont mid p' =>
      rw [hs] at he
      dsimp only at he
      obtain ⟨hm', hn', hsz, hnt, _, _⟩ := permuteStep_cont_safe hm hn h0 hb hs
      have hb' : Bij mid.size p' := by
        rw [hsz]
        exact (Permute.permuteStep_cont hm.m_bound h0 hb hs).1
      have h0' : 0#64 < mid.size := by rw [hsz]; exact h0
      have he' : Flat.permuteLoop fuel mid (mid.size - 1#64) p' = (.blocked, out) := by
        simpa only [hsz] using he
      simpa only [hnt] using ih hm' hn' h0' hb' he'

theorem permute_blocked {st out : Flat.St} {p : Vector Word MAX_N}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (hb : Bij st.size p) (he : Flat.permute st p = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  unfold Flat.permute at he
  split at he
  · cases he
  · rename_i h0
    dsimp only at he
    split at he
    · cases he
    · rename_i p' hp'
      exact permuteLoop_blocked hm hn (by bv_omega)
        (Permute.regroup_bij hm.m_bound hb hp') he

theorem lowest_blocked {planned : Vector Word MAX_N} {l : Flat.Locals}
    {st out : Flat.St}
    (hm : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st)
    (hlow : Flat.LowOk planned st)
    (he : Flat.permuteAtLowestHeight planned l st = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  unfold Flat.permuteAtLowestHeight at he
  split at he
  · cases he
  · rename_i sc hsc
    split at he
    · cases he
    · rename_i hc
      exact permute_blocked hm hn (hlow l sc hsc (Classical.byContradiction hc)) he

theorem permuteMapping_blocked {st out : Flat.St} (hf : Flat.FInv st)
    (heq : st.size = st.targetSize) (he : Flat.permuteMapping st = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  have hm := mapInv_of_finv hf
  have hp := hf.permOk heq
  obtain ⟨p, hr⟩ := Permute.rd_some_of_permOk hm.m_bound hp
  rw [Permute.permuteMapping_of hr] at he
  exact permute_blocked hm (noSurplus_of_finv hf) (Permute.permOk_bij hm.m_bound hp hr) he

end Bbu.Unit.PlannerRunU
