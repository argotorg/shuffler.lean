module

public import BbuKraken.Unit.Plan.PlannerRunBlockedSurplus
import all BbuKraken.Unit.Plan.PlannerRunBlockedSurplus
public import BbuKraken.Unit.Plan.PlannerRunBlockedLoop
import all BbuKraken.Unit.Plan.PlannerRunBlockedLoop

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Flat

theorem finish_blocked {st out : Flat.St} (hf : RunU.checks st → FInv st)
    (hr : RunU.finish st = (.blocked, out)) : BlockedBounds st.targetSize out := by
  unfold RunU.finish at hr
  split at hr
  · cases hr
  · rename_i hsize
    split at hr
    · cases hr
    · rename_i hcnt
      split at hr
      · cases hr
      · rename_i hav
        split at hr
        · cases hr
        · rename_i hlab
          apply buildBottomUp_blocked (hf ?_) hr
          exact ⟨Classical.byContradiction hsize, Classical.byContradiction hcnt,
            (by simpa only [Bool.not_eq_true', Bool.not_eq_false] using hav),
            (by simpa only [Bool.not_eq_true', Bool.not_eq_false] using hlab)⟩

theorem prep_emission_blocked {planned : Vector Word MAX_N} {m : Nat}
    {st out : Flat.St} (h : Prep planned m st) (hs : RunU.Safe planned st (4 * m))
    (l : Flat.Locals) (he : Flat.emissionRun planned l st = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  by_cases hd : (Flat.removeSurplus st).1 = .done
  · have hr : Flat.removeSurplus st = (.done, (Flat.removeSurplus st).2) := Prod.ext hd rfl
    rw [RunU.emission_lowest hr] at he
    obtain ⟨ha, hn⟩ := h.removeSurplus hd
    have ht := removeSurplus_target st
    have hlo := lowOk_of_map ha.map hn ha.support
    split at he
    · have hb := lowest_blocked ha.map hn hlo he
      simpa only [ht] using hb
    · rename_i hl
      have hld : (Flat.permuteAtLowestHeight planned l (Flat.removeSurplus st).2).1 = .done :=
        Classical.byContradiction hl
      have hb := finish_blocked (fun hc => (hs.loop l hd hld hc).f) he
      have hle : Flat.permuteAtLowestHeight planned l (Flat.removeSurplus st).2 =
          (.done, (Flat.permuteAtLowestHeight planned l (Flat.removeSurplus st).2).2) :=
        Prod.ext hld rfl
      have htarget := (lowest_preserves ha.map hn hlo hle).2.2.2.1
      simpa only [htarget, ht] using hb
  · rw [RunU.emission_surplus_fail hd] at he
    exact h.removeSurplus_blocked he

theorem ctorP_emission_blocked {m n : Word} {M : Flat.Mapping} (h : MapInv m n M)
    (data target : Vector StackSlot MAX_N) (spills : BitVec 32 → BitVec 8)
    (u : Flat.Uninit) (l : Flat.Locals) {out : Flat.St}
    (he : Flat.emissionRun M.pos l (Flat.ctorP data m target n M spills u) = (.blocked, out)) :
    BlockedBounds n out := by
  have hb := prep_emission_blocked (Prep.ctorP h data target spills u)
    (ctorP_safe h data target spills u) l he
  simpa only [Flat.ctorP, Flat.pend_fold] using hb

end Bbu.Unit.PlannerRunU
