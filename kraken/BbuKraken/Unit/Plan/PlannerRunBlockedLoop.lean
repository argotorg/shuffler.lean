module

public import BbuKraken.Unit.Plan.PlannerRunBlockedBasic
import all BbuKraken.Unit.Plan.PlannerRunBlockedBasic
public import BbuKraken.Unit.Plan.PlannerRunBlockedProduce
import all BbuKraken.Unit.Plan.PlannerRunBlockedProduce
public import BbuKraken.Unit.Plan.PlannerRunBlockedPermute
import all BbuKraken.Unit.Plan.PlannerRunBlockedPermute
public import BbuKraken.Unit.Loop.Cont
import all BbuKraken.Unit.Loop.Cont
public import BbuKraken.Unit.Loop.Step
import all BbuKraken.Unit.Loop.Step
public import BbuKraken.FlatSurplusRel
import all BbuKraken.FlatSurplusRel

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Flat

theorem urgentFrom_blocked {st out : Flat.St} (hf : FInv st) (t o u : Word)
    (hr : Flat.urgentFrom st t o u = .error (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  fun_induction Flat.urgentFrom st t o u with
  | case1 o u ho hp ih => exact ih hr
  | case2 o u ho hp slot hfree ih => exact ih hr
  | case3 o u ho hp slot hfree source hn hu =>
    apply blockDup_bounds (Nat.le_trans hf.size_le hf.n) hf.destOk
      (shallowestCopy_lt hn) (by simpa only [Bool.not_eq_true'] using hu)
    exact Except.error.inj hr
  | case4 o u ho hp slot hfree source hn hu ih => exact ih hr
  | case5 o u ho hp slot hfree source hn ih => exact ih hr
  | case6 o u ho => cases hr

theorem candidateFrom_lt {st : Flat.St} {slot : StackSlot} {source candidate : Word}
    (hs : source < st.size) (hc : candidate < st.size) :
    Flat.candidateFrom st slot source candidate < st.size := by
  revert hc
  fun_induction Flat.candidateFrom st slot source candidate with
  | case1 candidate hgt he => intro hc; exact hc
  | case2 candidate hgt he ih =>
    intro hc
    apply ih
    bv_omega
  | case3 candidate hgt => intro _; exact hs

theorem placeTop_finv_cont {st st' : Flat.St} {t t' : Word}
    (hf : FInv st) (hr : Flat.placeTop st t = .cont st' t') : FInv st' := by
  unfold Flat.placeTop at hr
  dsimp only at hr
  split at hr
  · cases hr
  split at hr
  · cases hr
  split at hr
  · split at hr
    · cases hr
    · split at hr
      · cases hr
      · cases hr
        rename_i hd
        exact (hf.swapWith (Decidable.not_not.mp hd)).1
  · cases hr
    exact hf

theorem placeTop_blocked {st out : Flat.St} {t : Word}
    (hf : FInv st) (hr : Flat.placeTop st t = .ret (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  unfold Flat.placeTop at hr
  dsimp only at hr
  split at hr
  · cases hr
  rename_i ht
  split at hr
  · cases hr
  split at hr
  · split at hr
    · rename_i hu
      exact blockSwap_bounds (Nat.le_trans hf.size_le hf.n) hf.destOk
        (Decidable.not_not.mp ht) (by simpa only [Bool.not_eq_true'] using hu)
        (Flat.Next.ret.inj hr)
    · split at hr
      · have he := congrArg (fun q => match q with | .ret r => r.1 | _ => .done) hr
        exact False.elim (Flat.swapWith_status st t he)
      · cases hr
  · cases hr

theorem bound_pos_lt {st : Flat.St} {t : Word} (hf : FInv st)
    (ht : t < st.targetSize) (hn : get st.pos t ≠ NONE) : get st.pos t < st.size :=
  ((hf.pos t ht).resolve_left hn).1

theorem bound_candidate_lt {st : Flat.St} {t : Word} (hf : FInv st)
    (ht : t < st.targetSize) (hp : get st.pos t ≠ NONE ∧ get st.pos t ≥ t) :
    (if get st.data t = get st.data (get st.pos t) then t
      else Flat.candidateFrom st (get st.data (get st.pos t)) (get st.pos t) (st.size - 1))
        < st.size := by
  have hb := bound_pos_lt hf ht hp.1
  split
  · bv_omega
  · apply candidateFrom_lt hb
    bv_omega

theorem bound_finv_cont {st st' : Flat.St} {t t' : Word}
    (hf : FInv st) (ht : t < st.targetSize)
    (hr : Flat.bound st t = .cont st' t') : FInv st' := by
  rw [Flat.bound_eq] at hr
  by_cases hp : get st.pos t ≠ NONE ∧ get st.pos t ≥ t
  case neg => rw [ite_eq_left hp] at hr; cases hr
  rw [ite_eq_right (Decidable.not_not.mpr hp)] at hr
  let p := if get st.data t = get st.data (get st.pos t) then t
    else Flat.candidateFrom st (get st.data (get st.pos t)) (get st.pos t) (st.size - 1)
  have hb := bound_pos_lt hf ht hp.1
  have hc : p < st.size := bound_candidate_lt hf ht hp
  change Flat.kB st t (get st.pos t) p = .cont st' t' at hr
  unfold Flat.kB at hr
  by_cases hd : get st.data p ≠ get st.data (get st.pos t)
  · rw [ite_eq_left hd] at hr; cases hr
  rw [ite_eq_right hd] at hr
  let a := Flat.swapDestinations st p (get st.pos t)
  have hs : FInv a := hf.swapDestinations hc hb
  change Flat.kBoundSw a t p = .cont st' t' at hr
  unfold Flat.kBoundSw at hr
  by_cases hpt : p = t
  · rw [ite_eq_left hpt] at hr
    exact (Flat.Next.cont.inj hr).1 ▸ hs
  rw [ite_eq_right hpt] at hr
  by_cases htop : p ≠ a.size - 1
  · rw [ite_eq_left htop] at hr
    by_cases hu : (!Flat.isSwapReachable a p) = true
    · rw [ite_eq_left hu] at hr; cases hr
    rw [ite_eq_right hu] at hr
    dsimp only at hr
    by_cases hdone : (Flat.swapWith a p).1 ≠ .done
    · rw [ite_eq_left hdone] at hr; cases hr
    rw [ite_eq_right hdone] at hr
    exact placeTop_finv_cont (hs.swapWith (Decidable.not_not.mp hdone)).1 hr
  · rw [ite_eq_right htop] at hr
    exact placeTop_finv_cont hs hr

theorem bound_blocked {st out : Flat.St} {t : Word}
    (hf : FInv st) (ht : t < st.targetSize)
    (hr : Flat.bound st t = .ret (.blocked, out)) : BlockedBounds st.targetSize out := by
  rw [Flat.bound_eq] at hr
  by_cases hp : get st.pos t ≠ NONE ∧ get st.pos t ≥ t
  case neg => rw [ite_eq_left hp] at hr; cases hr
  rw [ite_eq_right (Decidable.not_not.mpr hp)] at hr
  let p := if get st.data t = get st.data (get st.pos t) then t
    else Flat.candidateFrom st (get st.data (get st.pos t)) (get st.pos t) (st.size - 1)
  have hb := bound_pos_lt hf ht hp.1
  have hc : p < st.size := bound_candidate_lt hf ht hp
  change Flat.kB st t (get st.pos t) p = .ret (.blocked, out) at hr
  unfold Flat.kB at hr
  by_cases hd : get st.data p ≠ get st.data (get st.pos t)
  · rw [ite_eq_left hd] at hr; cases hr
  rw [ite_eq_right hd] at hr
  let a := Flat.swapDestinations st p (get st.pos t)
  have hs : FInv a := hf.swapDestinations hc hb
  change BlockedBounds a.targetSize out
  change Flat.kBoundSw a t p = .ret (.blocked, out) at hr
  unfold Flat.kBoundSw at hr
  by_cases hpt : p = t
  · rw [ite_eq_left hpt] at hr; cases hr
  rw [ite_eq_right hpt] at hr
  by_cases htop : p ≠ a.size - 1
  · rw [ite_eq_left htop] at hr
    by_cases hu : (!Flat.isSwapReachable a p) = true
    · rw [ite_eq_left hu] at hr
      exact blockSwap_bounds (Nat.le_trans hs.size_le hs.n) hs.destOk hc
        (by simpa only [Bool.not_eq_true'] using hu) (Flat.Next.ret.inj hr)
    rw [ite_eq_right hu] at hr
    dsimp only at hr
    by_cases hdone : (Flat.swapWith a p).1 ≠ .done
    · rw [ite_eq_left hdone] at hr
      have he := congrArg (fun q => match q with | .ret r => r.1 | _ => .done) hr
      exact False.elim (Flat.swapWith_status _ _ he)
    rw [ite_eq_right hdone] at hr
    have hs' := (hs.swapWith (Decidable.not_not.mp hdone)).1
    have hr' := placeTop_blocked hs' hr
    simpa only [Flat.swapWith_tsize] using hr'
  · rw [ite_eq_right htop] at hr
    exact placeTop_blocked hs hr

theorem kGenAt_finv_cont {st st' : Flat.St} {t u t' : Word}
    (hf : FInv st) (hp : st.pend ≠ 0#64)
    (hr : Flat.kGenAt st t u = .cont st' t') : FInv st' := by
  unfold Flat.kGenAt at hr
  dsimp only at hr
  split at hr
  · cases hr
  rename_i hd
  have hs := (hf.generate hp (Decidable.not_not.mp hd)).1
  exact (Flat.Next.cont.inj hr).1 ▸ hs

theorem kGenAt_blocked {st out : Flat.St} {t u : Word}
    (hf : FInv st) (hr : Flat.kGenAt st t u = .ret (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  unfold Flat.kGenAt at hr
  dsimp only at hr
  split at hr
  · exact generate_blocked hf (Flat.Next.ret.inj hr)
  · cases hr

theorem kGenT_finv_cont {st st' : Flat.St} {t t' : Word}
    (hf : FInv st) (hp : st.pend ≠ 0#64)
    (hr : Flat.kGenT st t = .cont st' t') : FInv st' := by
  unfold Flat.kGenT at hr
  dsimp only at hr
  split at hr
  · cases hr
  rename_i hd
  have hs := (hf.generate hp (Decidable.not_not.mp hd)).1
  split at hr
  · cases hr
  split at hr
  · exact (Flat.Next.cont.inj hr).1 ▸ hs
  · exact placeTop_finv_cont hs hr

theorem kGenT_blocked {st out : Flat.St} {t : Word}
    (hf : FInv st) (hp : st.pend ≠ 0#64)
    (hr : Flat.kGenT st t = .ret (.blocked, out)) : BlockedBounds st.targetSize out := by
  unfold Flat.kGenT at hr
  dsimp only at hr
  split at hr
  · exact generate_blocked hf (Flat.Next.ret.inj hr)
  rename_i hd
  have hdone := Decidable.not_not.mp hd
  have hs := (hf.generate hp hdone).1
  split at hr
  · cases hr
  split at hr
  · cases hr
  · have hout := placeTop_blocked hs hr
    rw [(Flat.generate_done hdone).1] at hout
    exact hout

theorem kU_finv_cont {st st' : Flat.St} {t u t' : Word}
    (hf : FInv st) (hp : st.pend ≠ 0#64) (ht : t < st.targetSize)
    (hr : Flat.kU st t u = .cont st' t') : FInv st' := by
  unfold Flat.kU at hr
  split at hr
  · exact kGenAt_finv_cont hf hp hr
  unfold Flat.kU2 at hr
  split at hr
  · exact kGenAt_finv_cont hf hp hr
  unfold Flat.kU3 at hr
  split at hr
  · exact bound_finv_cont hf ht hr
  · exact kGenT_finv_cont hf hp hr

theorem kU_blocked {st out : Flat.St} {t u : Word}
    (hf : FInv st) (hp : st.pend ≠ 0#64) (ht : t < st.targetSize)
    (hr : Flat.kU st t u = .ret (.blocked, out)) : BlockedBounds st.targetSize out := by
  unfold Flat.kU at hr
  split at hr
  · exact kGenAt_blocked hf hr
  unfold Flat.kU2 at hr
  split at hr
  · exact kGenAt_blocked hf hr
  unfold Flat.kU3 at hr
  split at hr
  · exact bound_blocked hf ht hr
  · exact kGenT_blocked hf hp hr

theorem body_finv_cont {st st' : Flat.St} {t t' : Word}
    (hf : FInv st) (ht : t < st.targetSize)
    (hr : Flat.body st t = .cont st' t') : FInv st' := by
  rw [Flat.body_eq] at hr
  split at hr
  · exact (Flat.Next.cont.inj hr).1 ▸ hf
  unfold Flat.kPend at hr
  split at hr
  · split at hr <;> cases hr
  rename_i hp
  cases he : Flat.urgentFrom st t t NONE with
  | error r => rw [he] at hr; cases hr
  | ok u =>
    rw [he] at hr
    exact kU_finv_cont hf hp ht hr

theorem body_blocked {st out : Flat.St} {t : Word}
    (hf : FInv st) (ht : t < st.targetSize)
    (hr : Flat.body st t = .ret (.blocked, out)) : BlockedBounds st.targetSize out := by
  rw [Flat.body_eq] at hr
  split at hr
  · cases hr
  unfold Flat.kPend at hr
  split at hr
  · split at hr
    · cases hr
    · rename_i heq
      exact permuteMapping_blocked hf (Decidable.not_not.mp heq) (Flat.Next.ret.inj hr)
  rename_i hp
  cases he : Flat.urgentFrom st t t NONE with
  | error r =>
    rw [he] at hr
    have hret := Flat.Next.ret.inj hr
    rw [hret] at he
    exact urgentFrom_blocked hf t t NONE he
  | ok u =>
    rw [he] at hr
    exact kU_blocked hf hp ht hr

theorem loop_blocked {st out : Flat.St} (hf : FInv st) (t : Word)
    (hr : Flat.loop st t = (.blocked, out)) : BlockedBounds st.targetSize out := by
  fun_induction Flat.loop st t with
  | case1 st t ht r he =>
    rw [hr] at he
    exact body_blocked hf ht he
  | case2 st t ht st' t' he ih =>
    have hs := body_finv_cont hf ht he
    have hout := ih hs hr
    rw [(Flat.body_cont he).1] at hout
    exact hout
  | case3 st t ht hs => cases hr
  | case4 st t ht hs => cases hr

theorem buildBottomUp_blocked {st out : Flat.St} (hf : FInv st)
    (hr : Flat.buildBottomUp st = (.blocked, out)) : BlockedBounds st.targetSize out :=
  loop_blocked hf 0#64 hr

end Bbu.Unit.PlannerRunU
