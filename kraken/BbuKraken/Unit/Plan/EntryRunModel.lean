import BbuKraken.Unit.Plan.EntryCallDefs

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

def returnWord (r : Flat.Status × Flat.PSt) : Word :=
  match r.1 with
  | .done => BitVec.ofNat 64 r.2.trace.length
  | .blocked => -1#64
  | .assertionFailed => -2#64

theorem allowed_bool (g : EG) (hs : Sizes g)
    (ha : g.r.p.allowed = g.allowed.setWidth 8) :
    (g.r.p.allowed != 0#8) = decide (g.allowed.setWidth 8 = 1#8) := by
  rw [ha]
  have hh : (g.allowed.setWidth 8).toNat ≤ 1 := by
    unfold Sizes EntryU.BadArgs at hs
    omega
  generalize g.allowed.setWidth 8 = a at *
  change a ≤ 1#8 at hh
  bv_decide

theorem model_run (g : EG) (hok : g.Ok) (hs : Sizes g)
    (hsrc : idsFrom g.r.p.sw g.idCount 0 = true)
    (htgt : idsFrom g.r.p.tw g.idCount 0 = true)
    (ha : g.r.p.allowed = g.allowed.setWidth 8) (ht : g.r.traceLength = 0)
    (us : Nat → Flat.RunU) :
    let d := Flat.zeroFrom g.r.p.m 0 g.r.dropped
    let r := Flat.plannerRun g.r.p.fl (g.strategy.setWidth 8 == 1#8)
      (withDropped g d).r.state us
    model g us = (returnWord r, some r) := by
  have hsrc' : ((Flat.offsets g.r.p.m).all fun i =>
      Flat.idOk g.idCount (Flat.get g.r.p.fl.source i)) = true := by
    exact (ids_model g.r.p.sw g.idCount g.r.p.m hok.sw (sizes_m hs)).trans hsrc
  have htgt' : ((Flat.offsets g.r.p.n).all fun i =>
      Flat.idOk g.idCount (Flat.get g.r.p.fl.target i)) = true := by
    exact (ids_model g.r.p.tw g.idCount g.r.p.n hok.tw (sizes_n hs)).trans htgt
  dsimp only
  unfold model Flat.planEntry
  rw [ite_eq_right (sizes_guard hs)]
  simp only [hsrc', htgt', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  let r := Flat.plannerRun g.r.p.fl (g.strategy.setWidth 8 == 1#8)
    (withDropped g (Flat.zeroFrom g.r.p.m 0 g.r.dropped)).r.state us
  have hr : Flat.plannerRun
      ⟨g.r.p.fl.source, g.r.p.m, g.r.p.fl.target, g.r.p.n,
        decide (g.allowed.setWidth 8 = 1)⟩
      (decide (g.strategy.setWidth 8 = 1))
      ⟨g.r.spills, Flat.zeroFrom g.r.p.m 0 g.r.dropped, false,
        g.r.data.map StackSlot.ofWord, [], g.r.sources⟩ us = r := by
    dsimp only [r, PG.fl, PlannerRunG.state, withDropped]
    simp only [BitVec.ofNat_eq_ofNat, allowed_bool g hs ha, Bool.beq_eq_decide_eq, ht, List.take_zero,
      List.map_nil, Flat.plannerRun]
  simp only [BitVec.ofNat_eq_ofNat] at hr ⊢
  rw [hr]
  change (match r.1 with
    | .done => (BitVec.ofNat 64 r.2.trace.length, some r)
    | .blocked => (-1#64, some r)
    | .assertionFailed => (-2#64, some r)) = (returnWord r, some r)
  cases hr : r.1 <;> simp only [returnWord, hr]

end Bbu.Unit.EntryValidU
