module

public import BbuKraken.Unit.Plan.EntryRunModel
import all BbuKraken.Unit.Plan.EntryRunModel
public import BbuKraken.Unit.Plan.EntryOutput
import all BbuKraken.Unit.Plan.EntryOutput

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

def Ran (g g' : EG) (t : MachineData) : Prop :=
  ∃ us st, model g us = (returnWord (st, g'.r.state), some (st, g'.r.state)) ∧
    Keep g g' ∧ al t = code st ∧ g'.saw = g.saw ∧
    (st = .done → g'.r.count = BitVec.ofNat 64 g'.r.state.trace.length)

theorem Keep.trans {g g' g'' : EG} (h : Keep g g') (h' : Keep g' g'') : Keep g g'' := by
  refine ⟨?_, h'.data.trans h.data, h'.ops.trans h.ops, h'.sources.trans h.sources,
    h'.count.trans h.count, h'.ids.trans h.ids, h'.idCount.trans h.idCount,
    h'.allowed.trans h.allowed, h'.strategy.trans h.strategy, h'.sawPtr.trans h.sawPtr⟩
  rw [h'.p, h.p]

theorem dropped_keep (g : EG) (d : Vector (BitVec 8) MAX_N) : Keep g (withDropped g d) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sawOut_keep (g : EG) (saw : BitVec 8) : Keep g (withSawOut g saw) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ran_of_runQ (g g' : EG) (s t : MachineData) (hok : g.Ok) (hs : Sizes g)
    (hsrc : idsFrom g.r.p.sw g.idCount 0 = true)
    (htgt : idsFrom g.r.p.tw g.idCount 0 = true)
    (ha : g.r.p.allowed = g.allowed.setWidth 8) (ht : g.r.traceLength = 0)
    (hq : RunQ (withDropped g (Flat.zeroFrom g.r.p.m 0 g.r.dropped)) g' s t)
    (hsaw : g'.saw = g.saw) : Ran g g' t := by
  obtain ⟨us, hal, hstate, hp, hd, ho, hsr, hc, hi, hcount⟩ := hq.1
  let r := Flat.plannerRun g.r.p.fl (g.strategy.setWidth 8 == 1#8)
    (withDropped g (Flat.zeroFrom g.r.p.m 0 g.r.dropped)).r.state us
  have hh : r = (r.1, g'.r.state) := Prod.ext rfl hstate.symm
  have hmodel := model_run g hok hs hsrc htgt ha ht us
  change model g us = (returnWord r, some r) at hmodel
  refine ⟨us, r.1, ?_, (dropped_keep g _).trans hq.2, ?_, hsaw, ?_⟩
  · rw [hh] at hmodel
    exact hmodel
  · exact hal
  · intro hdone
    change g'.r.count = if r.1 = .done then BitVec.ofNat 64 r.2.trace.length else g.r.count at hcount
    rw [hdone, ite_eq_left rfl] at hcount
    exact hstate.symm ▸ hcount

theorem result_done {g g' : EG} {t : MachineData} (h : Ran g g' t)
    (h1 : al t ≠ 1#8) (h2 : al t ≠ 2#8) :
    ResultWord g (withSawOut g' g'.r.p.saw) g'.r.count := by
  obtain ⟨us, st, hm, hk, hal, hsaw, hc⟩ := h
  have hst : st = .done := by cases st <;> simp_all [code, DONE, BLOCKED, ASSERTION_FAILED]
  subst st
  refine ⟨us, ?_⟩
  rw [hm]
  refine ⟨hc rfl, hk.trans (sawOut_keep g' _), rfl, ?_⟩
  rfl

theorem result_blocked {g g' : EG} {t : MachineData} (h : Ran g g' t)
    (h1 : al t = 1#8) : ResultWord g (withSawOut g' g'.r.p.saw) (-1#64) := by
  obtain ⟨us, st, hm, hk, hal, hsaw, hc⟩ := h
  have hst : st = .blocked := by cases st <;> simp_all [code, DONE, BLOCKED, ASSERTION_FAILED]
  subst st
  refine ⟨us, ?_⟩
  rw [hm]
  exact ⟨rfl, hk.trans (sawOut_keep g' _), rfl, rfl⟩

theorem result_failed {g g' : EG} {t : MachineData} (h : Ran g g' t)
    (h2 : al t = 2#8) : ResultWord g g' (-2#64) := by
  obtain ⟨us, st, hm, hk, hal, hsaw, hc⟩ := h
  have hst : st = .assertionFailed := by cases st <;> simp_all [code, DONE, BLOCKED, ASSERTION_FAILED]
  subst st
  refine ⟨us, ?_⟩
  rw [hm]
  exact ⟨rfl, hk, rfl, hsaw⟩

theorem result_rejected (g : EG) (w : Word) (h : ∀ us, model g us = (w, none)) :
    ResultWord g g w := by
  refine ⟨fun _ => ⟨⟨Vector.replicate MAX_N 0#64, Vector.replicate MAX_N 0#64⟩,
    ⟨Vector.replicate MAX_N 0#64, Vector.replicate MAX_N 0#64, 0#64, 0#64⟩,
    ⟨Vector.replicate MAX_N 0#64, Vector.replicate MAX_N 0#64, Vector.replicate MAX_N 0#64⟩,
    ⟨Vector.replicate MAX_N 0#8, Vector.replicate MAX_N 0#64⟩⟩, ?_⟩
  rw [h]
  exact ⟨rfl, rfl⟩

end Bbu.Unit.EntryValidU
