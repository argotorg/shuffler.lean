module

public import BbuKraken.Unit.Plan.ResolveLoopDefs
import all BbuKraken.Unit.Plan.ResolveLoopDefs

@[expose] public section

namespace Bbu.Unit.ResolveU

theorem Work.modelQ {w : Work} {r : RG} {s : MachineData} {st : Flat.Resolution}
    (hm : w.Model r s) (hq : w.result r s = (st, w.spills, w.dropped)) :
    modelQ r (w.ghost r) s st := by
  intro u
  have he := hm u
  rw [hq] at he
  rw [he]
  exact ⟨rfl, rfl⟩

theorem Work.empty {w : Work} {r : RG} {s : MachineData}
    (hok : w.Ok r s) (hm : w.Model r s) (hc : w.count = 0#64) :
    ResolveU.modelQ r (w.ghost r) s .stuck := by
  apply Work.modelQ hm
  rw [Work.result, hc, pass_empty hok.pass]
  rfl

theorem Work.no_best {w : Work} {r : RG} {s : MachineData}
    (hok : w.Ok r s) (hm : w.Model r s) (hb : (w.pick r).1 = Flat.NONE) :
    ResolveU.modelQ r (w.ghost r) s .stuck := by
  apply Work.modelQ hm
  rw [Work.result, pass_stuck hok.pass hb]
  rfl

def Work.drop (w : Work) (best : Word) : Work :=
  { w with
    dropped := Flat.put w.dropped best 1
    droppedNow := Flat.put w.droppedNow best 1
    pass := w.pass + 1 }

theorem Work.drop_model {w : Work} {r : RG} {s : MachineData}
    (hok : w.Ok r s) (hm : w.Model r s)
    (hb : (w.pick r).1 ≠ Flat.NONE) (hc : (w.pick r).2 ≠ Flat.SPILL) :
    (w.drop (w.pick r).1).Model r s := by
  intro u
  rw [hm u, Work.result, pass_drop hok.pass hb hc]
  rfl

theorem Work.spill_model {w : Work} {r : RG} {s : MachineData}
    (hok : w.Ok r s) (hm : w.Model r s)
    (hb : (w.pick r).1 ≠ Flat.NONE) (hc : (w.pick r).2 = Flat.SPILL)
    (ha : (Flat.spillAdd w.spills (Flat.get r.p.fl.source (w.pick r).1)).1 = .done) :
    ({ w with spills := (Flat.spillAdd w.spills
      (Flat.get r.p.fl.source (w.pick r).1)).2 }.drop (w.pick r).1).Model r s := by
  intro u
  rw [hm u, Work.result, pass_spill hok.pass hb hc ha]
  rfl

theorem Work.spill_fail {w : Work} {r : RG} {s : MachineData}
    (hok : w.Ok r s) (hm : w.Model r s)
    (hb : (w.pick r).1 ≠ Flat.NONE) (hc : (w.pick r).2 = Flat.SPILL)
    (ha : (Flat.spillAdd w.spills (Flat.get r.p.fl.source (w.pick r).1)).1 ≠ .done) :
    ResolveU.modelQ r (w.ghost r) s .assertionFailed := by
  apply Work.modelQ hm
  rw [Work.result, pass_fail hok.pass hb hc ha]
  rfl

end Bbu.Unit.ResolveU
