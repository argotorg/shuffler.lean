import BbuKraken.Unit.Plan.PlannerRunAttemptContext
import BbuKraken.Unit.Plan.PlannerRunRetryDefs

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def readDropped (p : Addr) (m : Mem 64) : Vector (BitVec 8) MAX_N :=
  Vector.ofFn fun i => rdb m (p + BitVec.ofNat 64 i.val)

theorem droppedFrom_congr (m : Word) (a b : Vector (BitVec 8) MAX_N)
    (h : ∀ i, i < m → Flat.get a i = Flat.get b i) (i c : Word) :
    Flat.droppedFrom m a i c = Flat.droppedFrom m b i c := by
  conv => lhs; rw [Flat.droppedFrom]
  conv => rhs; rw [Flat.droppedFrom]
  split
  · rename_i hi
    rw [h i hi]
    exact droppedFrom_congr m a b h (i + 1) _
  · rfl
termination_by (m - i).toNat
decreasing_by exact Flat.sub_succ_lt ‹i < m›

-- Only the first m bytes are owned. Their count does not depend on the unowned tail.
theorem readDropped_eq {P : Addr} {g : PlannerRunG} {F : MProp 64} {t : MachineData}
    (h : (PlannerRunView P g ∗ F).get t.dmem) :
    Flat.droppedCount g.p.m (readDropped g.p.drp t.dmem) =
      Flat.droppedCount g.p.m g.dropped := by
  apply droppedFrom_congr
  intro i hi
  by_cases hiN : i.toNat < MAX_N
  · obtain ⟨R, hb⟩ := dropped_read h hiN (BitVec.lt_def.mp hi)
    have hr := B8.rdb hb
    simpa only [readDropped, Flat.get, dite_eq_left hiN,
      Vector.getElem_ofFn, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr
  · simp only [Flat.get, dite_eq_right hiN]

def dropBudget (g : PlannerRunG) (t : MachineData) : Nat :=
  (g.p.m - Flat.droppedCount g.p.m (readDropped g.p.drp t.dmem)).toNat

theorem dropBudget_eq {initial current : PlannerRunG} {P : Addr} {F : MProp 64}
    {t : MachineData} (hm : RunMeta initial current)
    (h : (PlannerRunView P current ∗ F).get t.dmem) :
    dropBudget initial t = (current.p.m - Flat.droppedCount current.p.m current.dropped).toNat := by
  have hsize := congrArg PG.m hm.planner
  have hdrp := congrArg PG.drp hm.planner
  change current.p.m = initial.p.m at hsize
  change current.p.drp = initial.p.drp at hdrp
  unfold dropBudget
  rw [← hsize, ← hdrp, readDropped_eq h]

def indexAt (base : Addr) (t : MachineData) : Nat := (rax t - base).toNat / 8

def runV (g : PlannerRunG) (l : Label) (t : MachineData) : Nat :=
  let m := g.p.m.toNat
  let n := g.p.n.toNat
  let b := dropBudget g t * 65536
  if l = ".LB.Planner.run.26" then 0
  else if l = ".LB.Planner.run.19" ∨ l = ".LB.Planner.run.20" ∨
      l = ".LB.Planner.run.21" ∨ l = ".LB.Planner.run.22" ∨
      l = ".LB.Planner.run.23" ∨ l = ".LB.Planner.run.24" ∨
      l = ".LB.Planner.run.25" then 1
  else if l = ".LB.Planner.run.18" then 1000
  else if l = ".LB.Planner.run.17" then 2000 + (n - (rdx t).toNat)
  else if l = ".LB.Planner.run.16" then 3500
  else if l = ".LB.Planner.run.31" then
    (g.p.m - t.regs.rbp.toBitVec).toNat * 65536 + 4096 +
      (m - (rax t - g.p.drp).toNat)
  else if l = ".LB.Planner.run.30" then b + 8000
  else if l = ".LB.Planner.run.29" then b + 12000 + (m - (rax t - g.p.drp).toNat)
  else if l = ".LB.Planner.run.28" then b + 16000
  else if l = ".LB.Planner.run.14" then
    b + 20000 + 2 * (n - indexAt (t.regs.rsp.toBitVec + 16480#64) t)
  else if l = ".LB.Planner.run.15" then
    b + 20000 + 2 * (n - indexAt (t.regs.rsp.toBitVec + 16480#64) t) + 1
  else if l = ".LB.Planner.run.27" then b + 24000
  else if l = ".LB.Planner.run.13" then b + 28000 + (n - indexAt 0#64 t)
  else if l = ".LB.Planner.run.12" then b + 32000
  else if l = ".LB.Planner.run.11" then b + 34000 + (m - (rax t).toNat)
  else if l = ".LB.Planner.run.10" then b + 38000 + (m - (rax t).toNat)
  else if l = ".LB.Planner.run.32" then b + 42000
  else if l = ".LB.Planner.run.9" then b + 44000
  else if l = ".LB.Planner.run.8" then
    b + 48000 + (n - indexAt (t.regs.rsp.toBitVec + 96#64) t)
  else if l = ".LB.Planner.run.7" then b + 52000
  else if l = ".LB.Planner.run.6" then b + 56000 + (m - (rax t).toNat)
  else if l = ".LB.Planner.run.5" then b + 60000
  else if l = ".LB.Planner.run.4" then (m + 1) * 65536
  else
    let check := (m + 1) * 65536 + (n - (rcx t).toNat) * (m + 4)
    if l = ".LB.Planner.run.0" then check
    else if l = ".LB.Planner.run.1" then check + m + 3
    else if l = ".LB.Planner.run.2" then check + (m - (rax t).toNat) + 2
    else if l = ".LB.Planner.run.3" then check + 1
    else (m + 1) * 65536 + (n + 1) * (m + 4)

attribute [local simp] runV

end Bbu.Unit.PlannerRunU
