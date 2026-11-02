module

public import FlatShuffler.Unit.Plan.HasOther
import all FlatShuffler.Unit.Plan.HasOther
public import FlatShuffler.Unit.Plan.ExitDefs
import all FlatShuffler.Unit.Plan.ExitDefs

@[expose] public section

/-! The intended contract of `Planner::run`.
The input condition gives sizes, buffers and valid variable IDs. Conditions on
the local mappings are established by the function, so they are not input
assumptions. The memory view owns only the input-sized buffers. -/

namespace FlatShuffler.Unit
open FlatShuffler.Sep

-- The deepest call is `Emission::run`: 4127 words of locals and saved registers,
-- its return slot, and the 4112 words of the callee.
def plannerRunD : Nat := 8240

def plannerRunA (g : PlannerCallMemory) (s : MachineData) : Prop :=
  rdx s = g.dataPtr ∧ rcx s = g.opsPtr ∧ r8 s = g.sourcesPtr ∧ r9 s = g.countPtr ∧
    g.traceLength = 0

def plannerRunQ (g g' : PlannerCallMemory) (s t : MachineData) : Prop :=
  ∃ us : Nat → Flat.RunU,
    let r := Flat.plannerRun g.p.fl ((rsi s).setWidth 8 == 1#8) g.state us
    al t = code r.1 ∧ g'.state = r.2 ∧
      g'.p = { g.p with saw := g'.p.saw } ∧ g'.dataPtr = g.dataPtr ∧
      g'.opsPtr = g.opsPtr ∧ g'.sourcesPtr = g.sourcesPtr ∧ g'.countPtr = g.countPtr ∧
      g'.spillCount = g.spillCount ∧
      g'.count = if r.1 = .done then BitVec.ofNat 64 r.2.trace.length else g.count

def plannerRunX (g g' : PlannerCallMemory) (s _t : MachineData) : Prop :=
  ∃ us : Nat → Flat.RunU,
    let r := Flat.plannerRun g.p.fl ((rsi s).setWidth 8 == 1#8) g.state us
    r.1 = .assertionFailed ∧ g'.state = r.2 ∧
      g'.p = { g.p with saw := g'.p.saw } ∧ g'.dataPtr = g.dataPtr ∧
      g'.opsPtr = g.opsPtr ∧ g'.sourcesPtr = g.sourcesPtr ∧ g'.countPtr = g.countPtr ∧
      g'.spillCount = g.spillCount ∧ g'.count = g.count

def plannerRunNormalReturn (g g' : PlannerCallMemory) (s t : MachineData) : Prop :=
  plannerRunQ g g' s t ∧ al t ≠ ASSERTION_FAILED

theorem plannerRunX_of_Q {g g' : PlannerCallMemory} {s t u : MachineData}
    (h : plannerRunQ g g' s t) (ha : al t = 2#8) : plannerRunX g g' s u := by
  obtain ⟨us, hcode, hstate, hp, hd, ho, hs, hc, hsp, hn⟩ := h
  have hr : (Flat.plannerRun g.p.fl ((rsi s).setWidth 8 == 1#8) g.state us).1 =
      .assertionFailed := by
    have hstatus : ∀ a : Flat.Status, 2#8 = code a → a = .assertionFailed := by
      intro a he
      cases a <;> simp [code, DONE, BLOCKED, ASSERTION_FAILED] at he ⊢
    exact hstatus _ (ha.symm.trans hcode)
  exact ⟨us, hr, hstate, hp, hd, ho, hs, hc, hsp,
    by simpa only [hr, reduceCtorEq, ↓reduceIte] using hn⟩

abbrev PlannerRunThm [Host] [FunDecls] : Prop :=
  VThmWithExit plannerCallOwnedMemory PlannerCallMemory.Ok plannerRunAsm plannerRunA plannerRunD
    plannerRunNormalReturn plannerRunX

abbrev PlannerRunSpec [Host] [FunDecls] : Prop :=
  VSpecWithExit plannerCallOwnedMemory PlannerCallMemory.Ok Names.plannerRun plannerRunA plannerRunD
    plannerRunNormalReturn plannerRunX

end FlatShuffler.Unit
