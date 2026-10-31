import BbuKraken.Unit.Plan.HasOther

/-! The intended contract of `Planner::run`.
The input condition gives sizes, buffers and valid variable IDs. Conditions on
the local mappings are established by the function, so they are not input
assumptions. Full array buffers keep the view independent of the live size. -/

namespace Bbu.Unit
open Bbu.Sep

structure PlannerRunG where
  p : PG
  dataPtr : Addr
  opsPtr : Addr
  sourcesPtr : Addr
  countPtr : Addr
  spillCount : Nat
  spills : BitVec 32 → BitVec 8
  dropped : Vector (BitVec 8) MAX_N
  data : Vector Word MAX_N
  ops : List OpR
  traceLength : Nat
  sources : Vector Word MAX_N
  count : Word

structure PlannerRunG.Ok (g : PlannerRunG) : Prop where
  planner : g.p.Ok
  spillCount : g.spillCount ≤ 2 ^ 32
  sourceIds : ∀ i ∈ splIds g.p.sw, i < g.spillCount
  targetIds : ∀ i ∈ splIds g.p.tw, i < g.spillCount
  ops : g.ops.length = 6 * g.p.n.toNat + 4 * g.p.m.toNat
  traceLength : g.traceLength ≤ g.ops.length

def PlannerRunView (P : Addr) (g : PlannerRunG) : MProp 64 :=
  PView P g.p ∗ Spl g.p.spl g.spills (List.range g.spillCount)
    ∗ Bs g.p.drp g.dropped.toList ∗ Arr g.dataPtr g.data.toList
    ∗ Ops g.opsPtr 0 g.ops ∗ Arr g.sourcesPtr g.sources.toList ∗ Wd g.countPtr g.count

def PlannerRunG.state (g : PlannerRunG) : Flat.PSt :=
  ⟨g.spills, g.dropped, g.p.saw != 0#8, g.data.map StackSlot.ofWord,
    (g.ops.take g.traceLength).map OpR.op, g.sources⟩

-- The deepest call is `Emission::run`: 4127 words of locals and saved registers,
-- its return slot, and the 4112 words of the callee.
def plannerRunD : Nat := 8240

def plannerRunA (g : PlannerRunG) (s : MachineData) : Prop :=
  rdx s = g.dataPtr ∧ rcx s = g.opsPtr ∧ r8 s = g.sourcesPtr ∧ r9 s = g.countPtr ∧
    g.traceLength = 0

def plannerRunQ (g g' : PlannerRunG) (s t : MachineData) : Prop :=
  ∃ us : Nat → Flat.RunU,
    let r := Flat.plannerRun g.p.fl ((rsi s).setWidth 8 == 1#8) g.state us
    al t = code r.1 ∧ g'.state = r.2 ∧
      g'.p = { g.p with saw := g'.p.saw } ∧ g'.dataPtr = g.dataPtr ∧
      g'.opsPtr = g.opsPtr ∧ g'.sourcesPtr = g.sourcesPtr ∧ g'.countPtr = g.countPtr ∧
      g'.spillCount = g.spillCount ∧
      g'.count = if r.1 = .done then BitVec.ofNat 64 r.2.trace.length else g.count

abbrev PlannerRunThm [Host] [FunDecls] : Prop :=
  VThm PlannerRunView PlannerRunG.Ok plannerRunAsm plannerRunA plannerRunD plannerRunQ

abbrev PlannerRunSpec [Host] [FunDecls] : Prop :=
  VSpec PlannerRunView PlannerRunG.Ok Names.plannerRun plannerRunA plannerRunD plannerRunQ

end Bbu.Unit
