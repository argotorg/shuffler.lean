import BbuKraken.Unit.Plan.PlannerRunContext
import BbuKraken.Unit.Plan.PlannerRunStepModel
import BbuKraken.Unit.Plan.PlannerRunBuilder
import BbuKraken.Unit.Plan.PlannerRunEmissionReady
import BbuKraken.Unit.Plan.PlannerRunEmissionPost
import BbuKraken.Unit.Plan.PlannerRunEmissionData

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem mergeSaw_bool (old saw : BitVec 8) :
    (mergeSaw old saw != 0#8) = ((old != 0#8) || (saw != 0#8)) := by
  by_cases h : old = 0#8 <;> simp [mergeSaw, h]

theorem RunMeta.withData {initial current : PlannerRunG} (h : RunMeta initial current)
    (data : Vector Word MAX_N) : RunMeta initial {current with data := data} :=
  ⟨h.planner, h.dataPtr, h.opsPtr, h.sourcesPtr, h.countPtr, h.spillCount⟩

theorem RunMeta.withSources {initial current : PlannerRunG} (h : RunMeta initial current)
    (sources : Vector Word MAX_N) : RunMeta initial {current with sources := sources} :=
  ⟨h.planner, h.dataPtr, h.opsPtr, h.sourcesPtr, h.countPtr, h.spillCount⟩

theorem RunMeta.withCount {initial current : PlannerRunG} (h : RunMeta initial current)
    (count : Word) : RunMeta initial {current with count := count} :=
  ⟨h.planner, h.dataPtr, h.opsPtr, h.sourcesPtr, h.countPtr, h.spillCount⟩

/-- Model information kept while one attempt copies its data and creates the emission. -/
structure AttemptContext (initial current : PlannerRunG) (s : MachineData)
    (M : Flat.Mapping) where
  before : PlannerRunG
  loop : LoopContext initial before s
  mapping : Flat.Mapping
  saw : Bool
  init : mapping.init before.p.m before.p.n = mapping
  build : Flat.buildMapping
    ⟨before.p.fl.source, before.p.m, before.p.fl.target, before.p.n, before.dropped,
      (rsi s).setWidth 8 == 1#8⟩ mapping = some (M, saw)
  stable : RunMeta initial current
  planner : current.p.fl = before.p.fl
  state : current.state =
    {buildState before.p.fl before.state saw with data := current.state.data}
  count : current.count = initial.count
  map : MapInv current.p.m current.p.n M
  targets : Flat.targetsFrom current.p.fl current.spills 0 = true
  ok : current.Ok

namespace AttemptContext

def ofBuild {initial current : PlannerRunG} {s : MachineData}
    (ctx : LoopContext initial current s) (hok : current.Ok)
    (M0 M : Flat.Mapping) (saw : BitVec 8)
    (hm : MapInv current.p.m current.p.n M)
    (hi : M0.init current.p.m current.p.n = M0)
    (hb : Flat.buildMapping (plannerBuilder current s M0 0#8).fl M0 =
      some (M, saw != 0#8))
    (ht : Flat.targetsFrom current.p.fl current.spills 0 = true) :
    AttemptContext initial (withSaw current (mergeSaw current.p.saw saw)) s M where
  before := current
  loop := ctx
  mapping := M0
  saw := saw != 0#8
  init := hi
  build := (builderGhost_buildMapping current hok _ _ _ M0).symm.trans hb
  stable := ctx.stable.withSaw _
  planner := rfl
  state := by
    simp only [PlannerRunG.state, withSaw, buildState, mergeSaw_bool]
  count := ctx.count
  map := hm
  targets := ht
  ok := withSaw_ok hok _

def withData {initial current : PlannerRunG} {s : MachineData} {M : Flat.Mapping}
    (h : AttemptContext initial current s M) (data : Vector Word MAX_N) :
    AttemptContext initial {current with data := data} s M where
  before := h.before
  loop := h.loop
  mapping := h.mapping
  saw := h.saw
  init := h.init
  build := h.build
  stable := h.stable.withData data
  planner := h.planner
  state := by
    have he := congrArg (fun q : Flat.PSt => {q with data := data.map StackSlot.ofWord}) h.state
    exact he
  count := h.count
  map := h.map
  targets := h.targets
  ok := data_ok h.ok data

def wanted {initial current : PlannerRunG} {s : MachineData} {M : Flat.Mapping}
    (h : AttemptContext initial current s M) : Vector StackSlot MAX_N :=
  Flat.copyFrom h.before.p.fl 0 h.before.state.data

theorem copiedState {initial current : PlannerRunG} {s : MachineData} {M : Flat.Mapping}
    (h : AttemptContext initial current s M) (hd : current.state.data = h.wanted) :
    current.state = buildState h.before.p.fl h.before.state h.saw := by
  rw [h.state, hd]
  rfl

end AttemptContext

end Bbu.Unit.PlannerRunU
