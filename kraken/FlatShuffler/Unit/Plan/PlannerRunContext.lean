module

public import FlatShuffler.Unit.Plan.PlannerRunResult
import all FlatShuffler.Unit.Plan.PlannerRunResult
public import FlatShuffler.Unit.Plan.PlannerRunBuilderDefs
import all FlatShuffler.Unit.Plan.PlannerRunBuilderDefs

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU

structure RunMeta (initial current : PlannerCallMemory) : Prop where
  planner : current.p = {initial.p with saw := current.p.saw}
  dataPtr : current.dataPtr = initial.dataPtr
  opsPtr : current.opsPtr = initial.opsPtr
  sourcesPtr : current.sourcesPtr = initial.sourcesPtr
  countPtr : current.countPtr = initial.countPtr
  spillCount : current.spillCount = initial.spillCount

theorem RunMeta.refl (g : PlannerCallMemory) : RunMeta g g :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RunMeta.fl {initial current : PlannerCallMemory} (h : RunMeta initial current) :
    current.p.fl = initial.p.fl := by rw [h.planner]; rfl

theorem RunMeta.withSaw {initial current : PlannerCallMemory} (h : RunMeta initial current)
    (saw : BitVec 8) : RunMeta initial (withSaw current saw) := by
  refine ⟨?_, h.dataPtr, h.opsPtr, h.sourcesPtr, h.countPtr, h.spillCount⟩
  exact congrArg (fun p : PlannerObjectMemory => {p with saw := saw}) h.planner

def prependRun (u : Flat.RunU) (us : Nat → Flat.RunU) : Nat → Flat.RunU
  | 0 => u
  | k + 1 => us k

structure LoopContext (initial current : PlannerCallMemory) (s : MachineData) where
  stable : RunMeta initial current
  count : current.count = initial.count
  plug : (Nat → Flat.RunU) → Nat → Flat.RunU
  model : ∀ us,
    Flat.plannerRun initial.p.fl ((rsi s).setWidth 8 == 1#8) initial.state (plug us) =
      Flat.runLoop current.p.fl ((rsi s).setWidth 8 == 1#8) current.state us

def LoopContext.start (g : PlannerCallMemory) (s : MachineData)
    (ht : Flat.targetsFrom g.p.fl g.spills 0 = true) :
    LoopContext g (withSaw g 0#8) s where
  stable := (RunMeta.refl g).withSaw 0#8
  count := rfl
  plug := id
  model us := by
    rw [plannerRun_targets_ok _ _ _ _ ht, withSaw_state]
    rfl

def LoopContext.next {initial current next : PlannerCallMemory} {s : MachineData}
    (h : LoopContext initial current s) (u : Flat.RunU)
    (hm : RunMeta initial next) (hc : next.count = initial.count)
    (hs : ∀ us,
      Flat.runLoop current.p.fl ((rsi s).setWidth 8 == 1#8) current.state (prependRun u us) =
        Flat.runLoop next.p.fl ((rsi s).setWidth 8 == 1#8) next.state us) :
    LoopContext initial next s where
  stable := hm
  count := hc
  plug us := h.plug (prependRun u us)
  model us := (h.model _).trans (hs us)

theorem LoopContext.finish {initial current final : PlannerCallMemory} {s t : MachineData}
    (h : LoopContext initial current s) (hm : RunMeta initial final)
    (us : Nat → Flat.RunU) (st : Flat.Status)
    (hr : Flat.runLoop current.p.fl ((rsi s).setWidth 8 == 1#8) current.state us =
      (st, final.state))
    (ha : al t = code st)
    (hc : final.count = if st = .done then BitVec.ofNat 64 final.state.trace.length
      else initial.count) : plannerRunQ initial final s t := by
  refine ⟨h.plug us, ?_⟩
  rw [h.model us, hr]
  exact ⟨ha, rfl, hm.planner, hm.dataPtr, hm.opsPtr, hm.sourcesPtr,
    hm.countPtr, hm.spillCount, hc⟩

theorem PlannerCallMemory.trace_length {g : PlannerCallMemory} (h : g.Ok) :
    g.state.trace.length = g.traceLength := by
  simp only [PlannerCallMemory.state, List.length_map, List.length_take,
    Nat.min_eq_left h.traceLength]

theorem LoopContext.mapping_fail {initial current : PlannerCallMemory} {s t : MachineData}
    (h : LoopContext initial current s) (hok : current.Ok) (M : Flat.Mapping)
    (hi : M.init current.p.m current.p.n = M)
    (hb : Flat.buildMapping (plannerBuilder current s M 0#8).fl M = none)
    (ha : al t = code .assertionFailed) : plannerRunQ initial current s t := by
  let u : Flat.RunU := {emptyRunU with mapping := M}
  apply h.finish h.stable (fun _ => u) .assertionFailed
  · apply runLoop_mapping_fail
    change Flat.buildMapping
      ⟨current.p.fl.source, current.p.m, current.p.fl.target, current.p.n,
        current.dropped, (rsi s).setWidth 8 == 1#8⟩
      (M.init current.p.m current.p.n) = none
    rw [hi]
    exact (builderGhost_buildMapping current hok _ _ _ M).symm.trans hb
  · exact ha
  · exact h.count

end FlatShuffler.Unit.PlannerRunU
