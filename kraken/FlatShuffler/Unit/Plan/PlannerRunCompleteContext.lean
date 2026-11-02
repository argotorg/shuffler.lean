module

public import FlatShuffler.Unit.Plan.PlannerRunEmittedContext
import all FlatShuffler.Unit.Plan.PlannerRunEmittedContext
public import FlatShuffler.Unit.Plan.PlannerRunResolveDefs
import all FlatShuffler.Unit.Plan.PlannerRunResolveDefs

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

structure RunResult (initial current : PlannerCallMemory) (s : MachineData) (st : Flat.Status) where
  stable : RunMeta initial current
  attempts : Nat → Flat.RunU
  model : Flat.plannerRun initial.p.fl ((rsi s).setWidth 8 == 1#8) initial.state attempts =
    (st, current.state)

theorem RunResult.finish {initial current : PlannerCallMemory} {s t : MachineData} {st : Flat.Status}
    (h : RunResult initial current s st) (ha : al t = code st)
    (hc : current.count = if st = .done then BitVec.ofNat 64 current.state.trace.length
      else initial.count) : plannerRunQ initial current s t := by
  refine ⟨h.attempts, ?_⟩
  rw [h.model]
  exact ⟨ha, rfl, h.stable.planner, h.stable.dataPtr, h.stable.opsPtr,
    h.stable.sourcesPtr, h.stable.countPtr, h.stable.spillCount, hc⟩

theorem RunResult.exit {initial current : PlannerCallMemory} {s t : MachineData}
    (h : RunResult initial current s .assertionFailed)
    (hc : current.count = initial.count) : plannerRunX initial current s t := by
  refine ⟨h.attempts, ?_⟩
  rw [h.model]
  exact ⟨rfl, rfl, h.stable.planner, h.stable.dataPtr, h.stable.opsPtr,
    h.stable.sourcesPtr, h.stable.countPtr, h.stable.spillCount, hc⟩

def RunResult.withCount {initial current : PlannerCallMemory} {s : MachineData} {st : Flat.Status}
    (h : RunResult initial current s st) (w : Word) :
    RunResult initial {current with count := w} s st :=
  ⟨h.stable.withCount w, h.attempts, h.model⟩

def EmittedContext.terminal {initial current : PlannerCallMemory} {s : MachineData}
    {M : Flat.Mapping} (h : EmittedContext initial current s M)
    (hn : h.status ≠ .blocked) :
    RunResult initial
      {current with sources := if h.status = .done then
        Flat.sourcesFrom current.p.n 0 M current.sources else current.sources} s h.status where
  stable := h.stable.withSources _
  attempts := h.loop.plug (prependRun h.attempt (fun _ => emptyRunU))
  model := by
    rw [h.loop.model]
    have he := h.model h.attempt.r (fun _ => emptyRunU)
    have hu : {h.attempt with r := h.attempt.r} = h.attempt := by cases h.attempt; rfl
    rw [hu] at he
    rw [he]
    unfold emissionNext
    rw [ite_eq_left hn]
    by_cases hd : h.status = .done
    · rw [ite_eq_left hd, ite_eq_left hd]
      rfl
    · rw [ite_eq_right hd, ite_eq_right hd]

theorem AttemptContext.afterEmissionExit {initial current : PlannerCallMemory}
    {s t u : MachineData} {P : Addr} {M : Flat.Mapping} {F : MProp 64}
    {ra : Int64} {lo locals : List Word}
    (ctx : AttemptContext initial current s M) (hd : current.state.data = ctx.wanted)
    (h : EmitCountLI P current M F s ra lo locals t)
    (hp : locals[4115]? = some (Flat.unmappedFrom (countState current M) 0 0))
    (a : G) (hk : Keep (emissionGhost current ctx.ok (localEmissionHdr locals h.localLength)) a)
    (hx : runX (EmissionLocals.ofList locals h.localLength).planned.pos
      (emissionGhost current ctx.ok (localEmissionHdr locals h.localLength)) a t u) :
    plannerRunX initial
      (emissionResult current ctx.ok (localEmissionHdr locals h.localLength) a hk) s u := by
  obtain ⟨ec, hal, _⟩ := ctx.afterEmission hd h hp a hk (runX_to_modelResult hx)
  have hs : ec.status = .assertionFailed := by
    have he : 2#8 = code ec.status := hal
    cases hh : ec.status <;> simp [hh, code, DONE, BLOCKED, ASSERTION_FAILED] at he ⊢
  have ht := ec.terminal (by rw [hs]; decide)
  rw [hs] at ht
  have he := ht.exit (t := u) ec.count
  simpa only [hs, reduceCtorEq, ↓reduceIte] using he

def resolvedNext (pl : Flat.Planner) (take : Bool) (before : Word)
    (res : Flat.Resolution) (s : Flat.PSt) (us : Nat → Flat.RunU) : Flat.Status × Flat.PSt :=
  match res with
  | .stuck => (.blocked, s)
  | .assertionFailed => (.assertionFailed, s)
  | .dropped =>
    if Flat.droppedCount pl.m s.dropped > before then Flat.runLoop pl take s us
    else (.assertionFailed, s)

structure ResolvedContext (initial current : PlannerCallMemory) (s : MachineData)
    (before : Word) where
  prior : PlannerCallMemory
  loop : LoopContext initial prior s
  attempt : Flat.RunU
  resolution : Flat.Resolution
  stable : RunMeta initial current
  count : current.count = initial.count
  model : ∀ us, Flat.runLoop prior.p.fl ((rsi s).setWidth 8 == 1#8) prior.state
    (prependRun attempt us) =
      resolvedNext current.p.fl ((rsi s).setWidth 8 == 1#8) before resolution current.state us

def EmittedContext.afterResolve {initial current : PlannerCallMemory} {s : MachineData}
    {M : Flat.Mapping} (h : EmittedContext initial current s M) (hb : h.status = .blocked)
    (r : Flat.ResolveU) (res : Flat.Resolution) (sp : BitVec 32 → BitVec 8)
    (d : Vector (BitVec 8) MAX_N)
    (hq : Flat.resolve current.p.fl current.spills current.dropped M
      h.out.blockedOffset h.out.blockedExcess ⟨h.out.dest, h.out.pos⟩ h.out.size r =
        (res, sp, d)) :
    ResolvedContext initial (withResolve current sp d) s
      (Flat.droppedCount current.p.m current.dropped) where
  prior := h.before
  loop := h.loop
  attempt := {h.attempt with r := r}
  resolution := res
  stable := ⟨h.stable.planner, h.stable.dataPtr, h.stable.opsPtr,
    h.stable.sourcesPtr, h.stable.countPtr, h.stable.spillCount⟩
  count := h.count
  model := by
    intro us
    rw [h.model r us]
    simp only [emissionNext, hb, ne_eq, not_true_eq_false, ↓reduceIte]
    change Flat.resolve current.p.fl current.state.spills current.state.dropped M
      h.out.blockedOffset h.out.blockedExcess ⟨h.out.dest, h.out.pos⟩ h.out.size r = _ at hq
    rw [hq]
    cases res <;> rfl

namespace ResolvedContext

def retry {initial current : PlannerCallMemory} {s : MachineData} {before : Word}
    (h : ResolvedContext initial current s before) (hr : h.resolution = .dropped)
    (hp : Flat.droppedCount current.p.m current.dropped > before) :
    LoopContext initial current s :=
  h.loop.next h.attempt h.stable h.count (by
    intro us
    rw [h.model us]
    change Flat.droppedCount current.p.fl.m current.state.dropped > before at hp
    simp only [resolvedNext, hr, hp, ↓reduceIte])

def noProgress {initial current : PlannerCallMemory} {s : MachineData} {before : Word}
    (h : ResolvedContext initial current s before) (hr : h.resolution = .dropped)
    (hp : ¬ Flat.droppedCount current.p.m current.dropped > before) :
    RunResult initial current s .assertionFailed where
  stable := h.stable
  attempts := h.loop.plug (prependRun h.attempt (fun _ => emptyRunU))
  model := by
    rw [h.loop.model, h.model]
    change ¬ Flat.droppedCount current.p.fl.m current.state.dropped > before at hp
    simp only [resolvedNext, hr, hp, ↓reduceIte]

def terminal {initial current : PlannerCallMemory} {s : MachineData} {before : Word}
    (h : ResolvedContext initial current s before) (hr : h.resolution ≠ .dropped) :
    RunResult initial current s
      (if h.resolution = .stuck then .blocked else .assertionFailed) where
  stable := h.stable
  attempts := h.loop.plug (prependRun h.attempt (fun _ => emptyRunU))
  model := by
    rw [h.loop.model, h.model]
    cases he : h.resolution <;> simp_all [resolvedNext]

end ResolvedContext
end FlatShuffler.Unit.PlannerRunU
