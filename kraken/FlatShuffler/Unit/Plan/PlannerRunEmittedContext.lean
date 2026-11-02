module

public import FlatShuffler.Unit.Plan.PlannerRunAttemptContext
import all FlatShuffler.Unit.Plan.PlannerRunAttemptContext
public import FlatShuffler.Unit.Plan.PlannerRunDataEmission
import all FlatShuffler.Unit.Plan.PlannerRunDataEmission

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

structure EmittedContext (initial current : PlannerCallMemory) (s : MachineData)
    (M : Flat.Mapping) where
  before : PlannerCallMemory
  loop : LoopContext initial before s
  attempt : Flat.RunU
  out : Flat.St
  status : Flat.Status
  stable : RunMeta initial current
  count : current.count = initial.count
  targets : Flat.targetsFrom current.p.fl current.spills 0 = true
  model : ∀ r us,
    Flat.runLoop before.p.fl ((rsi s).setWidth 8 == 1#8) before.state
      (prependRun {attempt with r := r} us) =
    emissionNext current.p.fl ((rsi s).setWidth 8 == 1#8) M status out current.state r us

namespace AttemptContext

theorem afterEmission {initial current : PlannerCallMemory} {s t u : MachineData}
    {P : Addr} {M : Flat.Mapping} {F : MProp 64} {ra : Int64} {lo locals : List Word}
    (ctx : AttemptContext initial current s M) (hd : current.state.data = ctx.wanted)
    (h : EmitCountLI P current M F s ra lo locals t)
    (hp : locals[4115]? = some (Flat.unmappedFrom (countState current M) 0 0))
    (a : G) (hk : Keep (emissionGhost current ctx.ok (localEmissionHdr locals h.localLength)) a)
    (hq : runModelResult (EmissionLocals.ofList locals h.localLength).planned.pos
      (emissionGhost current ctx.ok (localEmissionHdr locals h.localLength)) a t u) :
    ∃ ec : EmittedContext initial
      (emissionResult current ctx.ok (localEmissionHdr locals h.localLength) a hk) s M,
      al u = code ec.status ∧ ec.out =
        Flat.restoreData current.dataCapacity (current.data.map StackSlot.ofWord) (flat a) := by
  obtain ⟨l, _, he, hal⟩ := hq
  let e := Flat.emissionRun (EmissionLocals.ofList locals h.localLength).planned.pos l
    (flat (emissionGhost current ctx.ok (localEmissionHdr locals h.localLength)))
  let result := emissionResult current ctx.ok (localEmissionHdr locals h.localLength) a hk
  let hdr := localEmissionHdr locals h.localLength
  let u0 : Flat.RunU := {emptyRunU with
    mapping := ctx.mapping
    u := ⟨hdr.dest, hdr.pos, hdr.blkOff, hdr.blkExc⟩
    l := l}
  have hplan : (EmissionLocals.ofList locals h.localLength).planned = M :=
    h.mappingEq h.localLength
  have hctor := h.ghost_ctor_full ctx.ok hp
  have hs := ctx.copiedState hd
  have hemit : Flat.emissionRun M.pos l
      (Flat.ctorP (buildState ctx.before.p.fl ctx.before.state ctx.saw).data
        ctx.before.p.m ctx.before.p.fl.target ctx.before.p.n M ctx.before.spills u0.u) =
        (e.1, Flat.restoreData current.dataCapacity
          (current.data.map StackSlot.ofWord) (flat a)) := by
    have he0 : Flat.emissionRun M.pos l
        (flat (emissionGhost current ctx.ok hdr)) = (e.1, flat a) := by
      have hh : Flat.emissionRun M.pos l (flat (emissionGhost current ctx.ok hdr)) = e := by
        dsimp only [e]
        rw [hplan]
      exact hh.trans (Prod.ext rfl he.symm)
    have hsafe := h.runA ctx.ok ctx.map hp
    change RunU.Safe (EmissionLocals.ofList locals h.localLength).planned.pos
      (flat (emissionGhost current ctx.ok (localEmissionHdr locals h.localLength)))
      (4 * current.p.m.toNat) at hsafe
    rw [hplan] at hsafe
    have hsize : (flat (emissionGhost current ctx.ok hdr)).size.toNat ≤
        current.dataCapacity := by
      change (localEmissionHdr locals h.localLength).len.toNat ≤ current.dataCapacity
      rw [(h.header.localHdr h.localLength).2.2.2.2.1]
      exact Nat.le_max_left _ _
    have hn : (flat (emissionGhost current ctx.ok hdr)).targetSize.toNat ≤
        current.dataCapacity := Nat.le_max_right _ _
    have hefull := Flat.restoreData_emissionRun current.dataCapacity
      (current.data.map StackSlot.ofWord) M.pos l
      (flat (emissionGhost current ctx.ok hdr)) hsize hn hsafe
    rw [he0] at hefull
    dsimp only at hctor hefull
    rw [hctor] at hefull
    have hdata := congrArg Flat.PSt.data hs
    change current.data.map StackSlot.ofWord = _ at hdata
    have hsp := congrArg Flat.PSt.spills hs
    change current.spills = ctx.before.spills at hsp
    have hm := congrArg Flat.Planner.m ctx.planner
    have hn := congrArg Flat.Planner.n ctx.planner
    change current.p.m = ctx.before.p.m at hm
    change current.p.n = ctx.before.p.n at hn
    simpa only [hdata, hm, hn, hsp, ctx.planner] using hefull
  have hstate : result.state = emittedState
      (buildState ctx.before.p.fl ctx.before.state ctx.saw)
        (Flat.restoreData current.dataCapacity (current.data.map StackSlot.ofWord) (flat a)) := by
    rw [emissionResult_state hk, hs]
    rfl
  let ec : EmittedContext initial result s M := {
    before := ctx.before
    loop := ctx.loop
    attempt := u0
    out := Flat.restoreData current.dataCapacity (current.data.map StackSlot.ofWord) (flat a)
    status := e.1
    stable := ⟨ctx.stable.planner, ctx.stable.dataPtr, ctx.stable.opsPtr,
      ctx.stable.sourcesPtr, ctx.stable.countPtr, ctx.stable.spillCount⟩
    count := ctx.count
    targets := ctx.targets
    model := by
      intro r us
      have hb : Flat.buildMapping
          ⟨ctx.before.p.fl.source, ctx.before.p.m, ctx.before.p.fl.target,
            ctx.before.p.n, ctx.before.dropped, (rsi s).setWidth 8 == 1#8⟩
          (((prependRun {u0 with r := r} us) 0).mapping.init
            ctx.before.p.m ctx.before.p.n) = some (M, ctx.saw) := by
        change Flat.buildMapping _ (ctx.mapping.init _ _) = _
        rw [ctx.init]
        exact ctx.build
      rw [runLoop_step hb hemit, ← hstate]
      change emissionNext ctx.before.p.fl _ _ _ _ _ r us =
        emissionNext current.p.fl _ _ _ _ _ r us
      rw [ctx.planner]
    }
  exact ⟨ec, hal, rfl⟩

end AttemptContext
end FlatShuffler.Unit.PlannerRunU
