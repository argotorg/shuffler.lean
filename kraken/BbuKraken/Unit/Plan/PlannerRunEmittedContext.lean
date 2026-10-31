import BbuKraken.Unit.Plan.PlannerRunAttemptContext

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

structure EmittedContext (initial current : PlannerRunG) (s : MachineData)
    (M : Flat.Mapping) where
  before : PlannerRunG
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

theorem afterEmission {initial current : PlannerRunG} {s t u : MachineData}
    {P : Addr} {M : Flat.Mapping} {F : MProp 64} {ra : Int64} {lo locals : List Word}
    (ctx : AttemptContext initial current s M) (hd : current.state.data = ctx.wanted)
    (h : EmitCountLI P current M F s ra lo locals t)
    (hp : locals[4115]? = some (Flat.unmappedFrom (countState current M) 0 0))
    (a : G) (hk : Keep (emissionGhost current ctx.ok (localEmissionHdr locals h.localLength)) a)
    (hq : runQ (EmissionLocals.ofList locals h.localLength).planned.pos
      (emissionGhost current ctx.ok (localEmissionHdr locals h.localLength)) a t u) :
    ∃ ec : EmittedContext initial
      (emissionResult current ctx.ok (localEmissionHdr locals h.localLength) a hk) s M,
      al u = code ec.status ∧ ec.out = flat a := by
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
  have hctor := h.ghost_ctor ctx.ok hp
  have hs := ctx.copiedState hd
  have hemit : Flat.emissionRun M.pos l
      (Flat.ctorP (buildState ctx.before.p.fl ctx.before.state ctx.saw).data
        ctx.before.p.m ctx.before.p.fl.target ctx.before.p.n M ctx.before.spills u0.u) =
        (e.1, flat a) := by
    have he0 : Flat.emissionRun M.pos l
        (flat (emissionGhost current ctx.ok hdr)) = (e.1, flat a) := by
      have hh : Flat.emissionRun M.pos l (flat (emissionGhost current ctx.ok hdr)) = e := by
        dsimp only [e]
        rw [hplan]
      exact hh.trans (Prod.ext rfl he.symm)
    dsimp only at hctor
    rw [hctor] at he0
    have hdata := congrArg Flat.PSt.data hs
    change current.data.map StackSlot.ofWord = _ at hdata
    have hsp := congrArg Flat.PSt.spills hs
    change current.spills = ctx.before.spills at hsp
    have hm := congrArg Flat.Planner.m ctx.planner
    have hn := congrArg Flat.Planner.n ctx.planner
    change current.p.m = ctx.before.p.m at hm
    change current.p.n = ctx.before.p.n at hn
    simpa only [hdata, hm, hn, hsp, ctx.planner] using he0
  have hstate : result.state = emittedState
      (buildState ctx.before.p.fl ctx.before.state ctx.saw) (flat a) := by
    rw [emissionResult_state hk, hs]
    rfl
  let ec : EmittedContext initial result s M := {
    before := ctx.before
    loop := ctx.loop
    attempt := u0
    out := flat a
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
end Bbu.Unit.PlannerRunU
