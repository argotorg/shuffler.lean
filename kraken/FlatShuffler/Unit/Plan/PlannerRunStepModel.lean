module

public import FlatShuffler.FlatPlan
import all FlatShuffler.FlatPlan

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU

def buildState (pl : Flat.Planner) (s : Flat.PSt) (saw : Bool) : Flat.PSt :=
  {s with saw := s.saw || saw, data := Flat.copyFrom pl 0 s.data}

def emittedState (s : Flat.PSt) (out : Flat.St) : Flat.PSt :=
  {s with data := out.data, trace := out.trace}

def resolvedState (s : Flat.PSt)
    (out : (BitVec 32 → BitVec 8) × Vector (BitVec 8) maxStackSize) : Flat.PSt :=
  {s with spills := out.1, dropped := out.2}

def emissionNext (pl : Flat.Planner) (take : Bool) (M : Flat.Mapping)
    (st : Flat.EmissionOutcome) (out : Flat.St) (s : Flat.PSt) (r : Flat.ResolveU)
    (us : Nat → Flat.RunU) : Flat.EmissionOutcome × Flat.PSt :=
  if st ≠ .blocked then
    if st = .done then (st, {s with sources := Flat.sourcesFrom pl.targetSize 0 M s.sources})
    else (st, s)
  else
    let q := Flat.resolve pl s.spills s.dropped M out.blockedOffset out.blockedExcess
      ⟨out.dest, out.pos⟩ out.size r
    let b := resolvedState s q.2
    match q.1 with
    | .stuck => (.blocked, b)
    | .assertionExit => (.assertionExit, b)
    | .dropped =>
      if Flat.droppedCount pl.sourceSize b.dropped > Flat.droppedCount pl.sourceSize s.dropped then
        Flat.runLoop pl take b us
      else (.assertionExit, b)

section
variable {pl : Flat.Planner} {take : Bool} {s : Flat.PSt} {us : Nat → Flat.RunU}
    {M : Flat.Mapping} {saw : Bool} {st : Flat.EmissionOutcome} {out : Flat.St}

theorem runLoop_step
    (hb : Flat.buildMapping ⟨pl.source, pl.sourceSize, pl.target, pl.targetSize, s.dropped, take⟩
      ((us 0).mapping.init pl.sourceSize pl.targetSize) = some (M, saw))
    (he : Flat.emissionRun M.pos (us 0).l
      (Flat.ctorP (buildState pl s saw).data pl.sourceSize pl.target pl.targetSize M s.spills (us 0).u) =
        (st, out)) :
    Flat.runLoop pl take s us = emissionNext pl take M st out
      (emittedState (buildState pl s saw) out) (us 0).r (fun k => us (k + 1)) := by
  dsimp only [buildState] at he
  rw [Flat.runLoop, hb]
  dsimp only
  rw [he]
  rfl

theorem runLoop_emitted
    (hb : Flat.buildMapping ⟨pl.source, pl.sourceSize, pl.target, pl.targetSize, s.dropped, take⟩
      ((us 0).mapping.init pl.sourceSize pl.targetSize) = some (M, saw))
    (he : Flat.emissionRun M.pos (us 0).l
      (Flat.ctorP (buildState pl s saw).data pl.sourceSize pl.target pl.targetSize M s.spills (us 0).u) =
        (st, out))
    (hn : st ≠ .blocked) :
    Flat.runLoop pl take s us =
      (st, if st = .done then
        {emittedState (buildState pl s saw) out with
          sources := Flat.sourcesFrom pl.targetSize 0 M s.sources}
        else emittedState (buildState pl s saw) out) := by
  dsimp only [buildState] at he
  rw [Flat.runLoop, hb]
  dsimp only
  rw [he]
  dsimp only
  rw [ite_eq_left hn]
  split <;> rfl

theorem runLoop_blocked
    (hb : Flat.buildMapping ⟨pl.source, pl.sourceSize, pl.target, pl.targetSize, s.dropped, take⟩
      ((us 0).mapping.init pl.sourceSize pl.targetSize) = some (M, saw))
    (he : Flat.emissionRun M.pos (us 0).l
      (Flat.ctorP (buildState pl s saw).data pl.sourceSize pl.target pl.targetSize M s.spills (us 0).u) =
        (.blocked, out)) :
    Flat.runLoop pl take s us =
      let a := emittedState (buildState pl s saw) out
      let q := Flat.resolve pl a.spills a.dropped M out.blockedOffset out.blockedExcess
        ⟨out.dest, out.pos⟩ out.size (us 0).r
      let b := resolvedState a q.2
      match q.1 with
      | .stuck => (.blocked, b)
      | .assertionExit => (.assertionExit, b)
      | .dropped =>
        if Flat.droppedCount pl.sourceSize b.dropped > Flat.droppedCount pl.sourceSize a.dropped then
          Flat.runLoop pl take b (fun k => us (k + 1))
        else (.assertionExit, b) := by
  dsimp only [buildState] at he
  rw [Flat.runLoop, hb]
  dsimp only
  rw [he]
  rfl

end
end FlatShuffler.Unit.PlannerRunU
