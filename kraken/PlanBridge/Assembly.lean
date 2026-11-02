module

public import PlanBridge.Interface
import all BbuKraken.PlanFinal

/-! The assembly contract starts at the C++ method `Planner::run`.
Its implementation imports stay private. -/

namespace PlanBridge

open Bbu Bbu.Unit
open Std.WP Lean.Order
open scoped Program.WP

private def inputOf (g : PlannerRunG) (s : MachineData) : Input :=
  ⟨g.p.fl, (rsi s).setWidth 8 == 1#8, g.state⟩

private def RunResult (post : Input → FlatResult → Prop)
    (g g' : PlannerRunG) (s : MachineData) (st : Flat.Status) : Prop :=
  ∃ us, let r := (inputOf g s).run us
    r.1 = st ∧ g'.state = r.2 ∧ post (inputOf g s) r

private def RunPost (post : Input → FlatResult → Prop) (P : Addr)
    (g : PlannerRunG) (F : MProp 64) (s t : MachineData) : Prop :=
  VPost PlannerRunView PlannerRunG.Ok P F plannerRunD
    (fun g' t => plannerRunQ g g' s t ∧
      ∃ st, al t = code st ∧ RunResult post g g' s st) s t

private def RunExit (post : Input → FlatResult → Prop) (P : Addr)
    (g : PlannerRunG) (F : MProp 64) (s t : MachineData) : Prop :=
  VPost PlannerRunView PlannerRunG.Ok P F plannerRunD
    (fun g' _ => plannerRunX g g' s t ∧ RunResult post g g' s .assertionFailed) s t

public def AssemblyContract (valid : Input → Prop) (post : Input → FlatResult → Prop) : Prop :=
  ∀ [Host] (L : Linked) (_X : ExitBoundary),
    letI := L.plannerDecls
    ∀ (P : Addr) (g : PlannerRunG) (F : MProp 64),
      Sep.BodyWithExit plannerRunAsm
        (fun s => VPre PlannerRunView PlannerRunG.Ok P g F plannerRunA plannerRunD s ∧
          valid (inputOf g s))
        (RunPost post P g F) (RunExit post P g F)

public def AssemblyBinaryContract (valid : Input → Prop)
    (post : Input → FlatResult → Prop) : Prop :=
  letI := binLinked.plannerDecls
  ∀ (P : Addr) (g : PlannerRunG) (F : MProp 64),
    Sep.BodyWithExit plannerRunAsm
      (fun s => VPre PlannerRunView PlannerRunG.Ok P g F plannerRunA plannerRunD s ∧
        valid (inputOf g s))
      (RunPost post P g F) (RunExit post P g F)

private theorem runPost_of_post {post : Input → FlatResult → Prop}
    {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t : MachineData}
    (hc : ∀ us, post (inputOf g s) ((inputOf g s).run us))
    (h : VPost PlannerRunView PlannerRunG.Ok P F plannerRunD
      (fun g' t => plannerRunQ g g' s t) s t) : RunPost post P g F s t := by
  obtain ⟨g', hq, hok, hm⟩ := h
  obtain ⟨us, hcode, hstate, hrest⟩ := hq
  refine ⟨g', ⟨⟨us, hcode, hstate, hrest⟩, _, hcode, us, rfl, hstate, hc us⟩, hok, hm⟩

private theorem runExit_of_exit {post : Input → FlatResult → Prop}
    {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t : MachineData}
    (hc : ∀ us, post (inputOf g s) ((inputOf g s).run us))
    (h : VPost PlannerRunView PlannerRunG.Ok P F plannerRunD
      (fun g' t => plannerRunX g g' s t) s t) : RunExit post P g F s t := by
  obtain ⟨g', hx, hok, hm⟩ := h
  obtain ⟨us, hstatus, hstate, hrest⟩ := hx
  exact ⟨g', ⟨⟨us, hstatus, hstate, hrest⟩, us, hstatus, hstate, hc us⟩, hok, hm⟩

public theorem kraken_to_flat {valid : Input → Prop} {post : Input → FlatResult → Prop}
    (hc : ∀ i us, valid i → post i (i.run us)) : AssemblyContract valid post := by
  intro _ L X
  let := L.plannerDecls
  intro P g F s ra
  refine ⟨fun t ⟨ht, hp, ok⟩ => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ h => h.elim
      (fun ⟨ha, hq, hm⟩ => Or.inl
        ⟨ha, runPost_of_post (fun us => hc _ us ok) hq, hm⟩)
      (fun ⟨ha, harg, hx⟩ => Or.inr
        ⟨ha, harg, runExit_of_exit (fun us => hc _ us ok) hx⟩))
    ((Bbu.plan_correct L X P g F s ra).le_wp t ⟨ht, hp⟩)

public theorem kraken_to_flat_binary {valid : Input → Prop}
    {post : Input → FlatResult → Prop}
    (hc : ∀ i us, valid i → post i (i.run us)) : AssemblyBinaryContract valid post :=
  kraken_to_flat hc binLinked binBoundary

end PlanBridge
