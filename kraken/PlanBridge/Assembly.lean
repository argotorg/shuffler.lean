module

public import PlanBridge.Interface
import all BbuKraken.PlanFinal

/-! The assembly contract. Its implementation imports stay private. -/

namespace PlanBridge

open Bbu Bbu.Unit Bbu.Unit.EntryValidU
open Std.WP Lean.Order
open scoped Program.WP

private def inputOf (g : EG) : Input :=
  ⟨g.r.p.m, g.r.p.n, g.r.p.fl.source, g.r.p.fl.target, g.r.spills, g.idCount,
    g.allowed.setWidth 8, g.strategy.setWidth 8, g.r.dropped,
    g.r.data.map StackSlot.ofWord, g.r.sources⟩

private def EntryResult (post : Input → FlatResult → Prop) (g g' : EG) (w : Bbu.Word) : Prop :=
  ∃ us, let r := model g us
    w = r.1 ∧
      match r.2 with
      | none => post (inputOf g) (w, none) ∧ g' = g
      | some (st, state) => Keep g g' ∧ g'.r.state = state ∧
          (if st = .assertionFailed then g'.saw = g.saw
           else (g'.saw != 0#8) = state.saw) ∧
          post (inputOf g) (w, some (st, state))

private def EntryPost (post : Input → FlatResult → Prop) (g : EG) (F : MProp 64)
    (s t : MachineData) : Prop :=
  ∃ g', g'.Ok ∧ EntryResult post g g' (rax t) ∧
    StkMem entryD (View (rsp s) g' ∗ F) s t.dmem

private def EntryExit (post : Input → FlatResult → Prop) (g : EG) (F : MProp 64)
    (s t : MachineData) : Prop :=
  ∃ g', g'.Ok ∧ AssertionResult g g' ∧
    post (inputOf g) (-2#64, some (.assertionFailed, g'.r.state)) ∧
    StkMem entryD (View (rsp s) g' ∗ F) s t.dmem

public def AssemblyContract (valid : Input → Prop) (post : Input → FlatResult → Prop) : Prop :=
  ∀ [Host] (L : Linked) (_X : ExitBoundary),
    letI := L.plannerDecls
    ∀ (g : EG) (F : MProp 64), valid (inputOf g) →
      Sep.BodyWithExit planAsm (EntryValidU.Pre g F) (EntryPost post g F)
        (EntryExit post g F)

public def AssemblyHarnessContract (valid : Input → Prop)
    (post : Input → FlatResult → Prop) : Prop :=
  letI := binLinked.plannerDecls
  ∀ (g : EG) (F : MProp 64), valid (inputOf g) →
    Sep.BodyWithExit planAsm (EntryValidU.Pre g F) (EntryPost post g F)
        (EntryExit post g F)

private theorem entryResult_of_result {post : Input → FlatResult → Prop}
    {g g' : EG} {w : Bbu.Word}
    (hc : ∀ us, post (inputOf g) ((inputOf g).run us))
    (h : ResultWord g g' w) : EntryResult post g g' w := by
  obtain ⟨us, hw, hr⟩ := h
  have hp := hc us
  change post (inputOf g) (model g us) at hp
  refine ⟨us, hw, ?_⟩
  generalize model g us = r at hw hr hp ⊢
  rcases r with ⟨c, _ | ⟨st, state⟩⟩
  · exact ⟨hw.symm ▸ hp, hr⟩
  · exact ⟨hr.1, hr.2.1, hr.2.2, hw.symm ▸ hp⟩

private theorem entryPost_of_post {post : Input → FlatResult → Prop}
    {g : EG} {F : MProp 64} {s t : MachineData}
    (hc : ∀ us, post (inputOf g) ((inputOf g).run us))
    (h : EntryValidU.Post g F s t) : EntryPost post g F s t := by
  obtain ⟨g', hg', hr, hm⟩ := h
  exact ⟨g', hg', entryResult_of_result hc hr, hm⟩

private theorem entryExit_of_exit {post : Input → FlatResult → Prop}
    {g : EG} {F : MProp 64} {s t : MachineData}
    (hc : ∀ us, post (inputOf g) ((inputOf g).run us))
    (h : EntryValidU.Exit g F s t) : EntryExit post g F s t := by
  obtain ⟨g', hg', hresult, hm⟩ := h
  obtain ⟨us, hmodel, hk, hsaw⟩ := hresult
  have hp := hc us
  change post (inputOf g) (model g us) at hp
  rw [hmodel] at hp
  exact ⟨g', hg', ⟨us, hmodel, hk, hsaw⟩, hp, hm⟩

public theorem kraken_to_flat {valid : Input → Prop} {post : Input → FlatResult → Prop}
    (hc : ∀ i us, valid i → post i (i.run us)) : AssemblyContract valid post := by
  intro _ L X
  let := L.plannerDecls
  intro g F ok s ra
  refine ⟨fun t ht => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ h => h.elim
      (fun ⟨ha, hp, hm⟩ => Or.inl
        ⟨ha, entryPost_of_post (fun us => hc _ us ok) hp, hm⟩)
      (fun ⟨ha, harg, hx⟩ => Or.inr
        ⟨ha, harg, entryExit_of_exit (fun us => hc _ us ok) hx⟩))
    ((Bbu.plan_correct L X g F s ra).le_wp t ht)

public theorem kraken_to_flat_harness {valid : Input → Prop}
    {post : Input → FlatResult → Prop}
    (hc : ∀ i us, valid i → post i (i.run us)) : AssemblyHarnessContract valid post :=
  kraken_to_flat hc binLinked binBoundary

end PlanBridge
