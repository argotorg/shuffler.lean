module

public import BbuKraken.Unit.Plan.ResolveInit
import all BbuKraken.Unit.Plan.ResolveInit
public import BbuKraken.Unit.Plan.ResolveOuter
import all BbuKraken.Unit.Plan.ResolveOuter
public import BbuKraken.Unit.Plan.ResolveTie
import all BbuKraken.Unit.Plan.ResolveTie
public import BbuKraken.Unit.Plan.ResolveCursor
import all BbuKraken.Unit.Plan.ResolveCursor
public import BbuKraken.Unit.Plan.ResolveClassify
import all BbuKraken.Unit.Plan.ResolveClassify
public import BbuKraken.Unit.Plan.ResolveDispatch
import all BbuKraken.Unit.Plan.ResolveDispatch
public import BbuKraken.Unit.Plan.ResolveDrop
import all BbuKraken.Unit.Plan.ResolveDrop
public import BbuKraken.Unit.Plan.ResolveSpill
import all BbuKraken.Unit.Plan.ResolveSpill

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem phase_commute (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) :
    initFullPhase P r F s ra (loopPhase P r F s ra (dropPhase P r F s ra rest)) =
      loopPhase P r F s ra (dropPhase P r F s ra (initFullPhase P r F s ra rest)) := by
  funext l t
  by_cases h0 : l = ".LB.Planner.resolve.0"
  · subst l; simp [initFullPhase, zphase, loopPhase, dropPhase]
  by_cases h1 : l = ".LB.Planner.resolve.1"
  · subst l; simp [initFullPhase, zphase, loopPhase, dropPhase]
  by_cases h4 : l = ".LB.Planner.resolve.4"
  · subst l; simp [initFullPhase, zphase, initPhase, loopPhase, dropPhase]
  by_cases h5 : l = ".LB.Planner.resolve.5"
  · subst l; simp [initFullPhase, zphase, initPhase, loopPhase, dropPhase]
  by_cases h6 : l = ".LB.Planner.resolve.6"
  · subst l; simp [initFullPhase, zphase, initPhase, loopPhase, dropPhase]
  by_cases h7 : l = ".LB.Planner.resolve.7"
  · subst l; simp [initFullPhase, zphase, initPhase, loopPhase, dropPhase]
  simp [initFullPhase, zphase, initPhase, loopPhase, dropPhase, h0, h1, h4, h5, h6, h7]

theorem var_commute (s : MachineData) (rest : Label → MachineData → Nat) :
    initFullVar s (loopVar s rest) = loopVar s (initFullVar s rest) := by
  funext l t
  by_cases h0 : l = ".LB.Planner.resolve.0"
  · subst l; simp [initFullVar, zvar, loopVar]
  by_cases hf : l = Names.resolve
  · subst l; simp [initFullVar, zvar, initVar, loopVar, Names.resolve]
  by_cases h1 : l = ".LB.Planner.resolve.1"
  · subst l; simp [initFullVar, zvar, initVar, loopVar, Names.resolve]
  by_cases h4 : l = ".LB.Planner.resolve.4"
  · subst l; simp [initFullVar, zvar, initVar, loopVar, Names.resolve]
  by_cases h5 : l = ".LB.Planner.resolve.5"
  · subst l; simp [initFullVar, zvar, initVar, loopVar, Names.resolve]
  by_cases h6 : l = ".LB.Planner.resolve.6"
  · subst l; simp [initFullVar, zvar, initVar, loopVar, Names.resolve]
  by_cases h7 : l = ".LB.Planner.resolve.7"
  · subst l; simp [initFullVar, zvar, initVar, loopVar, Names.resolve]
  simp [initFullVar, zvar, initVar, loopVar, h0, hf, h1, h4, h5, h6, h7]

end ResolveU

theorem resolve_unit [Host] [FunDecls]
    (hout : ∀ l ∈ Program.labels resolveAsm, label l ≠ label "exit")
    (hclass : VSpec CView CG.Ok Names.classify classifyA 16 classifyQ)
    (hadd : AddSpec) : VThmWithExit RView RG.Ok resolveAsm resolveA 1182 resolveQ resolveX := by
  intro P r F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  subst ht
  obtain ⟨xs, hl, hk⟩ := hp.kg ra
  let rest := fun (_ : Label) (_ : MachineData) => False
  let var := fun (_ : Label) (_ : MachineData) => 0
  let phase := ResolveU.loopPhase P r F s ra (ResolveU.dropPhase P r F s ra rest)
  let variant := ResolveU.loopVar s var
  refine Program.WP.cfg
    (ResolveU.Inv P r F s ra (ResolveU.initFullPhase P r F s ra phase))
    (ResolveU.V (ResolveU.initFullVar s variant)) ?_ rfl
  refine forallBlocks_cases ResolveU.labels ResolveU.labels_cover ?_
  intro l hlab
  simp only [ResolveU.labels, List.mem_cons, List.not_mem_nil, or_false] at hlab
  rcases hlab with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ResolveU.b_entry P r F s ra _ _
  · exact ResolveU.b_fn P r F s ra phase variant hp.ok hp.args hp.rdi xs hl hk
  · exact ResolveU.b_0 P r F s ra (ResolveU.InitPayload s)
      (ResolveU.initPhase P r F s ra phase) (ResolveU.initVar s variant) 67113864
      hp.ok (ResolveU.initPayload_store s) (by intro t; simp [ResolveU.initVar, Names.resolve])
  · exact ResolveU.b_1 P r F s ra phase variant hp.ok hp.args
  · exact ResolveU.b_2 P r F s ra _ _
  · exact ResolveU.b_3 P r F s ra _ _
  · exact ResolveU.b_4 P r F s ra phase variant
  · exact ResolveU.b_5 P r F s ra phase variant hp.ok hp.args
  · exact ResolveU.b_6 P r F s ra phase variant
  · apply ResolveU.b_7 P r F s ra phase variant hp.ok hp.args
    · intro t ht
      simpa [phase, ResolveU.loopPhase] using ht
    · intro t ht
      have he := hp.args.2.2.2.2.1
      change (rcx s).toNat ≤ 1024 at he
      simp only [variant, ResolveU.loopVar, ↓reduceIte,
        ResolveU.loopBase, ht, BitVec.sub_zero]
      omega
  all_goals change resolveAsm.ForallBlocks (fun blk => blk.label = _ →
    ResolveU.Obl P r F s ra
      (ResolveU.initFullPhase P r F s ra
        (ResolveU.loopPhase P r F s ra (ResolveU.dropPhase P r F s ra rest)))
      (ResolveU.initFullVar s (ResolveU.loopVar s var)) blk)
  all_goals rw [ResolveU.phase_commute, ResolveU.var_commute]
  · exact ResolveU.b_8 P r F s ra _ _ hp.ok
  · exact ResolveU.b_9 P r F s ra _ _ hp.ok
  · exact ResolveU.b_10 P r F s ra _ _
  · exact ResolveU.b_11 P r F s ra _ _
  · exact ResolveU.b_12 P r F s ra _ _ hp.ok hclass
  · exact ResolveU.b_13 P r F s ra _ _ hp.ok
  · exact ResolveU.b_14 P r F s ra _ _ hp.ok
  · exact ResolveU.b_15 P r F s ra _ _ hout hp.ok (ResolveU.addVSpec hadd)
  · exact ResolveU.b_16 P r F s ra _ _
  · exact ResolveU.b_17 P r F s ra _ _
  · exact ResolveU.b_18 P r F s ra _ _

end Bbu.Unit
