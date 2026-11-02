module

public import FlatShuffler.Unit.Plan.PlannerRunCompleteContext
import all FlatShuffler.Unit.Plan.PlannerRunCompleteContext
public import FlatShuffler.Unit.Plan.PlannerRunVariant
import all FlatShuffler.Unit.Plan.PlannerRunVariant
public import FlatShuffler.Unit.Plan.PlannerRunScanDefs
import all FlatShuffler.Unit.Plan.PlannerRunScanDefs
public import FlatShuffler.Unit.Plan.PlannerRunValidate
import all FlatShuffler.Unit.Plan.PlannerRunValidate

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

def LoopPhase (initial : PlannerCallMemory) (s : MachineData)
    (phase : PlannerCallMemory → MachineData → Prop) (t : MachineData) : Prop :=
  ∃ current, current.Ok ∧ Nonempty (LoopContext initial current s) ∧ phase current t

def AttemptPhase (initial : PlannerCallMemory) (s : MachineData)
    (phase : PlannerCallMemory → Flat.Mapping → MachineData → Prop) (t : MachineData) : Prop :=
  ∃ current M, ∃ ctx : AttemptContext initial current s M,
    current.state.data = ctx.wanted ∧ phase current M t

def EmittedPhase (initial : PlannerCallMemory) (s : MachineData)
    (phase : PlannerCallMemory → Flat.Mapping → MachineData → Prop) (t : MachineData) : Prop :=
  ∃ current M, ∃ ctx : EmittedContext initial current s M,
    some (al t) = code ctx.status ∧ ctx.status ≠ .blocked ∧ ctx.status ≠ .assertionExit ∧
      phase current M t

def RunReturn (P : Addr) (initial : PlannerCallMemory) (F : MProp 64) (s : MachineData)
    (ra : Int64) (t : MachineData) : Prop :=
  ∃ current lo locals, Bd P current F s ra lo locals t ∧ current.Ok ∧
    plannerRunNormalReturn initial current s t

def SourcePhase (P : Addr) (initial : PlannerCallMemory) (F : MProp 64) (s : MachineData)
    (ra : Int64) (t : MachineData) : Prop :=
  ∃ current M wanted,
    Nonempty (RunResult initial {current with sources := wanted} s .done) ∧
    current.count = initial.count ∧ al t = 0#8 ∧ SourcesHead P current M F s ra wanted t

def SourceDonePhase (P : Addr) (initial : PlannerCallMemory) (F : MProp 64) (s : MachineData)
    (ra : Int64) (t : MachineData) : Prop :=
  ∃ current M, Nonempty (RunResult initial current s .done) ∧
    al t = 0#8 ∧ SourcesDone P current M F s ra t

def BuildFailPhase (P : Addr) (initial : PlannerCallMemory) (F : MProp 64) (s : MachineData)
    (ra : Int64) (t : MachineData) : Prop :=
  ∃ current M0, current.Ok ∧ Nonempty (LoopContext initial current s) ∧
    BuildFailed P current F s ra M0 t

def RetryPhase (P : Addr) (initial : PlannerCallMemory) (F : MProp 64) (s : MachineData)
    (ra : Int64) (t : MachineData) : Prop :=
  ∃ current M before, ∃ ctx : ResolvedContext initial current s before,
    ctx.resolution = .dropped ∧ DropAfterHead P current M F s ra before t

def RetryFailPhase (P : Addr) (initial : PlannerCallMemory) (F : MProp 64) (s : MachineData)
    (ra : Int64) (t : MachineData) : Prop :=
  ∃ current before lo locals, ∃ ctx : ResolvedContext initial current s before,
    ctx.resolution = .dropped ∧
    ¬ Flat.droppedCount current.p.sourceSize current.dropped > before ∧
    Bd P current F s ra lo locals t ∧ current.Ok

def RunInv (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (resolvePhase : Label → MachineData → Prop) : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.plannerRun then t = s.pushRa ra
    else if l = ".LB.Planner.run.0" then CheckNext P (withSaw g 0#8) F s ra t
    else if l = ".LB.Planner.run.1" then CheckHead P (withSaw g 0#8) F s ra t
    else if l = ".LB.Planner.run.2" then CheckScan P (withSaw g 0#8) F s ra t
    else if l = ".LB.Planner.run.3" then CheckMissing P (withSaw g 0#8) F s ra t
    else if l = ".LB.Planner.run.5" then CheckDone P (withSaw g 0#8) F s ra t
    else if l = ".LB.Planner.run.19" then LoopPhase g s (fun a => PrepareHead P a F s ra) t
    else if l = ".LB.Planner.run.20" then LoopPhase g s (fun a => InitDestHead P a F s ra) t
    else if l = ".LB.Planner.run.21" then LoopPhase g s (fun a => InitDestDone P a F s ra) t
    else if l = ".LB.Planner.run.22" then LoopPhase g s (fun a => InitPosHead P a F s ra) t
    else if l = ".LB.Planner.run.23" then LoopPhase g s (fun a => InitDone P a F s ra) t
    else if l = ".LB.Planner.run.24" then
      ∃ current M, ∃ ctx : AttemptContext g current s M,
        EmitDataHead P current M F s ra ctx.wanted t
    else if l = ".LB.Planner.run.25" then AttemptPhase g s (fun a M => EmitDestHead P a M F s ra) t
    else if l = ".LB.Planner.run.26" then AttemptPhase g s (fun a M => EmitDestDone P a M F s ra) t
    else if l = ".LB.Planner.run.27" then AttemptPhase g s (fun a M => EmitPosHead P a M F s ra) t
    else if l = ".LB.Planner.run.7" then AttemptPhase g s (fun a M => EmitCountNext P a M F s ra) t
    else if l = ".LB.Planner.run.8" then AttemptPhase g s (fun a M => EmitCountHead P a M F s ra) t
    else if l = ".LB.Planner.run.9" then EmittedPhase g s (fun a M => PostEmitHead P a M F s ra) t
    else if l = ".LB.Planner.run.10" then SourcePhase P g F s ra t
    else if l = ".LB.Planner.run.11" then SourceDonePhase P g F s ra t
    else if l = ".LB.Planner.run.6" then BuildFailPhase P g F s ra t
    else if l = ".LB.Planner.run.13" then RetryFailPhase P g F s ra t
    else if l = ".LB.Planner.run.4" then CheckBad P (withSaw g 0#8) F s ra t
    else if l = ".LB.Planner.run.12" then RunReturn P g F s ra t
    else if l = ".LB.Planner.run.14" then
      AttemptPhase g s (fun a M t => a.p.targetSize = 0#64 ∧ EmitMapped P a M F s ra t) t
    else if l = ".LB.Planner.run.15" then AttemptPhase g s (fun a M => EmitReady P a M F s ra) t
    else if l = ".LB.Planner.run.18" then RetryPhase P g F s ra t
    else if l = ".LB.Planner.run.28" then
      AttemptPhase g s (fun a M t => a.p.sourceSize = 0#64 ∧
        ∃ lo locals, AttemptLI P a M F s ra lo locals t) t
    else resolvePhase l t

def RunExit [Host] (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t =>
    (a = ra ∧ VPost plannerCallOwnedMemory PlannerCallMemory.Ok P F plannerRunD
      (fun g' u => plannerRunNormalReturn g g' s u) s t ∧ Sep.mod.Agree s t) ∨
    (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧
      VPost plannerCallOwnedMemory PlannerCallMemory.Ok P F plannerRunD
        (fun g' u => plannerRunX g g' s u) s t)

def RunObl [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64) (resolvePhase : Label → MachineData → Prop)
    (blk : Program.Block) : Prop :=
  ∀ t, RunInv P g F s ra resolvePhase blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' (RunExit P g F s ra)) t

attribute [local simp] RunInv

end FlatShuffler.Unit.PlannerRunU
