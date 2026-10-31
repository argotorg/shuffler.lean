import BbuKraken.Unit.Plan.EntryResult
import ProofKit.CfgBlock

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

def wanted (g : EG) : Vector (BitVec 8) MAX_N :=
  Flat.zeroFrom g.r.p.m 0 g.r.dropped

def OutputPhase (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (word : EG → Word) (t : MachineData) : Prop :=
  ∃ g' lo, ∃ l : CallLocals,
    Bd g' F s ra lo (l.toList g'.r) t ∧ g'.Ok ∧
      ResultWord g (withSawOut g' g'.r.p.saw) (word g')

def ReturnPhase (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ g' lo locals, Bd g' F s ra lo locals t ∧ g'.Ok ∧ ResultWord g g' (rdx t)

def EntryInv (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.plan then t = s.pushRa ra
    else if l = ".LB.plan.0" then SourceNext g F s ra t
    else if l = ".LB.plan.1" then SourceHead g F s ra t
    else if l = ".LB.plan.2" then SourceDone g F s ra t ∧ g.r.p.m ≠ 0#64
    else if l = ".LB.plan.3" then TargetNext g F s ra t
    else if l = ".LB.plan.4" then TargetHead g F s ra t
    else if l = ".LB.plan.5" then Checked g F s ra t
    else if l = ".LB.plan.6" then Checked g F s ra t ∧ g.r.p.m ≠ 0#64
    else if l = ".LB.plan.7" then
      idsFrom g.r.p.sw g.idCount 0 = true ∧ idsFrom g.r.p.tw g.idCount 0 = true ∧
        ∃ d, ClearHead (withDropped g d) F s ra (wanted g) t
    else if l = ".LB.plan.8" then
      idsFrom g.r.p.sw g.idCount 0 = true ∧ idsFrom g.r.p.tw g.idCount 0 = true ∧
        Ready (withDropped g (wanted g)) F s ra t
    else if l = ".LB.plan.9" then ReturnPhase g F s ra t
    else if l = ".LB.plan.10" then OutputPhase g F s ra (fun a => a.r.count) t
    else if l = ".LB.plan.11" then OutputPhase g F s ra (fun _ => -1#64) t
    else if l = ".LB.plan.14" then SourceDone g F s ra t ∧ g.r.p.m = 0#64
    else False

def entryV (g : EG) (l : Label) (t : MachineData) : Nat :=
  if l = ".LB.plan.9" then 2
  else if l = ".LB.plan.10" ∨ l = ".LB.plan.11" then 4
  else if l = ".LB.plan.8" then 10
  else if l = ".LB.plan.7" then 100 + (r9 t - rax t).toNat
  else if l = ".LB.plan.6" then 3000
  else if l = ".LB.plan.5" then 4000
  else if l = ".LB.plan.4" then 6001 + 2 * (g.r.p.n.toNat - (rax t).toNat)
  else if l = ".LB.plan.3" then 6000 + 2 * (g.r.p.n.toNat - (rax t).toNat)
  else if l = ".LB.plan.2" ∨ l = ".LB.plan.14" then 8500
  else if l = ".LB.plan.1" then 10001 + 2 * (g.r.p.m.toNat - (rax t).toNat)
  else if l = ".LB.plan.0" then 10000 + 2 * (g.r.p.m.toNat - (rax t).toNat)
  else 19000

def EntryExit (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ Post g F s t ∧ Sep.mod.Agree s t

def EntryObl [Host] [FunDecls] (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, EntryInv g F s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept planAsm.labels (s.pushRa ra) I' (EntryExit g F s ra)) t

attribute [local simp] EntryInv entryV

end Bbu.Unit.EntryValidU
