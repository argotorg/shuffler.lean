module

public import BbuKraken.Unit.Plan.EntryRejectThm
import all BbuKraken.Unit.Plan.EntryRejectThm
public import BbuKraken.Unit.Plan.EntryRead
import all BbuKraken.Unit.Plan.EntryRead
public import BbuKraken.Unit.Plan.EntryIdsModel
import all BbuKraken.Unit.Plan.EntryIdsModel

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.EntryRejectIds
open Bbu.Sep EntryValidU

/-- The owned lists can stop at the first invalid source or target ID. -/
structure G where
  m : Word
  n : Word
  src : Word
  tgt : Word
  idCount : Word
  allowed : BitVec 32
  strategy : BitVec 32
  sw : List Word
  tw : List Word

structure G.Ok (g : G) : Prop where
  sizes : ¬ EntryU.BadArgs g.m g.n g.allowed g.strategy
  sw : g.sw.length ≤ g.m.toNat
  tw : g.tw.length ≤ g.n.toNat
  bad : idsFrom g.sw g.idCount 0 = false ∨
    (g.sw.length = g.m.toNat ∧ idsFrom g.tw g.idCount 0 = false)

def Frame (g : G) (F : MProp 64) : MProp 64 := Arr g.src g.sw ∗ Arr g.tgt g.tw ∗ F
def Args (g : G) (F : MProp 64) (s : MachineData) : MProp 64 :=
  EntryU.Args s g.allowed g.strategy (Frame g F)

def Pre (g : G) (F : MProp 64) (s : MachineData) : Prop :=
  g.Ok ∧ rdi s = g.m ∧ rsi s = g.n ∧ rdx s = g.src ∧ rcx s = g.tgt ∧ r9 s = g.idCount ∧
    ∃ fr v, fr.length = 11 ∧ (Stk (rsp s) fr v ∗ Args g F s).get s.dmem

def Post (g : G) (F : MProp 64) (s t : MachineData) : Prop :=
  rax t = -2#64 ∧
    ∃ fr v, fr.length = 11 ∧ (Stk (rsp s) fr v ∗ Args g F s).get t.dmem

abbrev Bd (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo : List Word) (t : MachineData) :=
  EntryU.Bd g.allowed g.strategy (Frame g F) s ra lo t

structure LI (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo : List Word) (t : MachineData) : Prop extends Bd g F s ra lo t where
  rdi : rdi t = g.m
  rsi : rsi t = g.n
  rdx : rdx t = g.src
  rcx : rcx t = g.tgt
  r9 : r9 t = g.idCount

theorem LI.next {g F s ra lo t u} (h : LI g F s ra lo t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15)
    (hdi : Bbu.rdi u = Bbu.rdi t) (hsi : Bbu.rsi u = Bbu.rsi t) (hdx : Bbu.rdx u = Bbu.rdx t)
    (hcx : Bbu.rcx u = Bbu.rcx t) (h9 : Bbu.Unit.r9 u = Bbu.Unit.r9 t) : LI g F s ra lo u :=
  ⟨h.toBd.next hm hsp hbp h12 h13 h14 h15,
    hdi.trans h.rdi, hsi.trans h.rsi, hdx.trans h.rdx, hcx.trans h.rcx, h9.trans h.r9⟩

theorem G.Ok.m {g : G} (h : g.Ok) : g.m.toNat ≤ 1024 := by
  have hh := h.sizes
  unfold EntryU.BadArgs MAX_N at hh
  omega

theorem G.Ok.n {g : G} (h : g.Ok) : g.n.toNat ≤ 1024 := by
  have hh := h.sizes
  unfold EntryU.BadArgs MAX_N at hh
  omega

theorem G.Ok.targetBad {g : G} (h : g.Ok) (hs : idsFrom g.sw g.idCount 0 = true) :
    idsFrom g.tw g.idCount 0 = false := by
  rcases h.bad with hb | ⟨_, hb⟩
  · simp only [hs, Bool.true_eq_false] at hb
  · exact hb

theorem G.Ok.sourceReadable {g : G} (h : g.Ok) {i : Word} (hi : i < g.m)
    (hm : idsFrom g.sw g.idCount 0 = idsFrom g.sw g.idCount i.toNat) :
    i.toNat < g.sw.length := by
  by_cases hn : i.toNat < g.sw.length
  · exact hn
  apply False.elim
  have he := idsFrom_end g.sw g.idCount (Nat.le_of_not_gt hn)
  have hs := hm.trans he
  rcases h.bad with hb | ⟨hl, _⟩
  · simp only [hs, Bool.true_eq_false] at hb
  · have hi' := BitVec.lt_def.mp hi
    omega

theorem G.Ok.targetReadable {g : G} (h : g.Ok) {i : Word}
    (hs : idsFrom g.sw g.idCount 0 = true)
    (hm : idsFrom g.tw g.idCount 0 = idsFrom g.tw g.idCount i.toNat) :
    i.toNat < g.tw.length := by
  by_cases hn : i.toNat < g.tw.length
  · exact hn
  apply False.elim
  have he := hm.trans (idsFrom_end g.tw g.idCount (Nat.le_of_not_gt hn))
  have hb := h.targetBad hs
  simp only [he, Bool.true_eq_false] at hb

theorem Bd.sourceRead {g F s ra lo t} (h : Bd g F s ra lo t) {i : Nat}
    (hi : i < g.sw.length) : SlotRead t.dmem (slotAt g.src i) g.sw[i] := by
  obtain ⟨R, he⟩ : ∃ R, Stk (rsp s) (lo ++ [s.regs.rbx.toBitVec]) ra.toBitVec ∗
      EntryU.Args s g.allowed g.strategy (Frame g F) = Arr g.src g.sw ∗ R :=
    ⟨_, by unfold EntryU.Args Frame; ecancel⟩
  exact slot_read (he ▸ h.kb.mem) hi

theorem Bd.targetRead {g F s ra lo t} (h : Bd g F s ra lo t) {i : Nat}
    (hi : i < g.tw.length) : SlotRead t.dmem (slotAt g.tgt i) g.tw[i] := by
  obtain ⟨R, he⟩ : ∃ R, Stk (rsp s) (lo ++ [s.regs.rbx.toBitVec]) ra.toBitVec ∗
      EntryU.Args s g.allowed g.strategy (Frame g F) = Arr g.tgt g.tw ∗ R :=
    ⟨_, by unfold EntryU.Args Frame; ecancel⟩
  exact slot_read (he ▸ h.kb.mem) hi

def SourceHead (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo, LI g F s ra lo t ∧ rax t < g.m ∧
    idsFrom g.sw g.idCount 0 = idsFrom g.sw g.idCount (rax t).toNat
def SourceNext (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo, LI g F s ra lo t ∧ rax t < g.m ∧
    idsFrom g.sw g.idCount 0 = idsFrom g.sw g.idCount ((rax t).toNat + 1)
def SourceDone (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo, LI g F s ra lo t ∧ idsFrom g.sw g.idCount 0 = true
def TargetHead (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo, LI g F s ra lo t ∧ rax t < g.n ∧ idsFrom g.sw g.idCount 0 = true ∧
    idsFrom g.tw g.idCount 0 = idsFrom g.tw g.idCount (rax t).toNat
def TargetNext (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo, LI g F s ra lo t ∧ rax t < g.n ∧ idsFrom g.sw g.idCount 0 = true ∧
    idsFrom g.tw g.idCount 0 = idsFrom g.tw g.idCount ((rax t).toNat + 1)

def Inv (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.plan then t = s.pushRa ra
    else if l = ".LB.plan.0" then SourceNext g F s ra t
    else if l = ".LB.plan.1" then SourceHead g F s ra t
    else if l = ".LB.plan.2" then SourceDone g F s ra t
    else if l = ".LB.plan.3" then TargetNext g F s ra t
    else if l = ".LB.plan.4" then TargetHead g F s ra t
    else if l = ".LB.plan.14" then SourceDone g F s ra t ∧ g.m = 0#64
    else if l = ".LB.plan.9" then ∃ lo, Bd g F s ra lo t ∧ rdx t = -2#64
    else False

def V (g : G) (l : Label) (t : MachineData) : Nat :=
  if l = Names.plan then 10000
  else if l = ".LB.plan.0" then 6000 + 2 * (g.m.toNat - (rax t).toNat)
  else if l = ".LB.plan.1" then 6001 + 2 * (g.m.toNat - (rax t).toNat)
  else if l = ".LB.plan.2" ∨ l = ".LB.plan.14" then 4000
  else if l = ".LB.plan.3" then 100 + 2 * (g.n.toNat - (rax t).toNat)
  else if l = ".LB.plan.4" then 101 + 2 * (g.n.toNat - (rax t).toNat)
  else 0

def E (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) : Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ Post g F s t ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, Inv g F s ra blk.label t →
    let I' (l : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv g F s ra l u ∧ Program.Decreases (V g) blk.label blk.idx t l j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept planAsm.labels (s.pushRa ra) I' (E g F s ra)) t

end Bbu.Unit.EntryRejectIds
