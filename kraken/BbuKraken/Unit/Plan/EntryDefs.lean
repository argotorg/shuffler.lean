module

public import BbuKraken.Unit.Plan.EntryModel
import all BbuKraken.Unit.Plan.EntryModel
public import BbuKraken.Unit.Plan.EntryReject
import all BbuKraken.Unit.Plan.EntryReject
public import BbuKraken.Unit.Plan.Call
import all BbuKraken.Unit.Plan.Call

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

structure EG where
  r : PlannerRunG
  idCount : Word
  allowed : BitVec 32
  strategy : BitVec 32
  sawPtr : Addr
  saw : BitVec 8

structure EG.Ok (g : EG) : Prop where
  sw : g.r.p.sw.length = g.r.p.m.toNat
  tw : g.r.p.tw.length = g.r.p.n.toNat
  ids : g.r.spillCount = Flat.ids g.idCount
  ops : g.r.ops.length = 6 * g.r.p.n.toNat + 4 * g.r.p.m.toNat
  traceLength : g.r.traceLength ≤ g.r.ops.length

def Buffers (g : EG) : MProp 64 :=
  Arr g.r.p.src g.r.p.sw ∗ Arr g.r.p.tgt g.r.p.tw ∗
    Spl g.r.p.spl g.r.spills (List.range g.r.spillCount) ∗
    Bs g.r.p.drp (g.r.dropped.toList.take g.r.p.m.toNat) ∗
    Arr g.r.dataPtr (g.r.data.toList.take g.r.dataCapacity) ∗
    Ops g.r.opsPtr 0 g.r.ops ∗
    Arr g.r.sourcesPtr (g.r.sources.toList.take g.r.p.n.toNat) ∗ B8 g.sawPtr g.saw

def Args (S : Addr) (g : EG) : MProp 64 :=
  B32 S g.allowed ∗ B32 (S + 8#64) g.strategy ∗
    Wd (S + 16#64) g.r.p.drp ∗ Wd (S + 24#64) g.sawPtr ∗
    Wd (S + 32#64) g.r.dataPtr ∗ Wd (S + 40#64) g.r.opsPtr ∗
    Wd (S + 48#64) g.r.sourcesPtr

def View (S : Addr) (g : EG) : MProp 64 := Args S g ∗ Buffers g

abbrev entryD : Nat := 8252

def Pre (g : EG) (F : MProp 64) (s : MachineData) : Prop :=
  g.Ok ∧ rdi s = g.r.p.m ∧ rsi s = g.r.p.n ∧ rdx s = g.r.p.src ∧
    rcx s = g.r.p.tgt ∧ r8 s = g.r.p.spl ∧ r9 s = g.idCount ∧
    g.r.p.allowed = g.allowed.setWidth 8 ∧ g.r.countPtr = rsp s - 88#64 ∧
    g.r.count = 0#64 ∧ g.r.traceLength = 0 ∧
    StkMem entryD (View (rsp s) g ∗ F) s s.dmem

structure Keep (g g' : EG) : Prop where
  p : g'.r.p = {g.r.p with saw := g'.r.p.saw}
  data : g'.r.dataPtr = g.r.dataPtr
  ops : g'.r.opsPtr = g.r.opsPtr
  sources : g'.r.sourcesPtr = g.r.sourcesPtr
  count : g'.r.countPtr = g.r.countPtr
  ids : g'.r.spillCount = g.r.spillCount
  idCount : g'.idCount = g.idCount
  allowed : g'.allowed = g.allowed
  strategy : g'.strategy = g.strategy
  sawPtr : g'.sawPtr = g.sawPtr

def model (g : EG) (us : Nat → Flat.RunU) : Word × Option (Flat.Status × Flat.PSt) :=
  Flat.planEntry g.r.p.m g.r.p.n g.r.p.fl.source g.r.p.fl.target g.r.spills
    g.idCount (g.allowed.setWidth 8) (g.strategy.setWidth 8) g.r.dropped
    (g.r.data.map StackSlot.ofWord) g.r.sources us

def ResultWord (g g' : EG) (w : Word) : Prop :=
  ∃ us, let r := model g us
    w = r.1 ∧
      match r.2 with
      | none => g' = g
      | some (st, state) => Keep g g' ∧ g'.r.state = state ∧
          if st = .assertionFailed then g'.saw = g.saw
          else (g'.saw != 0#8) = state.saw

def Result (g g' : EG) (t : MachineData) : Prop := ResultWord g g' (rax t)

def Post (g : EG) (F : MProp 64) (s t : MachineData) : Prop :=
  ∃ g', g'.Ok ∧ Result g g' t ∧ StkMem entryD (View (rsp s) g' ∗ F) s t.dmem

def fr (s : MachineData) (lo locals : List Word) : List Word :=
  lo ++ (locals ++ [s.regs.rbx.toBitVec])

structure Bd (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop where
  kb : Kb (View (rsp s) g ∗ F) s ra (fr s lo locals) 88#64 t
  low : lo.length = 8241
  localLength : locals.length = 10
  bp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

structure LI (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends Bd g F s ra lo locals t where
  rdi : t.regs.rdi.toBitVec = g.r.p.m
  rsi : t.regs.rsi.toBitVec = g.r.p.n
  rdx : t.regs.rdx.toBitVec = g.r.p.src
  rcx : t.regs.rcx.toBitVec = g.r.p.tgt
  r8 : t.regs.r8.toBitVec = g.r.p.spl
  r9 : t.regs.r9.toBitVec = g.idCount
  rbx : t.regs.rbx.toBitVec = g.allowed.setWidth 64
  r11 : t.regs.r11.toBitVec = g.strategy.setWidth 64

def Sizes (g : EG) : Prop :=
  ¬ EntryU.BadArgs g.r.p.m g.r.p.n g.allowed g.strategy

def idsFrom (words : List Word) (idCount : Word) (i : Nat) : Bool :=
  (words.drop i).all (fun w => Flat.idOk idCount (StackSlot.ofWord w))

def SourceHead (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, LI g F s ra lo locals t ∧ rax t < g.r.p.m ∧
    idsFrom g.r.p.sw g.idCount 0 = idsFrom g.r.p.sw g.idCount (rax t).toNat

def SourceNext (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, LI g F s ra lo locals t ∧ rax t < g.r.p.m ∧
    idsFrom g.r.p.sw g.idCount 0 = idsFrom g.r.p.sw g.idCount ((rax t).toNat + 1)

def SourceDone (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, LI g F s ra lo locals t ∧ idsFrom g.r.p.sw g.idCount 0 = true

def TargetHead (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, LI g F s ra lo locals t ∧ rax t < g.r.p.n ∧
    idsFrom g.r.p.sw g.idCount 0 = true ∧
    idsFrom g.r.p.tw g.idCount 0 = idsFrom g.r.p.tw g.idCount (rax t).toNat

def TargetNext (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, LI g F s ra lo locals t ∧ rax t < g.r.p.n ∧
    idsFrom g.r.p.sw g.idCount 0 = true ∧
    idsFrom g.r.p.tw g.idCount 0 = idsFrom g.r.p.tw g.idCount ((rax t).toNat + 1)

def Checked (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, LI g F s ra lo locals t ∧
    idsFrom g.r.p.sw g.idCount 0 = true ∧ idsFrom g.r.p.tw g.idCount 0 = true

end Bbu.Unit.EntryValidU
