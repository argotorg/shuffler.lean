module

public import FlatShuffler.Unit.Plan.ResolveLocals
import all FlatShuffler.Unit.Plan.ResolveLocals
public import FlatShuffler.Unit.Plan.ResolvePickModel
import all FlatShuffler.Unit.Plan.ResolvePickModel
public import FlatShuffler.Unit.Plan.ResolveZero
import all FlatShuffler.Unit.Plan.ResolveZero
public import FlatShuffler.Unit.Plan.ResolveStore
import all FlatShuffler.Unit.Plan.ResolveStore
public import FlatShuffler.Unit.Plan.ResolveLocalRead
import all FlatShuffler.Unit.Plan.ResolveLocalRead

@[expose] public section

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

structure Work where
  spills : BitVec 32 → BitVec 8
  dropped : Vector (BitVec 8) maxStackSize
  droppedNow : Vector (BitVec 8) maxStackSize
  candidates : Vector Word maxStackSize
  count : Word
  pass : Word

def Work.ghost (w : Work) (r : RG) : RG :=
  { r with spills := w.spills, dropped := w.dropped }

def Work.state (w : Work) : Flat.RState := ⟨w.spills, w.dropped, w.droppedNow⟩

def Work.pick (w : Work) (r : RG) : Word × BitVec 8 :=
  picked r.p.fl r.M w.candidates w.count w.state

def packResult (q : Flat.Resolution × Flat.RState) :
    Flat.Resolution × (BitVec 32 → BitVec 8) × Vector (BitVec 8) maxStackSize :=
  (q.1, q.2.spills, q.2.dropped)

def Work.result (w : Work) (r : RG) (s : MachineData) :
    Flat.Resolution × (BitVec 32 → BitVec 8) × Vector (BitVec 8) maxStackSize :=
  packResult (Flat.passFrom r.p.fl r.M w.candidates w.count (rcx s) w.pass w.state)

def Work.Model (w : Work) (r : RG) (s : MachineData) : Prop :=
  ∀ u : Flat.ResolveU,
    Flat.resolve r.p.fl r.spills r.dropped r.M (rdx s) (rcx s) r.current (r9 s) u =
      w.result r s

structure Work.Ok (w : Work) (r : RG) (s : MachineData) : Prop where
  count : w.count.toNat ≤ maxStackSize
  pass : w.pass < rcx s
  bounded : CandidatesBound r.p.sourceSize w.candidates w.count
  live : CandidatesLive r.M w.candidates w.count

structure Core (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (w : Work) (lo : List Word) (L : Lc) (t : MachineData) : Prop where
  bd : Bd P (w.ghost r) F s ra lo L.toList t
  candidates : L.candidates = w.candidates
  droppedNow : L.droppedNow = w.droppedNow
  count : L.count = w.count
  pass : L.pass = w.pass
  excess : L.excess = rcx s
  ok : w.Ok r s
  r12 : t.regs.r12.toBitVec = r.mp
  r14 : t.regs.r14.toBitVec = P
  r13 : t.regs.r13.toBitVec =
    t.regs.rsp.toBitVec + 48#64 + 8#64 * w.count

def Outer (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ w lo L, Core P r F s ra w lo L t ∧ w.Model r s

def PickEq (r : RG) (w : Work) (i best : Word) (cls : BitVec 8) : Prop :=
  w.pick r = Flat.pickFrom r.p.fl w.spills r.M w.droppedNow w.candidates w.count i best cls

structure PickAt (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (w : Work) (lo : List Word) (L : Lc) (i best : Word) (cls : BitVec 8)
    (t : MachineData) : Prop extends Core P r F s ra w lo L t where
  index : i < w.count
  rbx : t.regs.rbx.toBitVec = t.regs.rsp.toBitVec + 48#64 + 8#64 * i
  r15 : t.regs.r15.toBitVec = best
  bestClass : L.bestClass = cls
  bestValid : BestValid r.p.fl w.spills r.M w.droppedNow best cls

def Pick (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ w lo L i best cls, PickAt P r F s ra w lo L i best cls t ∧
    w.Model r s ∧ PickEq r w i best cls

def PickNext (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ w lo L i best cls, PickAt P r F s ra w lo L i best cls t ∧
    w.Model r s ∧ PickEq r w (i + 1) best cls

def PickEnd (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ w lo L, Core P r F s ra w lo L t ∧ w.Model r s ∧
    t.regs.r15.toBitVec = (w.pick r).1 ∧ L.bestClass = (w.pick r).2

def Pending (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ w lo L i best cls, Core P r F s ra w lo L t ∧ i < w.count ∧
    t.regs.rbx.toBitVec = t.regs.rsp.toBitVec + 48#64 + 8#64 * i ∧
    L.pending = best ∧ al t = cls ∧ BestValid r.p.fl w.spills r.M w.droppedNow best cls ∧
    w.Model r s ∧ PickEq r w (i + 1) best cls

def Tie (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ w lo L i best cls, PickAt P r F s ra w lo L i best cls t ∧
    w.Model r s ∧ PickEq r w i best cls ∧ best ≠ Flat.NONE ∧
    t.regs.rbp.toBitVec = Flat.get w.candidates i ∧
    L.pending = Flat.get w.candidates i ∧ (rsi t).setWidth 8 = cls ∧
    Flat.get w.droppedNow (Flat.get w.candidates i) = 0#8 ∧
    Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i) = cls ∧
    cls ≠ Flat.NOCLASS

def loopPhase (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (l : Label) (t : MachineData) : Prop :=
  if l = ".LB.Planner.resolve.7" then Outer P r F s ra t
  else if l = ".LB.Planner.resolve.8" then Tie P r F s ra t
  else if l = ".LB.Planner.resolve.9" then Pending P r F s ra t
  else if l = ".LB.Planner.resolve.10" then PickNext P r F s ra t
  else if l = ".LB.Planner.resolve.11" then Pick P r F s ra t
  else if l = ".LB.Planner.resolve.12" then PickEnd P r F s ra t
  else rest l t

def loopBase (s t : MachineData) : Nat :=
  (rcx s - rd t.dmem (t.regs.rsp.toBitVec + 32#64)).toNat * 32768

def loopVar (s : MachineData) (rest : Label → MachineData → Nat)
    (l : Label) (t : MachineData) : Nat :=
  if l = ".LB.Planner.resolve.7" then loopBase s t + 20000
  else if l = ".LB.Planner.resolve.8" then
    loopBase s t + 2 * (t.regs.r13.toBitVec - t.regs.rbx.toBitVec).toNat + 6
  else if l = ".LB.Planner.resolve.9" then
    loopBase s t + 2 * (t.regs.r13.toBitVec - t.regs.rbx.toBitVec).toNat + 4
  else if l = ".LB.Planner.resolve.10" then
    loopBase s t + 2 * (t.regs.r13.toBitVec - t.regs.rbx.toBitVec).toNat + 2
  else if l = ".LB.Planner.resolve.11" then
    loopBase s t + 2 * (t.regs.r13.toBitVec - t.regs.rbx.toBitVec).toNat + 8
  else if l = ".LB.Planner.resolve.12" then loopBase s t + 8
  else if l = ".LB.Planner.resolve.14" then loopBase s t + 6
  else if l = ".LB.Planner.resolve.13" then loopBase s t + 4
  else rest l t

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {w : Work} {lo : List Word} {L : Lc}

theorem Core.next (h : Core P r F s ra w lo L t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) (h12 : u.regs.r12 = t.regs.r12)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13) :
    Core P r F s ra w lo L u :=
  ⟨h.bd.next hm hsp, h.candidates, h.droppedNow, h.count, h.pass, h.excess, h.ok,
    h12 ▸ h.r12, h14 ▸ h.r14, by rw [h13, hsp]; exact h.r13⟩

theorem Core.base (h : Core P r F s ra w lo L t) :
    loopBase s t = (rcx s - w.pass).toNat * 32768 := by
  obtain ⟨R, hm⟩ := h.bd.typedWord 4 (by decide)
  have hr := Wd.rd hm
  change rd t.dmem (t.regs.rsp.toBitVec + 32#64) = L.pass at hr
  rw [loopBase, hr, h.pass]

end

end FlatShuffler.Unit.ResolveU
