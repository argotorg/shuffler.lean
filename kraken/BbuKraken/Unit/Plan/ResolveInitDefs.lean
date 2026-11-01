module

public import BbuKraken.Unit.Plan.ResolveInitFrame
import all BbuKraken.Unit.Plan.ResolveInitFrame
public import BbuKraken.Unit.Plan.ResolveInitModel
import all BbuKraken.Unit.Plan.ResolveInitModel
public import BbuKraken.Unit.Plan.ResolveLoopDefs
import all BbuKraken.Unit.Plan.ResolveLoopDefs

@[expose] public section

namespace Bbu.Unit.ResolveU
open Bbu.Sep

structure CandidateState (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo : List Word) (L : Lc) (u0 : Flat.ResolveU) (count : Word) (t : MachineData) : Prop where
  bd : Bd P r F s ra lo L.toList t
  excess : L.excess = rcx s
  r12 : t.regs.r12.toBitVec = r.mp
  r14 : t.regs.r14.toBitVec = P
  r8 : r8 t = r.currentPtr
  r9 : r9 t = r9 s
  countBound : count.toNat ≤ MAX_N
  bounded : CandidatesBound r.p.m L.candidates count
  live : CandidatesLive r.M L.candidates count
  zero : ∀ q : Word, q < r.p.m → Flat.get L.droppedNow q = 0#8
  droppedNow : u0.droppedNow = L.droppedNow

def candidateStart (r : RG) (s : MachineData) (u : Flat.ResolveU) :=
  Flat.candidatesFrom r.M r.current (r9 s) (rdx s + 1#64) u.candidates 0#64

def Scan (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (after : Bool) (t : MachineData) : Prop :=
  ∃ lo L u0 count,
    CandidateState P r F s ra lo L u0 count t ∧ t.regs.rbp.toBitVec = count ∧
    rdx t < r9 s ∧
    let next := if after then rdx t + 1#64 else rdx t
    count ≤ next ∧ next.toNat ≤ MAX_N ∧
    candidateStart r s u0 =
      Flat.candidatesFrom r.M r.current (r9 s) next L.candidates count

def CandidatesDone (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (setCount : Bool) (t : MachineData) : Prop :=
  ∃ lo L u0 count,
    CandidateState P r F s ra lo L u0 count t ∧
    (if setCount then t.regs.rbp.toBitVec = count else count = 0#64) ∧
    candidateStart r s u0 = some (L.candidates, count)

def initPhase (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (l : Label) (t : MachineData) : Prop :=
  if l = ".LB.Planner.resolve.4" then Scan P r F s ra true t
  else if l = ".LB.Planner.resolve.5" then Scan P r F s ra false t
  else if l = ".LB.Planner.resolve.6" then CandidatesDone P r F s ra false t
  else if l = ".LB.Planner.resolve.7" then CandidatesDone P r F s ra true t
  else rest l t

def initVar (s : MachineData) (rest : Label → MachineData → Nat)
    (l : Label) (t : MachineData) : Nat :=
  if l = Names.resolve then 67120000
  else if l = ".LB.Planner.resolve.1" then 67113864
  else if l = ".LB.Planner.resolve.4" then 67108864 + 4 * (r9 s - rdx t).toNat + 2
  else if l = ".LB.Planner.resolve.5" then 67108864 + 4 * (r9 s - rdx t).toNat + 3
  else if l = ".LB.Planner.resolve.6" then 67108866
  else if l = ".LB.Planner.resolve.7" then 67108865
  else rest l t

def initFullPhase (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) :=
  zphase P r F s ra (InitPayload s) (initPhase P r F s ra rest)

def initFullVar (s : MachineData) (rest : Label → MachineData → Nat) :=
  zvar 67113864 (initVar s rest)

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {lo : List Word} {L : Lc} {u0 : Flat.ResolveU} {count : Word}

theorem CandidateState.next (h : CandidateState P r F s ra lo L u0 count t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
    (h8 : Bbu.r8 u = Bbu.r8 t) (h9 : Bbu.Unit.r9 u = Bbu.Unit.r9 t) :
    CandidateState P r F s ra lo L u0 count u :=
  ⟨h.bd.next hm hsp, h.excess, h12 ▸ h.r12, h14 ▸ h.r14,
    h8 ▸ h.r8, h9 ▸ h.r9, h.countBound, h.bounded, h.live, h.zero, h.droppedNow⟩

theorem CandidateState.model (h : CandidateState P r F s ra lo L u0 count t)
    (hok : r.Ok) (ha : resolveA r s)
    (he : candidateStart r s u0 = some (L.candidates, count)) :
    ∀ u : Flat.ResolveU,
      Flat.resolve r.p.fl r.spills r.dropped r.M (rdx s) (rcx s) r.current (Bbu.Unit.r9 s) u =
        packResult (Flat.passFrom r.p.fl r.M L.candidates count (rcx s) 0#64
          ⟨r.spills, r.dropped, L.droppedNow⟩) := by
  intro u
  rw [resolve_independent r hok s ha u u0]
  change Flat.candidatesFrom r.M r.current (Bbu.Unit.r9 s) (rdx s + 1)
    u0.candidates 0 = some (L.candidates, count) at he
  have hz : Flat.zeroFrom r.p.fl.m 0 u0.droppedNow = L.droppedNow := by
    rw [h.droppedNow]
    exact zeroFrom_fixed r.p.m 0 L.droppedNow hok.planner.m h.zero
  rw [Flat.resolve, he]
  simp only [hz]
  rfl

end
end Bbu.Unit.ResolveU
