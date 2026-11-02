module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionDefs
import all FlatShuffler.Unit.Plan.PlannerRunEmissionDefs

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

def setLocalWords (locals : List Word) (xs : List (Nat × Word)) : List Word :=
  xs.foldl (fun a p => a.set p.1 p.2) locals

def storeLocalWords (m : Mem 64) (sp : Addr) (xs : List (Nat × Word)) : Mem 64 :=
  xs.foldl (fun a p => a.storeInt (sp + BitVec.ofNat 64 (8 * p.1)) 8 p.2.toInt) m

def headerWrites (g : PlannerCallMemory) : List (Nat × Word) :=
  [(2060, g.p.tgt), (2061, g.p.targetSize), (2062, g.p.spl), (2063, g.dataPtr),
    (2064, g.p.sourceSize), (2065, g.opsPtr), (2066, 0#64)]

def headerLocals (g : PlannerCallMemory) (locals : List Word) : List Word :=
  setLocalWords locals (headerWrites g)

section
variable {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {lo locals : List Word}

theorem AttemptLI.storeWords (h : AttemptLI P g M F s ra lo locals t) (hok : g.Ok)
    (xs : List (Nat × Word)) (hx : ∀ p ∈ xs, 2060 ≤ p.1 ∧ p.1 < 4121) :
    AttemptLI P g M F s ra lo (setLocalWords locals xs)
      { t with dmem := storeLocalWords t.dmem t.regs.rsp.toBitVec xs } := by
  induction xs generalizing locals t with
  | nil => exact h.next rfl rfl rfl rfl rfl rfl rfl rfl
  | cons p xs ih =>
    have hp := hx p List.mem_cons_self
    have h1 := h.storeLocal hok hp.2 hp.1 p.2
      (u := {t with
        dmem := t.dmem.storeInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * p.1)) 8 p.2.toInt})
      rfl rfl rfl rfl rfl rfl rfl rfl
    exact ih h1 (fun q hq => hx q (List.mem_cons_of_mem p hq))

theorem headerWrites.bounds (g : PlannerCallMemory) :
    ∀ p ∈ headerWrites g, 2060 ≤ p.1 ∧ p.1 < 4121 := by
  intro p hp
  simp only [headerWrites, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

theorem AttemptLI.headerSome (h : AttemptLI P g M F s ra lo locals t) (hok : g.Ok)
    (i : Nat) (hi : i < 7) :
    ((storeLocalWords t.dmem t.regs.rsp.toBitVec ((headerWrites g).take i)).loadInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (2060 + i))) 8).isSome = true := by
  have hh := h.storeWords hok ((headerWrites g).take i)
    (fun p hp => headerWrites.bounds g p (List.mem_of_mem_take hp))
  exact hh.localSome (by omega)

theorem AttemptLI.headerOpsSome (h : AttemptLI P g M F s ra lo locals t) (hok : g.Ok) :
    ((storeLocalWords t.dmem t.regs.rsp.toBitVec ((headerWrites g).take 5)).loadInt
      (t.regs.rsp.toBitVec + 8#64) 8).isSome = true := by
  have hh := h.storeWords hok ((headerWrites g).take 5)
    (fun p hp => headerWrites.bounds g p (List.mem_of_mem_take hp))
  exact hh.localSome (i := 1) (by decide)

theorem AttemptLI.headerOpsRead (h : AttemptLI P g M F s ra lo locals t) (hok : g.Ok) :
    rd (storeLocalWords t.dmem t.regs.rsp.toBitVec ((headerWrites g).take 5))
      (t.regs.rsp.toBitVec + 8#64) = g.opsPtr := by
  have hh := h.storeWords hok ((headerWrites g).take 5)
    (fun p hp => headerWrites.bounds g p (List.mem_of_mem_take hp))
  exact hh.toLoopLI.opsRead

theorem AttemptLI.headerSetup (h : AttemptLI P g M F s ra lo locals t) (hok : g.Ok) :
    EmitLI P g M F s ra lo (headerLocals g locals)
      { t with dmem := storeLocalWords t.dmem t.regs.rsp.toBitVec (headerWrites g) } := by
  refine ⟨h.storeWords hok _ (headerWrites.bounds g), ?_⟩
  simp [CtorHeader, headerLocals, headerWrites, setLocalWords, h.localLength]

end
end FlatShuffler.Unit.PlannerRunU
