module

public import BbuKraken.Unit.Plan.ClassifyInitFrame
import all BbuKraken.Unit.Plan.ClassifyInitFrame

@[expose] public section

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

def prologueBase (s : MachineData) (ra : Int64) : Word :=
  (s.pushRa ra).regs.rsp.toBitVec - 56#64

def prologueState (s : MachineData) (ra : Int64) : MachineData :=
  { s.pushRa ra with
    regs := { (s.pushRa ra).regs with rsp := ⟨prologueBase s ra⟩ },
    dmem := pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec
      (pushRegs (s.pushRa ra)) }

def prologuePayload (s : MachineData) (ra : Int64) (x : BitVec 32) : MachineData :=
  { prologueState s ra with
    dmem := (prologueState s ra).dmem.storeInt (prologueBase s ra + 4#64) 4 x.toInt }

def prologueScratch (s : MachineData) (ra : Int64) (x : BitVec 32) (o : BitVec 8) :
    MachineData :=
  { prologueState s ra with
    dmem := (prologuePayload s ra x).dmem.storeInt (prologueBase s ra + 3#64) 1 o.toInt }

theorem prologue_frame {P : Addr} {c : CG} {F : MProp 64}
    {s : MachineData} {ra : Int64} {xs : List Word} (hl : xs.length = 16)
    (hk : Kg (CView P c ∗ F) s ra xs (s.pushRa ra)) :
    ∃ lo w q, PushOk (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec
        (pushRegs (s.pushRa ra)) ∧
      Bd P c F s ra lo w q (prologueState s ra) ∧
      Bd P c F s ra lo w ((inp c s).slot.payload ++ q.extractLsb' 0 32)
        (prologuePayload s ra (inp c s).slot.payload) ∧
      Bd P c F s ra lo w
        ((inp c s).slot.payload ++ (inp c s).slot.valueOpcode ++ q.extractLsb' 0 24)
        (prologueScratch s ra (inp c s).slot.payload (inp c s).slot.valueOpcode) := by
  obtain ⟨lo, w, q, a, b, d, e, f, g, hxs, hlo⟩ := split_frame hl
  subst xs
  obtain ⟨hps, hm⟩ := init_frame hlo hk
  have hb : Bd P c F s ra lo w q (prologueState s ra) := ⟨⟨hm, rfl⟩, hlo⟩
  have hmem1 := Stk.storeHi32 hb.kb.mem (a := prologueBase s ra) rfl
    (inp c s).slot.payload
  have hb1 : Bd P c F s ra lo w ((inp c s).slot.payload ++ q.extractLsb' 0 32)
      (prologuePayload s ra (inp c s).slot.payload) := ⟨⟨hmem1, rfl⟩, hlo⟩
  have hmem2 := Stk.store34 hb.kb.mem (a := prologueBase s ra) rfl
    (inp c s).slot.payload (inp c s).slot.valueOpcode
  have hb2 : Bd P c F s ra lo w
      ((inp c s).slot.payload ++ (inp c s).slot.valueOpcode ++ q.extractLsb' 0 24)
      (prologueScratch s ra (inp c s).slot.payload (inp c s).slot.valueOpcode) :=
    ⟨⟨hmem2, rfl⟩, hlo⟩
  exact ⟨lo, w, q, hps, hb, hb1, hb2⟩

section
variable {P : Addr} {c : CG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo : List Word} {w q : Word}

theorem prologue_return (h : Bd P c F s ra lo w q t)
    (hr : (rdx t).setWidth 8 = (inp c s).eval) :
    Inv P c F s ra (.label ".LB.Planner.classify.8") t := by
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
  exact ⟨lo, w, q, h, hr⟩

theorem prologue_generated (h : LI P c F s ra lo w q t)
    (hr : (inp c s).eval = (inp c s).generated) :
    Inv P c F s ra (.label ".LB.Planner.classify.0") t := by
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
  exact ⟨lo, w, q, h, hr⟩

theorem prologue_free (h : LI P c F s ra lo w q t)
    (hr : (inp c s).eval = (inp c s).generated) (hf : (inp c s).free = true)
    (hsi : rsi t = c.h.mp) (hcx : rcx t = rcx s) :
    Inv P c F s ra (.label ".LB.Planner.classify.6") t := by
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
  exact ⟨⟨lo, w, q, h, hr, hf⟩, hsi, hcx⟩

theorem prologue_copied (h : LI P c F s ra lo w q t)
    (hf : (inp c s).free = false) (hsi : rsi t = c.h.mp)
    (hcx : (rcx t).setWidth 32 = (inp c s).slot.payload) :
    Inv P c F s ra (.label ".LB.Planner.classify.4") t := by
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
  exact ⟨⟨lo, w, q, h, hf⟩, hsi, hcx⟩

end

end Bbu.Unit.ClassifyU
