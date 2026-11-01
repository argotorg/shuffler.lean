module

public import Init.Data.Fin.Lemmas
import all Init.Data.Fin.Lemmas
public import BbuKraken.Unit.Plan.EntryCall
import all BbuKraken.Unit.Plan.EntryCall
public import BbuKraken.Unit.Plan.EntryOutput
import all BbuKraken.Unit.Plan.EntryOutput

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

theorem Bd.storeLocalLowByte {g : EG} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}
    (h : Bd g F s ra lo locals t) {i : Nat} (hi : i < 10) (v : BitVec 8)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 1 v.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) :
    Bd g F s ra lo
      (locals.set i ((locals[i]'(h.localLength ▸ hi)).extractLsb' 8 56 ++ v)) u := by
  obtain ⟨R, e⟩ := h.localFocus
  obtain ⟨Q, he, hs⟩ := ResolveU.Arr_focus_set
    t.regs.rsp.toBitVec locals (h.localLength ▸ hi)
  have hm0 := e locals h.localLength ▸ h.kb.mem
  rw [he, MProp.sep_assoc] at hm0
  have hm1 := PlannerRunU.word_storeLowByte hm0 v.toInt
  have hl : (locals.set i
      ((locals[i]'(h.localLength ▸ hi)).extractLsb' 8 56 ++ v)).length = 10 := by
    simp [h.localLength]
  refine ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, hl, hbp.trans h.bp,
    h12.trans h.r12, h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩
  rw [hm, e _ hl, hs, MProp.sep_assoc]
  simpa only [BitVec.ofInt_toInt] using hm1

inductive EntryWrite where
  | word (i : Fin 10) (v : Word)
  | byte (i : Fin 10) (v : BitVec 8)

def EntryWrite.locals (locals : List Word) : EntryWrite → List Word
  | .word i v => locals.set i.val v
  | .byte i v => locals.set i.val ((locals[i.val]?.getD 0#64).extractLsb' 8 56 ++ v)

def EntryWrite.mem (m : Mem 64) (sp : Addr) : EntryWrite → Mem 64
  | .word i v => m.storeInt (sp + BitVec.ofNat 64 (8 * i.val)) 8 v.toInt
  | .byte i v => m.storeInt (sp + BitVec.ofNat 64 (8 * i.val)) 1 v.toInt

def entryStores (g : EG) : List EntryWrite :=
  [.word ⟨2, by decide⟩ g.r.p.src, .word ⟨3, by decide⟩ g.r.p.m,
    .word ⟨4, by decide⟩ g.r.p.tgt, .word ⟨5, by decide⟩ g.r.p.n,
    .word ⟨6, by decide⟩ g.r.p.spl, .byte ⟨7, by decide⟩ g.r.p.allowed,
    .word ⟨8, by decide⟩ g.r.p.drp, .word ⟨1, by decide⟩ 0#64]

def entrySetLocals (locals : List Word) (ws : List EntryWrite) : List Word :=
  ws.foldl EntryWrite.locals locals

def entryStoreMem (m : Mem 64) (sp : Addr) (ws : List EntryWrite) : Mem 64 :=
  ws.foldl (fun m w => w.mem m sp) m

theorem Bd.entryStores {g : EG} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {lo locals : List Word}
    (h : Bd g F s ra lo locals t) (ws : List EntryWrite) :
    Bd g F s ra lo (entrySetLocals locals ws)
      {t with dmem := entryStoreMem t.dmem t.regs.rsp.toBitVec ws} := by
  induction ws generalizing locals t with
  | nil => exact h.next rfl rfl rfl rfl rfl rfl rfl
  | cons w ws ih =>
    have h1 : Bd g F s ra lo (w.locals locals)
        {t with dmem := w.mem t.dmem t.regs.rsp.toBitVec} := by
      cases w with
      | word i v => exact h.storeLocal i.isLt v rfl rfl rfl rfl rfl rfl rfl
      | byte i v =>
        have hi : i.val < locals.length := by rw [h.localLength]; exact i.isLt
        have hs := h.storeLocalLowByte i.isLt v
          (u := {t with dmem := (EntryWrite.byte i v).mem t.dmem t.regs.rsp.toBitVec})
          rfl rfl rfl rfl rfl rfl rfl
        simpa only [EntryWrite.locals, List.getElem?_eq_getElem hi, Option.getD_some] using hs
    exact ih h1

private theorem pack_word (w : Word) : w.extractLsb' 8 56 ++ w.setWidth 8 = w := by bv_decide

theorem entrySetLocals_layout (g : EG) (hc : g.r.count = 0#64)
    (locals : List Word) (hl : locals.length = 10) :
    ∃ (l : CallLocals) (saw : BitVec 8), entrySetLocals locals (entryStores g) =
      l.toList (PlannerRunU.withSaw g.r saw) := by
  match locals, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9], _ =>
    refine ⟨⟨w0, w7.extractLsb' 8 56, w9.extractLsb' 8 56⟩, w9.setWidth 8, ?_⟩
    dsimp only [entrySetLocals, entryStores, EntryWrite.locals, List.foldl_cons,
      List.foldl_nil, CallLocals.toList, PlannerRunU.withSaw]
    simp [hc, pack_word]

end Bbu.Unit.EntryValidU
