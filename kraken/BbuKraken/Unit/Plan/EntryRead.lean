module

public import BbuKraken.Unit.Plan.EntryFrame
import all BbuKraken.Unit.Plan.EntryFrame

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

structure SlotRead (m : Mem 64) (a : Addr) (w : Word) : Prop where
  payloadSome : (m.loadInt a 4).isSome = true
  kindSome : (m.loadInt (a + 4#64) 1).isSome = true
  opcodeSome : (m.loadInt (a + 5#64) 1).isSome = true
  payload : BitVec.ofInt 32 (m.loadInt a 4).get! = w.extractLsb' 0 32
  kind : rdb m (a + 4#64) = w.extractLsb' 32 8
  opcode : rdb m (a + 5#64) = w.extractLsb' 40 8

theorem slot_read {m : Mem 64} {a : Addr} {words : List Word} {F : MProp 64}
    (h : (Arr a words ∗ F).get m) {i : Nat} (hi : i < words.length) :
    SlotRead m (slotAt a i) words[i] := by
  obtain ⟨R, he⟩ := Arr.focus a words hi
  rw [he, MProp.sep_assoc] at h
  have k4 := Wd.isSome_byte h (j := 4) (by decide)
  have k5 := Wd.isSome_byte h (j := 5) (by decide)
  have h4 := Wd.rdb_byte h (j := 4) (by decide)
  have h5 := Wd.rdb_byte h (j := 5) (by decide)
  rw [Wd.split, MProp.sep_assoc] at h
  exact ⟨B32.isSome h, k4, k5, EntryU.b32_read h, h4, h5⟩

theorem Bd.sourceRead {g : EG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo locals : List Word} (h : Bd g F s ra lo locals t) (hok : g.Ok)
    {i : Word} (hi : i < g.r.p.m) :
    SlotRead t.dmem (slotAt g.r.p.src i.toNat)
      (g.r.p.sw[i.toNat]'(hok.sw ▸ BitVec.lt_def.mp hi)) := by
  obtain ⟨R, he⟩ : ∃ R, View (rsp s) g ∗
      (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F) = Arr g.r.p.src g.r.p.sw ∗ R :=
    ⟨_, by unfold View Buffers; ecancel⟩
  exact slot_read (he ▸ h.mem) (hok.sw ▸ BitVec.lt_def.mp hi)

theorem Bd.targetRead {g : EG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo locals : List Word} (h : Bd g F s ra lo locals t) (hok : g.Ok)
    {i : Word} (hi : i < g.r.p.n) :
    SlotRead t.dmem (slotAt g.r.p.tgt i.toNat)
      (g.r.p.tw[i.toNat]'(hok.tw ▸ BitVec.lt_def.mp hi)) := by
  obtain ⟨R, he⟩ : ∃ R, View (rsp s) g ∗
      (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F) = Arr g.r.p.tgt g.r.p.tw ∗ R :=
    ⟨_, by unfold View Buffers; ecancel⟩
  exact slot_read (he ▸ h.mem) (hok.tw ▸ BitVec.lt_def.mp hi)

end Bbu.Unit.EntryValidU
