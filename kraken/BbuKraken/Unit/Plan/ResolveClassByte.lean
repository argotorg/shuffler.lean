module

public import BbuKraken.Unit.Plan.ResolveLoopDefs
import all BbuKraken.Unit.Plan.ResolveLoopDefs

@[expose] public section

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem rdb_storeByte (m : Mem 64) (a : Addr) (z : Int) :
    rdb (m.storeInt a 1 z) a = BitVec.ofInt 8 z := by
  rw [rdb, Mem.loadInt_storeInt _ _ _ _ (by decide), Option.get!_some]
  rw [ofBytes_toBytes, Int.take]
  simp [BitVec.ofInt]

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {lo : List Word} {L : Lc} {w : Work}

theorem Bd.classRead (h : Bd P r F s ra lo L.toList t) :
    rdb t.dmem (t.regs.rsp.toBitVec + 23#64) = L.bestClass := by
  obtain ⟨R, hm⟩ := h.typedWord 2 (by decide)
  have hr := Wd.rdb_byte hm (j := 7) (by decide)
  change rdb t.dmem (t.regs.rsp.toBitVec + 16#64 + 7#64) = L.classWord.extractLsb' 56 8 at hr
  simpa only [Lc.bestClass, Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd] using hr

theorem Bd.classSome (h : Bd P r F s ra lo L.toList t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 23#64) 1).isSome = true := by
  obtain ⟨R, hm⟩ := h.typedWord 2 (by decide)
  have hr := Wd.isSome_byte hm (j := 7) (by decide)
  simpa only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd] using hr

theorem Bd.storeClass (h : Bd P r F s ra lo L.toList t) (z : Int)
    (hm : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 23#64) 1 z)
    (hsp : u.regs.rsp = t.regs.rsp) :
    ∃ v : Word, Bd P r F s ra lo { L with classWord := v }.toList u ∧
      ({ L with classWord := v } : Lc).bestClass = BitVec.ofInt 8 z := by
  obtain ⟨v, hv⟩ := h.storeLocalByte (i := 2) (by simp) (j := 7#64) (by decide) z
    (by simpa only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd] using hm) hsp
  rw [Lc.set_classWord] at hv
  have hr := hv.classRead
  rw [hsp, hm, rdb_storeByte] at hr
  exact ⟨v, hv, hr.symm⟩

theorem Core.withClass (h : Core P r F s ra w lo L t) {v : Word}
    (hb : Bd P (w.ghost r) F s ra lo { L with classWord := v }.toList u)
    (hsp : u.regs.rsp = t.regs.rsp) (h12 : u.regs.r12 = t.regs.r12)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13) :
    Core P r F s ra w lo { L with classWord := v } u :=
  ⟨hb, h.candidates, h.droppedNow, h.count, h.pass, h.excess, h.ok,
    h12 ▸ h.r12, h14 ▸ h.r14, by rw [h13, hsp]; exact h.r13⟩

theorem Core.withPending (h : Core P r F s ra w lo L t) {v : Word}
    (hb : Bd P (w.ghost r) F s ra lo { L with pending := v }.toList u)
    (hsp : u.regs.rsp = t.regs.rsp) (h12 : u.regs.r12 = t.regs.r12)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13) :
    Core P r F s ra w lo { L with pending := v } u :=
  ⟨hb, h.candidates, h.droppedNow, h.count, h.pass, h.excess, h.ok,
    h12 ▸ h.r12, h14 ▸ h.r14, by rw [h13, hsp]; exact h.r13⟩

end
end Bbu.Unit.ResolveU
