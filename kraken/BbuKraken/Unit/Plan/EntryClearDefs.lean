module

public import BbuKraken.Unit.Plan.EntryFrame
import all BbuKraken.Unit.Plan.EntryFrame

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

def withDropped (g : EG) (d : Vector (BitVec 8) MAX_N) : EG :=
  {g with r := {g.r with dropped := d}}

structure ClearLI (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends Bd g F s ra lo locals t where
  rdi : t.regs.rdi.toBitVec = g.r.p.m
  rsi : t.regs.rsi.toBitVec = g.r.p.n
  rdx : t.regs.rdx.toBitVec = g.r.p.src
  rcx : t.regs.rcx.toBitVec = g.r.p.tgt
  r8 : t.regs.r8.toBitVec = g.r.p.spl
  rbx : t.regs.rbx.toBitVec = g.allowed.setWidth 64
  r11 : t.regs.r11.toBitVec = g.strategy.setWidth 64

theorem LI.toClearLI {g F s ra lo locals t} (h : LI g F s ra lo locals t) :
    ClearLI g F s ra lo locals t :=
  ⟨h.toBd, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.rbx, h.r11⟩

section
variable {g : EG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo locals : List Word}

theorem ClearLI.next (h : ClearLI g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15)
    (hdi : u.regs.rdi = t.regs.rdi) (hsi : u.regs.rsi = t.regs.rsi)
    (hdx : u.regs.rdx = t.regs.rdx) (hcx : u.regs.rcx = t.regs.rcx)
    (h8 : u.regs.r8 = t.regs.r8)
    (hbx : u.regs.rbx = t.regs.rbx) (h11 : u.regs.r11 = t.regs.r11) :
    ClearLI g F s ra lo locals u :=
  ⟨h.toBd.next hm hsp hbp h12 h13 h14 h15,
    hdi ▸ h.rdi, hsi ▸ h.rsi, hdx ▸ h.rdx, hcx ▸ h.rcx,
    h8 ▸ h.r8, hbx ▸ h.rbx, h11 ▸ h.r11⟩

theorem ClearLI.storeDropped (h : ClearLI g F s ra lo locals t)
    {i : Word} (hi : i.toNat < MAX_N) (hmn : i.toNat < g.r.p.m.toNat) (z : Int)
    (hm : u.dmem = t.dmem.storeInt (g.r.p.drp + i) 1 z)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15)
    (hdi : u.regs.rdi = t.regs.rdi) (hsi : u.regs.rsi = t.regs.rsi)
    (hdx : u.regs.rdx = t.regs.rdx) (hcx : u.regs.rcx = t.regs.rcx)
    (h8 : u.regs.r8 = t.regs.r8)
    (hbx : u.regs.rbx = t.regs.rbx) (h11 : u.regs.r11 = t.regs.r11) :
    ClearLI (withDropped g (Flat.put g.r.dropped i (BitVec.ofInt 8 z)))
      F s ra lo locals u := by
  obtain ⟨R, he⟩ : ∃ R, ∀ d : Vector (BitVec 8) MAX_N,
      View (rsp s) (withDropped g d) ∗
        (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F) = Bs g.r.p.drp (d.toList.take g.r.p.m.toNat) ∗ R :=
    ⟨_, fun d => by simp only [View, Args, Buffers, withDropped, PlannerRunG.dataCapacity]; ecancel⟩
  have hs := SpillSetProof.Bs.store (x := i) (he g.r.dropped ▸ h.mem)
    (by simp only [List.length_take, Vector.length_toList]; omega) z
  have hm' : (View (rsp s) (withDropped g (Flat.put g.r.dropped i (BitVec.ofInt 8 z))) ∗
      (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F)).get u.dmem := by
    rw [hm, he]
    simpa only [Flat.put, Vector.toList_setIfInBounds, List.take_set] using hs
  exact ⟨⟨⟨(sep_lc _ _ _).symm ▸ hm', hsp ▸ h.kb.sp⟩,
      h.low, h.localLength, hbp.trans h.bp, h12.trans h.r12,
      h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩,
    hdi ▸ h.rdi, hsi ▸ h.rsi, hdx ▸ h.rdx, hcx ▸ h.rcx,
    h8 ▸ h.r8, hbx ▸ h.rbx, h11 ▸ h.r11⟩

end

def ClearHead (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (wanted : Vector (BitVec 8) MAX_N) (t : MachineData) : Prop :=
  ∃ lo locals i, ClearLI g F s ra lo locals t ∧ i < g.r.p.m ∧
    rax t = g.r.p.drp + i ∧ r9 t = g.r.p.drp + g.r.p.m ∧
    Flat.zeroFrom g.r.p.m i g.r.dropped = wanted

def Ready (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, ClearLI g F s ra lo locals t

end Bbu.Unit.EntryValidU
