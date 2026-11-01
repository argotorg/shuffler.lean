module

public import BbuKraken.Unit.TopFrame
import all BbuKraken.Unit.TopFrame
public import BbuKraken.Kit
import all BbuKraken.Kit

@[expose] public section

/-!
# The result of `build_bottom_up`

The blocks after the call of `buildBottomUp`. `TQ` is the state after the call: the status
`st` and the flat state `fs` of `Flat.buildBottomUp` on the struct of the constructor, the
words of the struct that the blocks read, and the memory facts. `TR` is the state at `.LB.build_bottom_up.17`
(with `rsp` at the struct and the result in `rdx`) and before `ret` (with `rsp` at the return
address and the result in `rax`). `TR.ret` gives the postcondition of the unit.

The blocks `.LB.build_bottom_up.13` (blocked) and `.LB.build_bottom_up.12` (done) store two words to `blocked`. These words are
not in the frame (`disj_frame`) and not in `data` or in the ops buffer (`disj_blk`), so the
loads from the struct and the facts of `FlatMem` stay.
-/

namespace Bbu.Unit
open Bbu.Sep

namespace Top

section
variable (s : MachineData)

-- The struct of the constructor on the inputs in `s`. `u` is the content of the members that
-- the constructor does not initialize.
def topCtor (u : Flat.Uninit) : Flat.St :=
  Flat.ctor (flatData s) (rdi s) (flatTgt s) (rsi s) (flatDest s) (topSpill s) u

-- The result of the flat model on the inputs in `s`.
def topRes (u : Flat.Uninit) : Word × Option Flat.St :=
  Flat.build_bottom_up (rdi s) (rsi s) (flatData s) (flatTgt s) (flatDest s) (topSpill s) u

-- `FlatOut` with the result word `w` in place of `rax`.
def OutW (t : MachineData) (w : Word) (r : Word × Option Flat.St) : Prop :=
  w = r.1 ∧ ∀ fs, r.2 = some fs → r.1 = BitVec.ofNat 64 fs.trace.length → FlatMem s t fs

end

/-! ## The flat result -/

section
variable {s : MachineData} {u : Flat.Uninit}

theorem topRes_ng (hg : ¬TopGuard s) : topRes s u = (-2, none) := by
  have hc : rdi s > rsi s ∨ rsi s > BitVec.ofNat 64 MAX_N := by
    simp only [TopGuard, mArg, nArg, MAX_N] at hg
    simp only [GT.gt, BitVec.lt_def, MAX_N, BitVec.toNat_ofNat]
    omega
  simp only [topRes, Flat.build_bottom_up, hc, ↓reduceIte]

theorem topRes_c (hg : TopGuard s) :
    topRes s u = (let r := Flat.buildBottomUp (topCtor s u)
      match r.1 with
      | .done => (BitVec.ofNat 64 r.2.trace.length,
          some { r.2 with blockedOffset := 0, blockedExcess := 0 })
      | .blocked => (BitVec.ofNat 64 r.2.trace.length, some r.2)
      | .assertionFailed => (-2, some r.2)) := by
  have hc : ¬(rdi s > rsi s ∨ rsi s > BitVec.ofNat 64 MAX_N) := by
    obtain ⟨h1, h2⟩ := hg
    simp only [GT.gt, BitVec.lt_def, MAX_N, BitVec.toNat_ofNat, mArg, nArg] at h1 h2 ⊢
    omega
  simp only [topRes, Flat.build_bottom_up, hc, ↓reduceIte]
  rfl

variable {fs : Flat.St}

theorem topRes_done (hg : TopGuard s) (h : Flat.buildBottomUp (topCtor s u) = (.done, fs)) :
    topRes s u = (BitVec.ofNat 64 fs.trace.length,
      some { fs with blockedOffset := 0, blockedExcess := 0 }) := by
  rw [topRes_c hg, h]

theorem topRes_blocked (hg : TopGuard s) (h : Flat.buildBottomUp (topCtor s u) = (.blocked, fs)) :
    topRes s u = (BitVec.ofNat 64 fs.trace.length, some fs) := by
  rw [topRes_c hg, h]

theorem topRes_fail (hg : TopGuard s)
    (h : Flat.buildBottomUp (topCtor s u) = (.assertionFailed, fs)) :
    topRes s u = (-2, some fs) := by
  rw [topRes_c hg, h]

end

/-! ## The state at `.LB.build_bottom_up.17` and before `ret` -/

-- `sp` is `rsp` and `w` is the result word.
structure TR (s : MachineData) (ra : Int64) (sp w : Word) (t : MachineData) : Prop where
  sp : t.regs.rsp.toBitVec = sp
  ra : t.dmem.loadInt (rsp s - 8#64) 8 = (s.pushRa ra).dmem.loadInt (rsp s - 8#64) 8
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  mapped : Mem.Mapped [frame topF s] t.dmem
  out : Mem.UnchangedOutside (frame topF s :: topOut s) s.dmem t.dmem
  res : ∃ u, OutW s t w (topRes s u)

section
variable {s : MachineData} {ra : Int64} {t u : MachineData} {fs : Flat.St}

theorem flatMem_congr (h : FlatMem s t fs) (e : u.dmem = t.dmem) : FlatMem s u fs := by
  have e1 : topOp s u = topOp s t := by funext i; simp only [topOp, e]
  have e2 : topData s u = topData s t := by funext i; simp only [topData, e]
  exact ⟨e1 ▸ h.ops, e2 ▸ h.data, by rw [e]; exact h.blk0, by rw [e]; exact h.blk1⟩

theorem TR.retAddr {w : Word} (h : TR s ra (rsp s - 8#64) w u) : u.retAddr = some ra := by
  have e : (s.pushRa ra).regs.get64 .rsp = rsp s - 8#64 := by simp [MachineData.pushRa]
  rw [← MachineData.retAddr_pushRa s ra, MachineData.retAddr, MachineData.retAddr, e,
    Reg64s.get64_rsp, h.sp, h.ra]

theorem TR.isSome {w : Word} (h : TR s ra (rsp s - 8#64) w u) : u.retAddr.isSome = true := by
  rw [h.retAddr]; rfl

-- `ret` from a state `u` that holds `TR` with the result in `rax`.
theorem TR.ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    (h : TR s ra (rsp s - 8#64) (rax u) u) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ TopFlatPost s t ∧ (topMod s).Agree s t) u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.rsp.toBitVec + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  have hsp : u.regs.rsp.toBitVec + 8#64 = rsp s := by rw [h.sp]; exact BitVec.sub_add_cancel _ _
  obtain ⟨v, hw, hf⟩ := h.res
  refine Or.inr ⟨⟨by simp [h.retAddr], ⟨h.mapped, v, ?_, fun fs e1 e2 => flatMem_congr (hf fs e1 e2) rfl⟩,
    ⟨fun q hq => ?_, h.out⟩⟩, fun _ _ _ => ?_⟩
  · refine Eq.trans ?_ hw; simp [rax]
  · simp only [Reg64s.get64_set64]
    split
    · next he => subst he; rw [Reg64s.get64_rsp] at *; exact hsp
    · have hb := h.rbx; have hp := h.rbp; have h2 := h.r12; have h3 := h.r13; have h4 := h.r14
      have h5 := h.r15
      cases q <;> simp_all [topMod, Reg64s.get64_rbx, Reg64s.get64_rbp, Reg64s.get64_r12,
        Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15]
  · apply MachineData.stackBelow_of_add_eight
    simp only [MachineData.pushRa, Reg64s.get64_set64, reduceIte]
    rw [hsp]; exact BitVec.sub_add_cancel _ _

-- The return address is in the frame.
theorem ra_in_frame : Mem.Blocks.Inside (rsp s - 8#64) 8 [frame topF s] := by
  simp only [Mem.Blocks.Inside, topF_eq, or_false]; bv_omega

-- `pushRa` changes only the frame.
theorem out_pushRa : Mem.UnchangedOutside (frame topF s :: topOut s) s.dmem (s.pushRa ra).dmem :=
  fun b hb => by
    rw [MachineData.dmem_pushRa]
    exact Mem.Blocks.Inside.get?_storeInt (bs := frame topF s :: topOut s)
      (Or.inl (by simp only [topF_eq, rsp]; bv_omega)) hb _

-- `.LB.build_bottom_up.14`: the guard fails, `rax` is `-2`. The memory, `rsp` and the callee-saved registers
-- are the ones after the call of `build_bottom_up`.
theorem trFail (hp : TopPre s) (hg : ¬TopGuard s) (hm : u.dmem = (s.pushRa ra).dmem)
    (hsp : u.regs.rsp = (s.pushRa ra).regs.rsp)
    (e1 : u.regs.rbx = s.regs.rbx) (e2 : u.regs.rbp = s.regs.rbp) (e3 : u.regs.r12 = s.regs.r12)
    (e4 : u.regs.r13 = s.regs.r13) (e5 : u.regs.r14 = s.regs.r14) (e6 : u.regs.r15 = s.regs.r15)
    (hax : u.regs.rax.toBitVec = -2#64) : TR s ra (rsp s - 8#64) (rax u) u := by
  refine ⟨by rw [hsp]; simp [MachineData.pushRa], by rw [hm], e1, e2, e3, e4, e5, e6,
    hm ▸ frame0 hp, hm ▸ out_pushRa, ⟨u0 s ra, ?_⟩⟩
  rw [topRes_ng hg]
  exact ⟨by simp [rax, Reg64s.get64_rax, hax], fun fs e => by cases e⟩

-- `.LB.build_bottom_up.17`: `movq %rdx,%rax; addq $32872,%rsp`.
theorem TR.ret_17 {w : Word} (h : TR s ra (topS s) w t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = BitVec.ofNat 64 frSub + t.regs.rsp.toBitVec)
    (hax : u.regs.rax.toBitVec = w)
    (e1 : u.regs.rbx = t.regs.rbx) (e2 : u.regs.rbp = t.regs.rbp) (e3 : u.regs.r12 = t.regs.r12)
    (e4 : u.regs.r13 = t.regs.r13) (e5 : u.regs.r14 = t.regs.r14) (e6 : u.regs.r15 = t.regs.r15) :
    TR s ra (rsp s - 8#64) (rax u) u := by
  obtain ⟨v, hw, hf⟩ := h.res
  refine ⟨by rw [hsp, h.sp]; unfold topS frSub offOps; bv_omega, by rw [hu]; exact h.ra, e1.trans h.rbx,
    e2.trans h.rbp, e3.trans h.r12, e4.trans h.r13, e5.trans h.r14, e6.trans h.r15,
    hu ▸ h.mapped, hu ▸ h.out, v, ?_, fun fs e1 e2 => flatMem_congr (hf fs e1 e2) hu⟩
  refine Eq.trans ?_ hw; simp [rax, Reg64s.get64_rax, hax]

end

end Top

end Bbu.Unit
