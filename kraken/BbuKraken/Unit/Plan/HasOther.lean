module

public import BbuKraken.Unit.Plan.Call
import all BbuKraken.Unit.Plan.Call
public import BbuKraken.Unit.Plan.IsRetained
import all BbuKraken.Unit.Plan.IsRetained
public import BbuKraken.Unit.ShallowestCopy
import all BbuKraken.Unit.ShallowestCopy
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-!
# `Planner::hasOtherRetainedCopy`

`Names.hasOtherRetainedCopy` in `build/kraken/c/build_bottom_up.S`: if `m = 0` it returns `false` at once. Else it pushes
`r15` … `rbx`, keeps the bytes `_droppedNow` (`rdx`) in the word at `rsp` and runs the loop over
the sources `rbx < m`. `r12` is `m`, `r13` the planner, `rbp` the offset, `r14` the offset times 8
and `r15` the `Mapping`. Each turn of the loop is one unfold of `Flat.otherFrom`, with a call of
`isRetained`. The frame is the return slot of `isRetained`, the word of `_droppedNow` and the
saved `rbx`, `rbp`, `r12` … `r15`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

/-! ## `Planner` -/

-- The members of a `Planner` and the words that `m_source` and `m_target` point to.
structure PG where
  src : Addr
  m : Word
  tgt : Addr
  n : Word
  spl : Addr
  allowed : BitVec 8
  drp : Addr
  saw : BitVec 8
  sw : List Word
  tw : List Word

structure PG.Ok (p : PG) : Prop where
  m : p.m.toNat ≤ MAX_N
  n : p.n.toNat ≤ MAX_N
  sw : p.sw.length = p.m.toNat
  tw : p.tw.length = p.n.toNat

def PView (P : Addr) (p : PG) : MProp 64 :=
  Wd P p.src ∗ Wd (P + 8#64) p.m ∗ Wd (P + 16#64) p.tgt ∗ Wd (P + 24#64) p.n
    ∗ Wd (P + 32#64) p.spl ∗ B8 (P + 40#64) p.allowed ∗ Wd (P + 48#64) p.drp ∗ B8 (P + 56#64) p.saw
    ∗ Arr p.src p.sw ∗ Arr p.tgt p.tw

-- The flat `Planner`.
def PG.fl (p : PG) : Flat.Planner :=
  ⟨vec (p.sw.map StackSlot.ofWord), p.m, vec (p.tw.map StackSlot.ofWord), p.n, p.allowed != 0#8⟩

section
variable {P : Addr} {p : PG} {F : MProp 64} {m : Mem 64} {i : Word}

theorem PView.rd_src (h : (PView P p ∗ F).get m) : rd m P = p.src :=
  rd_of_eq h (by unfold PView; ecancel)
theorem PView.isSome_src (h : (PView P p ∗ F).get m) : (m.loadInt P 8).isSome = true :=
  isSome_of_eq p.src h (by unfold PView; ecancel)
theorem PView.rd_m (h : (PView P p ∗ F).get m) : rd m (P + 8#64) = p.m :=
  rd_of_eq h (by unfold PView; ecancel)
theorem PView.isSome_m (h : (PView P p ∗ F).get m) : (m.loadInt (P + 8#64) 8).isSome = true :=
  isSome_of_eq p.m h (by unfold PView; ecancel)

theorem PView.arr_src (h : (PView P p ∗ F).get m) : ∃ R, (Arr p.src p.sw ∗ R).get m :=
  ⟨_, (by unfold PView; ecancel : PView P p ∗ F = Arr p.src p.sw ∗ _) ▸ h⟩

theorem PView.isSome_sw (h : (PView P p ∗ F).get m) (hok : p.Ok) (hi : i.toNat < p.m.toNat) :
    (m.loadInt (slotAt p.src i.toNat) 8).isSome = true :=
  let ⟨_, h⟩ := PView.arr_src h; Arr.isSome h (hok.sw ▸ hi)

-- Slot `i < m` of the source.
theorem PView.rd_sw (h : (PView P p ∗ F).get m) (hok : p.Ok) (hi : i.toNat < p.m.toNat) :
    StackSlot.ofWord (rd m (slotAt p.src i.toNat)) = Flat.get p.fl.source i := by
  obtain ⟨_, h⟩ := PView.arr_src h
  have hi' : i.toNat < p.sw.length := hok.sw ▸ hi
  show _ = Flat.get (vec (p.sw.map StackSlot.ofWord)) i
  rw [get_vecL (by simpa using hi') (by simpa [hok.sw] using hok.m), List.getElem_map]
  exact congrArg StackSlot.ofWord (Arr.rd h hi')
end

/-! ## The contract -/

-- The planner, the `Mapping` and the bytes `_droppedNow`.
structure HG where
  p : PG
  mp : Addr
  M : Flat.Mapping
  dn : Addr
  dv : Vector (BitVec 8) MAX_N

def HView (P : Addr) (h : HG) : MProp 64 :=
  PView P h.p ∗ MapM h.mp h.M ∗ Bs h.dn h.dv.toList

def HG.Ok (h : HG) : Prop := h.p.Ok

def hasOtherA (h : HG) (s : MachineData) : Prop :=
  rsi s = h.mp ∧ rdx s = h.dn ∧ (rcx s).toNat < h.p.m.toNat

def hasOtherQ (h h' : HG) (s t : MachineData) : Prop :=
  h' = h ∧ al t = if Flat.hasOtherRetainedCopy h.p.fl h.M h.dv (rcx s) then 1#8 else 0#8

section
variable {P : Addr} {h : HG} {F : MProp 64} {m : Mem 64} {i : Word}

theorem HView.pv (hm : (HView P h ∗ F).get m) : ∃ R, (PView P h.p ∗ R).get m :=
  ⟨_, (by unfold HView; ecancel : HView P h ∗ F = PView P h.p ∗ _) ▸ hm⟩

theorem HView.split (P : Addr) (h : HG) (F : MProp 64) :
    HView P h ∗ F = MapM h.mp h.M ∗ (PView P h.p ∗ Bs h.dn h.dv.toList ∗ F) := by
  unfold HView; ecancel

-- Byte `i` of `_droppedNow`.
theorem HView.rdb_dn (hm : (HView P h ∗ F).get m) (hi : i.toNat < MAX_N) :
    rdb m (h.dn + i) = Flat.get h.dv i := by
  obtain ⟨R, e⟩ : ∃ R, HView P h ∗ F = Bs h.dn h.dv.toList ∗ R := ⟨_, by unfold HView; ecancel⟩
  have := Bs.rdb (e ▸ hm) (by simpa using hi)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [this, get_eq _ hi]
  simp

theorem HView.isSome_dn (hm : (HView P h ∗ F).get m) (hi : i.toNat < MAX_N) :
    (m.loadInt (h.dn + i) 1).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, HView P h ∗ F = Bs h.dn h.dv.toList ∗ R := ⟨_, by unfold HView; ecancel⟩
  have := Bs.isSome (e ▸ hm) (by simpa using hi)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
end

namespace OtherU

/-! ### One turn of the loop -/

section
variable {pl : Flat.Planner} {M : Flat.Mapping} {dn : Vector (BitVec 8) MAX_N} {off o : Word}

theorem from_ge (h : ¬ o < pl.m) : Flat.otherFrom pl M dn off o = false := by
  rw [Flat.otherFrom, dite_eq_right h]

theorem skip_off (h : o < pl.m) (ho : o = off) :
    Flat.otherFrom pl M dn off o = Flat.otherFrom pl M dn off (o + 1) := by
  rw [Flat.otherFrom, dite_eq_left h]
  simp [ho]

theorem skip_slot (h : o < pl.m) (hs : Flat.get pl.source o ≠ Flat.get pl.source off) :
    Flat.otherFrom pl M dn off o = Flat.otherFrom pl M dn off (o + 1) := by
  rw [Flat.otherFrom, dite_eq_left h]
  simp [hs]

theorem skip_ret (h : o < pl.m) (hr : Flat.isRetained M o = false) :
    Flat.otherFrom pl M dn off o = Flat.otherFrom pl M dn off (o + 1) := by
  rw [Flat.otherFrom, dite_eq_left h]
  simp [hr]

theorem skip_dn (h : o < pl.m) (hd : Flat.get dn o ≠ 0#8) :
    Flat.otherFrom pl M dn off o = Flat.otherFrom pl M dn off (o + 1) := by
  rw [Flat.otherFrom, dite_eq_left h]
  simp [hd]

theorem found (h : o < pl.m) (ho : o ≠ off) (hs : Flat.get pl.source o = Flat.get pl.source off)
    (hr : Flat.isRetained M o = true) (hd : Flat.get dn o = 0#8) :
    Flat.otherFrom pl M dn off o = true := by
  rw [Flat.otherFrom, dite_eq_left h]
  simp [ho, hs, hr, hd]
end

/-! ### The registers -/

-- The frame of the body: the return slot of `isRetained`, the word of `_droppedNow`, then the
-- saved `rbx`, `rbp`, `r12` … `r15`.
def fr (s : MachineData) (w : Word) : List Word :=
  w :: [s.regs.rdx.toBitVec, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
    s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]

-- The registers in the loop.
structure LI (P : Addr) (h : HG) (F : MProp 64) (s : MachineData) (ra : Int64) (w : Word)
    (t : MachineData) : Prop where
  kb : Kb (HView P h ∗ F) s ra (fr s w) 56#64 t
  r12 : t.regs.r12.toBitVec = h.p.m
  r13 : t.regs.r13.toBitVec = P
  rbp : t.regs.rbp.toBitVec = rcx s
  r14 : t.regs.r14.toBitVec = rcx s * 8#64
  r15 : t.regs.r15.toBitVec = h.mp

section
variable {P : Addr} {h : HG} {F : MProp 64} {s t t' : MachineData} {ra : Int64} {w : Word}

theorem LI.next (hl : LI P h F s ra w t) (hm : t'.dmem = t.dmem) (hsp : t'.regs.rsp = t.regs.rsp)
    (h12 : t'.regs.r12 = t.regs.r12) (h13 : t'.regs.r13 = t.regs.r13)
    (hbp : t'.regs.rbp = t.regs.rbp) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) : LI P h F s ra w t' :=
  ⟨hl.kb.next hm hsp, by rw [h12]; exact hl.r12, by rw [h13]; exact hl.r13,
    by rw [hbp]; exact hl.rbp, by rw [h14]; exact hl.r14, by rw [h15]; exact hl.r15⟩

theorem LI.stk (hl : LI P h F s ra w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) : t'.StackAtOrBelow (s.pushRa ra) :=
  (hl.kb.next hm hsp).stack (by decide)

-- The state after `isRetained`: it keeps `rbx`, `rbp` and `r12` … `r15`.
theorem LI.after {c : MachineData} {M' : Flat.Mapping} {w' : Word}
    (hag : Sep.mod.Agree c t) (hl : LI P h F s ra w c)
    (hkb : Kb (MapM h.mp M' ∗ (PView P h.p ∗ Bs h.dn h.dv.toList ∗ F)) s ra ([] ++ w' ::
      [s.regs.rdx.toBitVec, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
        s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]) 56#64 t)
    (hM : M' = h.M) : LI P h F s ra w' t ∧ t.regs.rbx = c.regs.rbx := by
  subst hM
  refine ⟨⟨by rw [HView.split]; exact hkb, ?_, ?_, ?_, ?_, ?_⟩,
    mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx⟩
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact hl.r12
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13]; exact hl.r13
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]; exact hl.rbp
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]; exact hl.r14
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]; exact hl.r15
end

/-! ### The pops -/

section
variable {Q : MProp 64} {s t t' : MachineData} {ra : Int64} {w : Word}

theorem popSome (hk : Kb Q s ra (fr s w) 56#64 t) :
    (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec) 8).isSome = true
      ∧ (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + 8#64) 8).isSome = true
      ∧ (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64) 8).isSome = true
      ∧ (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64) 8).isSome = true
      ∧ (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64) 8).isSome = true
      ∧ (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8).isSome
        = true := by
  have hk' : Kb Q s ra ([w] ++ [s.regs.rdx.toBitVec, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec,
      s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec])
      56#64 t := hk
  have := fun (i : Nat) (hi : i < 7) => hk'.isSome_hi rfl (i := i) (by simpa using hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 8#64 + t.regs.rsp.toBitVec = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 1) by
      bv_omega]; exact this 1 (by decide)
  · rw [show 8#64 + t.regs.rsp.toBitVec + 8#64 = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 2) by
      bv_omega]; exact this 2 (by decide)
  · rw [show 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 3) by bv_omega]; exact this 3 (by decide)
  · rw [show 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 4) by bv_omega]; exact this 4 (by decide)
  · rw [show 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 5) by bv_omega]; exact this 5 (by decide)
  · rw [show 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 6) by bv_omega]; exact this 6 (by decide)

-- The state after `addq $8, %rsp` and the pops.
theorem popKg (hk : Kb Q s ra (fr s w) 56#64 t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp.toBitVec
      = 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
    (hbx : t'.regs.rbx.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec))
    (hbp : t'.regs.rbp.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : t'.regs.r12.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64))
    (h13 : t'.regs.r13.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64))
    (h14 : t'.regs.r14.toBitVec
      = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64))
    (h15 : t'.regs.r15.toBitVec
      = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)) :
    Kg Q s ra (fr s w) t' := by
  have hk' : Kb Q s ra ([w] ++ [s.regs.rdx.toBitVec, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec,
      s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec])
      56#64 t := hk
  have hsp0 := hk.sp
  refine hk.kg hm ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (try apply UInt64.toBitVec_inj.mp)
  · rw [hsp]; bv_omega
  · rw [hbx, show 8#64 + t.regs.rsp.toBitVec = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 1) by
      bv_omega]; exact hk'.rd_hi rfl (i := 1) (by simp)
  · rw [hbp, show 8#64 + t.regs.rsp.toBitVec + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 2) by bv_omega]
    exact hk'.rd_hi rfl (i := 2) (by simp)
  · rw [h12, show 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 3) by bv_omega]
    exact hk'.rd_hi rfl (i := 3) (by simp)
  · rw [h13, show 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 4) by bv_omega]
    exact hk'.rd_hi rfl (i := 4) (by simp)
  · rw [h14, show 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 5) by bv_omega]
    exact hk'.rd_hi rfl (i := 5) (by simp)
  · rw [h15, show 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64
      = t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 6) by bv_omega]
    exact hk'.rd_hi rfl (i := 6) (by simp)
end

/-! ### The invariant, the variant and the obligation of a block -/

-- The result of the unit.
abbrev res (h : HG) (s : MachineData) : Bool := Flat.hasOtherRetainedCopy h.p.fl h.M h.dv (rcx s)

def Inv (P : Addr) (h : HG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.hasOtherRetainedCopy then t = s.pushRa ra
    else if l = ".LB.Planner.hasOtherRetainedCopy.0" then
      ∃ w, LI P h F s ra w t ∧ t.regs.rbx.toBitVec.toNat < h.p.m.toNat
      ∧ Flat.otherFrom h.p.fl h.M h.dv (rcx s) (t.regs.rbx.toBitVec + 1#64) = res h s
    else if l = ".LB.Planner.hasOtherRetainedCopy.1" then
      ∃ w, LI P h F s ra w t ∧ t.regs.rbx.toBitVec.toNat < h.p.m.toNat
      ∧ Flat.otherFrom h.p.fl h.M h.dv (rcx s) t.regs.rbx.toBitVec = res h s
    else if l = ".LB.Planner.hasOtherRetainedCopy.2" then
      ∃ w, Kb (HView P h ∗ F) s ra (fr s w) 56#64 t ∧ res h s = false
    else if l = ".LB.Planner.hasOtherRetainedCopy.3" then
      ∃ w, Kb (HView P h ∗ F) s ra (fr s w) 56#64 t ∧ al t = if res h s then 1#8 else 0#8
    else if l = ".LB.Planner.hasOtherRetainedCopy.4" then
      ∃ w, Kb (HView P h ∗ F) s ra (fr s w) 56#64 t ∧ res h s = false
    else False

-- The variant. A turn of the loop decreases `m - rbx`.
def V (h : HG) (l : Label) (t : MachineData) : Nat :=
  if l = Names.hasOtherRetainedCopy then 2 ^ 70
  else if l = ".LB.Planner.hasOtherRetainedCopy.0" then
    2 * (h.p.m.toNat - t.regs.rbx.toBitVec.toNat) - 1
  else if l = ".LB.Planner.hasOtherRetainedCopy.1" then
    2 * (h.p.m.toNat - t.regs.rbx.toBitVec.toNat)
  else if l = ".LB.Planner.hasOtherRetainedCopy.4" then 1
  else 0

def E (P : Addr) (h : HG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost HView HG.Ok P F 8 (fun h' t => hasOtherQ h h' s t) s t
    ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (P : Addr) (h : HG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, Inv P h F s ra blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv P h F s ra c u ∧ Program.Decreases (V h) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels hasOtherRetainedCopyAsm) (s.pushRa ra) I'
        (E P h F s ra)) t

def labels : List CfgLabel :=
  [.entry, .label Names.hasOtherRetainedCopy,
    .label ".LB.Planner.hasOtherRetainedCopy.0",
    .label ".LB.Planner.hasOtherRetainedCopy.1",
    .label ".LB.Planner.hasOtherRetainedCopy.2",
    .label ".LB.Planner.hasOtherRetainedCopy.3",
    .label ".LB.Planner.hasOtherRetainedCopy.4"]

theorem labels_cover : hasOtherRetainedCopyAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.hasOtherRetainedCopy]
  cfg_labels

macro "ho_inv" : tactic => `(tactic|
  simp only [Inv, Names.hasOtherRetainedCopy, String.reduceEq, ↓reduceIte])
macro "ho_inv" "at" h:ident : tactic => `(tactic|
  simp only [Inv, Names.hasOtherRetainedCopy, String.reduceEq, ↓reduceIte] at $h:ident)
macro "ho_var" : tactic => `(tactic|
  simp only [V, Names.hasOtherRetainedCopy, String.reduceEq, ↓reduceIte])

/-! ### `xorq (%b, %i), %rd` -/

section
variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

theorem xor_reg_mem_idx_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem addr 8).isSome = true ∧
          let v := s.regs.get64 rd ^^^ BitVec.ofInt 64 (Mem.loadInt s.dmem addr 8).get!
          ∀ af : Bool, Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.xor (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, Reg64s.get_low_W64,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_idx, Width.bytes, hload, Effects.All]
  intro af
  exact hn _ (by rw [hload, Option.get!_some] at hpre; exact hpre af)
end

/-! ### The blocks -/

open ShallowestCopy

section
variable [Host] [FunDecls] (P : Addr) (h : HG) (F : MProp 64) (s : MachineData) (ra : Int64)

set_option maxHeartbeats 100000 in
theorem b_entry : hasOtherRetainedCopyAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl P h F s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  ho_inv
  exact ht

set_option maxHeartbeats 100000 in
theorem b_fn (hpre : VPre HView HG.Ok P h F hasOtherA 8 s) (w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ : Word)
    (hk0 : Kg (HView P h ∗ F) s ra [w₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇] (s.pushRa ra)) :
    hasOtherRetainedCopyAsm.ForallBlocks fun blk =>
      blk.label = .label Names.hasOtherRetainedCopy → Obl P h F s ra blk := by
  cfg_block [Obl, Names.hasOtherRetainedCopy]
  intro t ht
  ho_inv at ht
  subst ht
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = P := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hq : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by
    rw [← Reg64s.get64_rsp, hk0.sp64]
  obtain ⟨hpo, hpm⟩ := hk0.pushes (xs := [(s.pushRa ra).regs.r15.toBitVec,
    (s.pushRa ra).regs.r14.toBitVec, (s.pushRa ra).regs.r13.toBitVec,
    (s.pushRa ra).regs.r12.toBitVec, (s.pushRa ra).regs.rbp.toBitVec,
    (s.pushRa ra).regs.rbx.toBitVec]) (by simp)
  simp only [pushes] at hpm
  change (Stk (rsp s) ([w₀] ++ w₁ :: [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec,
    s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec])
    ra.toBitVec ∗ HView P h ∗ F).get _ at hpm
  simp only [PushOk] at hpo
  obtain ⟨p1, p2, p3, p4, p5, p6, -⟩ := hpo
  have ha : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64
      = rsp s - 8#64 - BitVec.ofNat 64 (8 * ([s.regs.rbx.toBitVec, s.regs.rbp.toBitVec,
        s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec,
        s.regs.r15.toBitVec].length + 1)) := by
    rw [hq]; simp only [List.length_cons, List.length_nil]; bv_omega
  have k7 := Stk.wd_isSome hpm ha
  have hst := Stk.wd_store hpm ha (s.pushRa ra).regs.rdx.toBitVec
  change (Stk (rsp s) (fr s w₀) ra.toBitVec ∗ HView P h ∗ F).get _ at hst
  have hsp : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64
      = rsp s - 8#64 - 56#64 := ha.trans rfl
  have hv := hst
  rw [sep_lc] at hv
  obtain ⟨_, hR⟩ := HView.pv hv
  have h_m := PView.rd_m hR
  have k_m := PView.isSome_m hR
  unfold rd at h_m
  clear hv hR
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hrdi, h_m, BitVec.and_self] at k_m ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | with_reducible exact p4
    | with_reducible exact p5
    | with_reducible exact p6
    | with_reducible exact k7
    | with_reducible exact k_m
  | goto ".LB.Planner.hasOtherRetainedCopy.4" =>
    rename_i hc
    simp only [hrdi, h_m, BitVec.and_self] at hc
    have h0 := beq_iff_eq.mp hc
    cfg_goto
    · exact Kb.stack ⟨hst, hsp⟩ (by decide)
    · ho_inv
      exact ⟨w₀, ⟨hst, hsp⟩, from_ge (by show ¬ (0 : Word) < h.p.m; rw [h0]; decide)⟩
    · simp [V, Names.hasOtherRetainedCopy]
  | goto ".LB.Planner.hasOtherRetainedCopy.1" =>
    rename_i hc
    simp only [hrdi, h_m, BitVec.and_self] at hc
    have h0 : h.p.m ≠ 0#64 := by simpa using hc
    have hpos : 0 < h.p.m.toNat := Nat.pos_of_ne_zero fun e => h0 (BitVec.eq_of_toNat_eq e)
    cfg_goto
    · exact Kb.stack ⟨hst, hsp⟩ (by decide)
    · ho_inv
      refine ⟨w₀, ⟨⟨hst, hsp⟩, rfl, by simpa [MachineData.pushRa] using hpre.rdi, ?_, ?_, ?_⟩,
        hpos, rfl⟩
      · first | rfl | simp [MachineData.pushRa]
      · first | rfl | simp [MachineData.pushRa]
      · simpa [MachineData.pushRa] using hpre.args.1
    · left; have := h.p.m.isLt; simp [V, Names.hasOtherRetainedCopy]; omega

set_option maxHeartbeats 100000 in
theorem b_0 : hasOtherRetainedCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.hasOtherRetainedCopy.0" → Obl P h F s ra blk := by
  cfg_block [Obl]
  intro t ht
  ho_inv at ht
  obtain ⟨w, hli, hlt, hrest⟩ := ht
  have h12 := hli.r12
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [sub_beq_zero] at *
  vc_by_shape
  | goto ".LB.Planner.hasOtherRetainedCopy.2" =>
    rename_i hc
    have he : t.regs.rbx.toBitVec + 1#64 = h.p.m := by
      rw [BitVec.add_comm, ← h12]; exact beq_iff_eq.mp hc
    cfg_goto
    · exact hli.stk rfl rfl
    · ho_inv
      exact ⟨w, hli.kb.next rfl rfl, hrest.symm.trans (from_ge (by rw [he]; exact BitVec.lt_irrefl _))⟩
    · left; ho_var; omega
  | other =>
    rename_i hc
    have hne : 1#64 + t.regs.rbx.toBitVec ≠ h.p.m := by
      rw [← h12]; simpa using hc
    have e : (1#64 + t.regs.rbx.toBitVec).toNat = t.regs.rbx.toBitVec.toNat + 1 := by bv_omega
    have hlt' : (1#64 + t.regs.rbx.toBitVec).toNat < h.p.m.toNat := by
      have : (1#64 + t.regs.rbx.toBitVec).toNat ≠ h.p.m.toNat :=
        fun x => hne (BitVec.eq_of_toNat_eq x)
      omega
    first
    | (left; ho_var; omega)
    | (ho_inv
       refine ⟨w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt', ?_⟩
       rw [BitVec.add_comm]; exact hrest)

set_option maxHeartbeats 100000 in
theorem b_2 : hasOtherRetainedCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.hasOtherRetainedCopy.2" → Obl P h F s ra blk := by
  cfg_block [Obl]
  intro t ht
  ho_inv at ht
  obtain ⟨w, hk, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    first
    | (right; exact ⟨by ho_var, Nat.lt_succ_self _⟩)
    | (ho_inv
       exact ⟨w, hk.next rfl rfl, by
        simp only [res, rcx]
        simp only [show s.regs.get64 .rcx = s.regs.rcx.toBitVec from rfl, hd, Bool.false_eq_true,
          ite_false]; rfl⟩)

set_option maxHeartbeats 100000 in
theorem b_4 : hasOtherRetainedCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.hasOtherRetainedCopy.4" → Obl P h F s ra blk := by
  cfg_block [Obl]
  intro t ht
  ho_inv at ht
  obtain ⟨w, hk, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Planner.hasOtherRetainedCopy.3" =>
    cfg_goto
    · exact (hk.next rfl rfl).stack (by decide)
    · ho_inv
      exact ⟨w, hk.next rfl rfl, by
        simp only [res, rcx]
        simp only [show s.regs.get64 .rcx = s.regs.rcx.toBitVec from rfl, hd, Bool.false_eq_true,
          ite_false]; rfl⟩
    · left; simp [V, Names.hasOtherRetainedCopy]

set_option maxHeartbeats 100000 in
theorem b_3 (hok : HG.Ok h) : hasOtherRetainedCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.hasOtherRetainedCopy.3" → Obl P h F s ra blk := by
  cfg_block [Obl]
  intro t ht
  ho_inv at ht
  obtain ⟨w, hk, hal⟩ := ht
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := popSome hk
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact q1
    | with_reducible exact q2
    | with_reducible exact q3
    | with_reducible exact q4
    | with_reducible exact q5
    | with_reducible exact q6
  | retAddr =>
    refine Option.isSome_iff_exists.mpr
      ⟨ra, Kg.retAddr (P := HView P h ∗ F) (s := s) (fr := fr s w) ?_⟩
    exact popKg hk rfl rfl rfl rfl rfl rfl rfl rfl
  | ret =>
    refine Kg.vret (ok := HG.Ok) (a' := h) (popKg hk rfl rfl rfl rfl rfl rfl rfl rfl) rfl hok
      fun t' _ hax => ⟨rfl, ?_⟩
    simp only [al] at hal ⊢
    rw [hax]
    exact hal


set_option maxHeartbeats 400000 in
theorem b_1 (hret : VSpec MapM (fun _ => True) Names.isRetained isRetainedA 0 isRetainedQ)
    (hok : HG.Ok h) (hA : hasOtherA h s) :
    hasOtherRetainedCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.hasOtherRetainedCopy.1" → Obl P h F s ra blk := by
  cfg_block [Obl]
  intro t ht
  ho_inv at ht
  obtain ⟨w, hli, hlt, hrest⟩ := ht
  obtain ⟨hsi, hdx, hcx⟩ := hA
  have hbp := hli.rbp
  have h13 := hli.r13
  have h14 := hli.r14
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  obtain ⟨_, hR⟩ := HView.pv hb
  have h_src := PView.rd_src hR
  have k_src := PView.isSome_src hR
  have h_x := PView.rd_sw hR hok hlt
  have k_x := PView.isSome_sw hR hok hlt
  have h_o := PView.rd_sw hR hok hcx
  have k_o := PView.isSome_sw hR hok hcx
  unfold rd at h_src
  clear hb hR
  simp only [Names.isRetained] at hret
  unfold rd at h_x h_o
  have hmax : t.regs.rbx.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hlt hok.m
  kvcgen64 [hret, xor_reg_mem_idx_spec]
  all_goals try symexec_norm
  all_goals try simp only [h13, h14, h_src, fold_slot] at ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_src
    | with_reducible exact k_x
    | with_reducible exact k_o
  | goto ".LB.Planner.hasOtherRetainedCopy.0" =>
    rename_i hc
    have hskip : Flat.otherFrom h.p.fl h.M h.dv (rcx s) t.regs.rbx.toBitVec
        = Flat.otherFrom h.p.fl h.M h.dv (rcx s) (t.regs.rbx.toBitVec + 1#64) := by
      first
      | (refine skip_off (BitVec.lt_def.2 hlt) ?_
         simp only [sub_beq_zero] at hc
         exact (beq_iff_eq.mp hc).trans hbp)
      | (refine skip_slot (BitVec.lt_def.2 hlt) ?_
         have hne := jne_true hc
         simp only [h13, h14, h_src, fold_slot] at hne
         rwa [h_x, h_o] at hne)
    cfg_goto
    · exact hli.stk rfl rfl
    · ho_inv
      exact ⟨w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt, hskip.symm.trans hrest⟩
    · left; ho_var; omega
  | other =>
    first
    | decide
    | (rename_i hoff _ _ _ _ hsl
       simp only [sub_beq_zero] at hoff
       have hoff' : t.regs.rbx.toBitVec ≠ rcx s := by
         show _ ≠ s.regs.rcx.toBitVec; rw [← hbp]; simpa using hoff
       have hsl' := jne_false hsl
       simp only [h13, h14, h_src, fold_slot] at hsl'
       rw [h_x, h_o] at hsl'
       clear hsl
       refine Kb.vcall (V := MapM) (ok := fun _ => True) (A := isRetainedA) (Q := isRetainedQ)
         (S := h.mp) (a := h.M) (F := PView P h.p ∗ Bs h.dn h.dv.toList ∗ F) (s := s) (ra := ra)
         (lo := []) (w := w) (hi := [s.regs.rdx.toBitVec, s.regs.rbx.toBitVec,
           s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec,
           s.regs.r15.toBitVec]) (k := 0) ?kb rfl rfl ?rdi trivial ?A ?_
       case kb => rw [← HView.split]; exact hli.kb.next rfl rfl
       case rdi => exact hli.r15
       case A => exact hmax
       intro t2 a' lo' w' hkb hl hQ _ hag
       obtain rfl := List.eq_nil_of_length_eq_zero hl
       obtain ⟨hli2, hbx⟩ := LI.after hag (hli.next rfl rfl rfl rfl rfl rfl rfl) hkb hQ.1
       have hal : al t2 = if Flat.isRetained h.M t.regs.rbx.toBitVec then 1#8 else 0#8 := hQ.2
       clear hQ hkb
       have hbx' : t2.regs.rbx.toBitVec = t.regs.rbx.toBitVec := by rw [hbx]
       have hk2 : Kb (HView P h ∗ F) s ra ([w'] ++ [s.regs.rdx.toBitVec, s.regs.rbx.toBitVec,
           s.regs.rbp.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec,
           s.regs.r15.toBitVec]) 56#64 t2 := hli2.kb
       have e0 : t2.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * 0) = t2.regs.rsp.toBitVec := by simp
       have h_dn : rd t2.dmem t2.regs.rsp.toBitVec = h.dn := by
         rw [← e0, hk2.rd_hi rfl (i := 0) (by simp)]; exact hdx
       have k_dn : (t2.dmem.loadInt t2.regs.rsp.toBitVec 8).isSome = true := by
         rw [← e0]; exact hk2.isSome_hi rfl (i := 0) (by simp)
       have hb2 := hli2.kb.mem
       rw [sep_lc] at hb2
       have hmax2 : t2.regs.rbx.toBitVec.toNat < MAX_N := hbx' ▸ hmax
       have h_b := HView.rdb_dn hb2 hmax2
       have k_b := HView.isSome_dn hb2 hmax2
       unfold rd at h_dn
       unfold rdb at h_b
       clear hb2 hk2
       kvcgen64
       all_goals try symexec_norm
       all_goals try simp only [h_dn] at ⊢
       vc_by_shape
       | load =>
         first
         | with_reducible exact k_dn
         | with_reducible exact k_b
       | goto ".LB.Planner.hasOtherRetainedCopy.0" =>
         rename_i hc
         have hskip : Flat.otherFrom h.p.fl h.M h.dv (rcx s) t.regs.rbx.toBitVec
             = Flat.otherFrom h.p.fl h.M h.dv (rcx s) (t.regs.rbx.toBitVec + 1#64) := by
           first
           | (refine skip_ret (BitVec.lt_def.2 hlt) ?_
              have h1 := hal.symm.trans (al_zero (t := t2) (by
                first
                | with_reducible assumption
                | (rw [Bool.not_eq_false']; with_reducible assumption)))
              cases hr : Flat.isRetained h.M t.regs.rbx.toBitVec
              · rfl
              · rw [hr] at h1; exact absurd h1 (by decide))
           | (refine skip_dn (BitVec.lt_def.2 hlt) ?_
              simp only [h_dn] at hc
              simp only [h_b] at hc
              rw [hbx'] at hc
              simpa using hc)
         cfg_goto
         · exact hli2.stk rfl rfl
         · ho_inv
           refine ⟨w', hli2.next rfl rfl rfl rfl rfl rfl rfl, ?_, ?_⟩
           · rw [hbx']; exact hlt
           · rw [hbx']; exact hskip.symm.trans hrest
         · left; ho_var; rw [hbx']; omega
       | goto ".LB.Planner.hasOtherRetainedCopy.3" =>
         rename_i hc
         have hr : Flat.isRetained h.M t.regs.rbx.toBitVec = true := by
           have h1 := al_ne (t := t2) (by
             first
             | with_reducible assumption
             | (rw [Bool.not_eq_true']; with_reducible assumption))
           cases hr : Flat.isRetained h.M t.regs.rbx.toBitVec
           · rw [hr] at hal; exact (h1 hal).elim
           · rfl
         have hd : Flat.get h.dv t.regs.rbx.toBitVec = 0#8 := by
           simp only [h_dn] at hc
           simp only [h_b] at hc
           rw [hbx'] at hc
           simpa using hc
         have hres : res h s = true :=
           hrest.symm.trans (found (BitVec.lt_def.2 hlt) hoff' hsl' hr hd)
         have ha1 : al t2 = 1#8 := hal.trans (by rw [hr]; rfl)
         cfg_goto
         · exact (hli2.kb.next rfl rfl).stack (by decide)
         · ho_inv
           refine ⟨w', hli2.kb.next rfl rfl, ?_⟩
           rw [hres]; exact ha1
         · left; ho_var; omega)
  all_goals decide

end

end OtherU

end Bbu.Unit

namespace Bbu.Unit

open OtherU in
theorem hasOtherRetainedCopy_unit [Host] [FunDecls]
    (hret : VSpec MapM (fun _ => True) Names.isRetained isRetainedA 0 isRetainedQ) :
    VThm HView HG.Ok hasOtherRetainedCopyAsm hasOtherA 8 hasOtherQ := by
  intro P h F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr₀, hfr, hk0⟩ := hpre.kg ra
  match fr₀, hfr, hk0 with
  | [w₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇], _, hk0 =>
  refine Program.WP.cfg (OtherU.Inv P h F s ra) (OtherU.V h) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry P h F s ra
  · exact b_fn P h F s ra hpre w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ hk0
  · exact b_0 P h F s ra
  · exact b_1 P h F s ra hret hpre.ok hpre.args
  · exact b_2 P h F s ra
  · exact b_3 P h F s ra hpre.ok
  · exact b_4 P h F s ra

end Bbu.Unit
