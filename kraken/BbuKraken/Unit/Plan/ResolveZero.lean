import BbuKraken.Unit.Plan.ResolveByteFrame
import BbuKraken.Unit.Plan.ResolveExit

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU
open Bbu.Sep

structure InputRegs (P : Addr) (r : RG) (s t : MachineData) : Prop where
  r12 : t.regs.get64 .r12 = r.mp
  r14 : t.regs.get64 .r14 = P
  r8 : r8 t = r.currentPtr
  r9 : r9 t = r9 s
  rdx : rdx t = rdx s

def ZeroPrefix (o : Word) (t : MachineData) : Prop :=
  ∀ q : Word, q < o → rdb t.dmem (t.regs.rsp.toBitVec + 8240#64 + q) = 0#8

def Zero (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (R : List Word → List Word → Prop) (t : MachineData) : Prop :=
  ∃ lo loc o, Bd P r F s ra lo loc t ∧ R lo loc ∧ InputRegs P r s t ∧ o < r.p.m ∧
    rax t = t.regs.rsp.toBitVec + 8240#64 + o ∧
    rcx t = t.regs.rsp.toBitVec + 8240#64 + r.p.m ∧ ZeroPrefix o t

def AfterZero (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (R : List Word → List Word → Prop) (t : MachineData) : Prop :=
  ∃ lo loc, Bd P r F s ra lo loc t ∧ R lo loc ∧ InputRegs P r s t ∧ ZeroPrefix r.p.m t

def zphase (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (R : List Word → List Word → Prop) (phase : Label → MachineData → Prop)
    (l : Label) (t : MachineData) : Prop :=
  if l = ".LB.Planner.resolve.0" then Zero P r F s ra R t
  else if l = ".LB.Planner.resolve.1" then AfterZero P r F s ra R t
  else phase l t

def zvar (C : Nat) (var : Label → MachineData → Nat) (l : Label) (t : MachineData) : Nat :=
  if l = ".LB.Planner.resolve.0" then (rcx t - rax t).toNat + C + 1 else var l t

theorem rdb_storeByte_ne (m : Mem 64) (a b : Addr) (z : Int) (h : b ≠ a) :
    rdb (m.storeInt a 1 z) b = rdb m b := by
  simp only [rdb, Mem.loadInt_one, Mem.get?_storeInt_one, ite_eq_right h]

theorem rdb_storeZero (m : Mem 64) (a : Addr) : rdb (m.storeInt a 1 0) a = 0#8 := by
  rw [rdb, Mem.loadInt_storeInt _ _ _ _ (by decide), Option.get!_some]
  rfl

theorem zeroPrefix_next {t u : MachineData} {o : Word} (h : ZeroPrefix o t)
    (hm : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8240#64 + o) 1 0)
    (hsp : u.regs.rsp = t.regs.rsp) : ZeroPrefix (o + 1) u := by
  have hsp' : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec := congrArg UInt64.toBitVec hsp
  intro q hq
  rw [hsp', hm]
  by_cases he : q = o
  · subst q
    exact rdb_storeZero _ _
  · rw [rdb_storeByte_ne _ _ _ _ (by intro he'; exact he (by bv_omega))]
    exact h q (by bv_omega)

theorem zero_continue {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {R : List Word → List Word → Prop} {lo loc : List Word} {o : Word}
    (hb : Bd P r F s ra lo loc t) (hz : ZeroPrefix o t)
    (hoN : o.toNat < MAX_N)
    (hR : ∀ w, R lo (loc.set (1030 + o.toNat / 8) w))
    (ho : o + 1 < r.p.m) (hregs : InputRegs P r s u)
    (ha : rax u = u.regs.rsp.toBitVec + 8240#64 + (o + 1))
    (hc : rcx u = u.regs.rsp.toBitVec + 8240#64 + r.p.m)
    (hm : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8240#64 + o) 1 0)
    (hsp : u.regs.rsp = t.regs.rsp) : Zero P r F s ra R u := by
  obtain ⟨w, hbu⟩ := hb.storeZeroByte (u := u) hoN hm hsp
  exact ⟨lo, _, o + 1, hbu, hR w, hregs, ho, ha, hc, zeroPrefix_next hz hm hsp⟩

theorem zero_end {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {R : List Word → List Word → Prop} {lo loc : List Word} {o : Word}
    (hb : Bd P r F s ra lo loc t) (hz : ZeroPrefix o t)
    (hoN : o.toNat < MAX_N)
    (hR : ∀ w, R lo (loc.set (1030 + o.toNat / 8) w))
    (he : o + 1 = r.p.m) (hregs : InputRegs P r s u)
    (hm : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8240#64 + o) 1 0)
    (hsp : u.regs.rsp = t.regs.rsp) : AfterZero P r F s ra R u := by
  obtain ⟨w, hbu⟩ := hb.storeZeroByte (u := u) hoN hm hsp
  refine ⟨lo, _, hbu, hR w, hregs, ?_⟩
  rw [← he]
  exact zeroPrefix_next hz hm hsp

section
variable [Host] [FunDecls]
  (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (R : List Word → List Word → Prop) (phase : Label → MachineData → Prop)
  (var : Label → MachineData → Nat) (C : Nat)
  (hok : r.Ok)
  (hR : ∀ lo loc (o : Word) w, o.toNat < MAX_N → R lo loc → R lo (loc.set (1030 + o.toNat / 8) w))
  (hV : ∀ t, var ".LB.Planner.resolve.1" t ≤ C)

include hok hR hV

theorem b_0 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.0" →
      Obl P r F s ra (zphase P r F s ra R phase) (zvar C var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, zphase, Names.resolve, String.reduceEq, ↓reduceIte, Zero] at ht
  obtain ⟨lo, loc, o, hb, hrel, hregs, ho, hax, hcx, hz⟩ := ht
  have hoN : o.toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp ho) hok.planner.m
  have hsome := hb.zeroByteSome hoN
  have e0 : rcx t - rax t = r.p.m - o := by rw [hax, hcx]; bv_omega
  have e1 : rcx t - (1#64 + rax t) = r.p.m - (o + 1) := by rw [hax, hcx]; bv_omega
  simp only [Reg64s.get64_rax, Reg64s.get64_rcx] at hax hcx e0 e1
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => rw [hax]; exact hsome
  | goto ".LB.Planner.resolve.0" =>
    rename_i hj
    symexec_norm at hj
    have hn : o + 1 ≠ r.p.m := by
      intro he
      simp only [hax, hcx] at hj
      have hh : 1#64 + (t.regs.rsp.toBitVec + 8240#64 + o) =
          t.regs.rsp.toBitVec + 8240#64 + r.p.m := by rw [← he]; bv_omega
      simp only [hh, sub_beq_zero, beq_self_eq_true, Bool.not_true, Bool.false_eq_true] at hj
    cfg_goto
    · exact hb.kb.stack (by decide)
    · simp only [Inv, zphase, Names.resolve, String.reduceEq, ↓reduceIte]
      apply zero_continue hb hz hoN (fun w => hR lo loc o w hoN hrel)
      · bv_omega
      · exact ⟨hregs.r12, hregs.r14, hregs.r8, hregs.r9, hregs.rdx⟩
      · change 1#64 + t.regs.rax.toBitVec = t.regs.rsp.toBitVec + 8240#64 + (o + 1)
        rw [hax]; bv_omega
      · exact hcx
      · rw [← hax]
      · rfl
    · left
      simp only [V, zvar, String.reduceEq, false_or, ↓reduceIte]
      symexec_norm at ⊢
      rw [e0, e1]
      have hd := Flat.sub_succ_lt ho
      omega
  | other =>
    rename_i hj
    symexec_norm at hj
    have he : o + 1 = r.p.m := by
      have hh : 1#64 + t.regs.rax.toBitVec = t.regs.rcx.toBitVec := by
        simpa only [Bool.not_eq_false', sub_beq_zero, beq_iff_eq] using hj
      rw [hax, hcx] at hh
      bv_omega
    first
    | (simp only [Inv, zphase, Names.resolve, String.reduceEq, ↓reduceIte]
       apply zero_end hb hz hoN (fun w => hR lo loc o w hoN hrel) he
       · exact ⟨hregs.r12, hregs.r14, hregs.r8, hregs.r9, hregs.rdx⟩
       · rw [← hax]
       · rfl)
    | (left
       simp only [V, zvar, String.reduceEq, false_or, ↓reduceIte]
       symexec_norm at ⊢
       rw [e0]
       have bound (u : MachineData) : var ".LB.Planner.resolve.1" u + 2 <
           (r.p.m - o).toNat + C + 1 + 2 := by
         have hv := hV u
         omega
       apply bound)

end
end Bbu.Unit.ResolveU
