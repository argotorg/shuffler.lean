module

public import BbuKraken.Unit.Plan.EntrySpecs
import all BbuKraken.Unit.Plan.EntrySpecs
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-! The rejection paths of the public `plan` entry.
The argument guard runs before the source, target and output buffers are read.
Only the stack frame and the two stack arguments must be mapped on these paths. -/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.EntryU
open Bbu.Sep

def BadArgs (m n : Word) (allowed strategy : BitVec 32) : Prop :=
  MAX_N < m.toNat ∨ MAX_N < n.toNat ∨
    1 < (allowed.setWidth 8).toNat ∨ 1 < (strategy.setWidth 8).toNat

def Args (s : MachineData) (allowed strategy : BitVec 32) (F : MProp 64) : MProp 64 :=
  B32 (rsp s) allowed ∗ B32 (rsp s + 8#64) strategy ∗ F

def RejectPre (allowed strategy : BitVec 32) (F : MProp 64) (s : MachineData) : Prop :=
  BadArgs (rdi s) (rsi s) allowed strategy ∧
    ∃ fr v, fr.length = 11 ∧ (Stk (rsp s) fr v ∗ Args s allowed strategy F).get s.dmem

def RejectPost (allowed strategy : BitVec 32) (F : MProp 64) (s t : MachineData) : Prop :=
  rax t = -2#64 ∧
    ∃ fr v, fr.length = 11 ∧ (Stk (rsp s) fr v ∗ Args s allowed strategy F).get t.dmem

theorem bad_or (allowed strategy : BitVec 32) :
    1 < ((allowed ||| strategy).setWidth 8).toNat ↔
      1 < (allowed.setWidth 8).toNat ∨ 1 < (strategy.setWidth 8).toNat := by
  have hor : (allowed ||| strategy).setWidth 8 = allowed.setWidth 8 ||| strategy.setWidth 8 := by
    bv_decide
  rw [hor]
  generalize allowed.setWidth 8 = a, strategy.setWidth 8 = b
  change 1#8 < (a ||| b) ↔ 1#8 < a ∨ 1#8 < b
  bv_decide

theorem low8_widen (w : BitVec 32) :
    (w.setWidth 64).take 8 = w.setWidth 8 := by
  simp only [BitVec.take]
  bv_decide

theorem b32_read {a : Addr} {v : BitVec 32} {F : MProp 64} {m : Mem 64}
    (h : (B32 a v ∗ F).get m) : BitVec.ofInt 32 (m.loadInt a 4).get! = v := by
  unfold B32 at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.get!_some,
    BitVec.ofInt_ofBytes_toBytes 32 4 rfl]

structure Bd (allowed strategy : BitVec 32) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo : List Word) (t : MachineData) : Prop where
  kb : Kb (Args s allowed strategy F) s ra (lo ++ [s.regs.rbx.toBitVec]) 88#64 t
  len : lo.length = 10
  bp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

theorem Bd.next {a b F s ra lo t u} (h : Bd a b F s ra lo t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) : Bd a b F s ra lo u :=
  ⟨h.kb.next hm hsp, h.len, hbp.trans h.bp, h12.trans h.r12,
    h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

theorem Bd.popSome {a b F s ra lo t} (h : Bd a b F s ra lo t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 80#64) 8).isSome = true := by
  have hd : 88#64 = BitVec.ofNat 64 (8 * (lo ++ [s.regs.rbx.toBitVec]).length) := by
    simp [h.len]
  exact h.kb.isSome_fr hd (i := 10) (by simp [h.len])

theorem Bd.pop {a b F s ra lo t u} (h : Bd a b F s ra lo t)
    (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = 80#64 + t.regs.rsp.toBitVec + 8#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem (80#64 + t.regs.rsp.toBitVec))
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) :
    Kg (Args s a b F) s ra (lo ++ [s.regs.rbx.toBitVec]) u := by
  have hd : 88#64 = BitVec.ofNat 64 (8 * (lo ++ [s.regs.rbx.toBitVec]).length) := by
    simp [h.len]
  have hr := h.kb.rd_fr hd (i := 10) (by simp [h.len])
  have hlen := h.len
  have he : (lo ++ [s.regs.rbx.toBitVec])[10]'(by simp [h.len]) = s.regs.rbx.toBitVec := by
    rw [List.getElem_append_right (by omega)]
    simp [h.len]
  rw [he] at hr
  refine h.kb.kg hm (by rw [hsp, h.kb.sp]; bv_omega) ?_
    (hbp.trans h.bp) (h12.trans h.r12) (h13.trans h.r13)
    (h14.trans h.r14) (h15.trans h.r15)
  apply UInt64.toBitVec_inj.mp
  rw [hbx, BitVec.add_comm (80#64)]
  exact hr

def Inv (allowed strategy : BitVec 32) (F : MProp 64) (s : MachineData) (ra : Int64) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.plan then t = s.pushRa ra
    else if l = ".LB.plan.12" ∨ l = ".LB.plan.13" then ∃ lo, Bd allowed strategy F s ra lo t
    else if l = ".LB.plan.9" then ∃ lo, Bd allowed strategy F s ra lo t ∧ rdx t = -2#64
    else False

def V (l : Label) (_ : MachineData) : Nat :=
  if l = Names.plan then 3
  else if l = ".LB.plan.12" ∨ l = ".LB.plan.13" then 2
  else 0

def E (allowed strategy : BitVec 32) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ RejectPost allowed strategy F s t ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (a b : BitVec 32) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, Inv a b F s ra blk.label t →
    let I' (l : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv a b F s ra l u ∧ Program.Decreases V blk.label blk.idx t l j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels planAsm) (s.pushRa ra) I' (E a b F s ra)) t

section
variable [Host] [FunDecls] (a b : BitVec 32) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_entry : planAsm.ForallBlocks fun blk => blk.label = .entry → Obl a b F s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  simpa only [Inv, Names.plan, ↓reduceIte] using ht

theorem b_12 : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.12" → Obl a b F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte, true_or] at ht
  obtain ⟨lo, hb⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  cfg_goto
  · exact (hb.kb.next rfl rfl).stack (by decide)
  · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte, or_self]
    exact ⟨lo, hb.next rfl rfl rfl rfl rfl rfl rfl, rfl⟩
  · left; simp [V, Names.plan]

theorem b_13 : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.13" → Obl a b F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte, or_true] at ht
  obtain ⟨lo, hb⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  cfg_goto
  · exact (hb.kb.next rfl rfl).stack (by decide)
  · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte, or_self]
    exact ⟨lo, hb.next rfl rfl rfl rfl rfl rfl rfl, rfl⟩
  · left; simp [V, Names.plan]

theorem b_9 : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.9" → Obl a b F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte, or_self] at ht
  obtain ⟨lo, hb, hdx⟩ := ht
  have kp := hb.popSome
  rw [BitVec.add_comm] at kp
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => with_reducible exact kp
  | retAddr =>
    refine Option.isSome_iff_exists.mpr ⟨ra, Kg.retAddr
      (P := Args s a b F) (s := s) (fr := lo ++ [s.regs.rbx.toBitVec]) ?_⟩
    exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
  | ret =>
    refine Kg.ret (P := Args s a b F) (fr := lo ++ [s.regs.rbx.toBitVec]) ?_
      fun u hmem hax => ?_
    · exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
    · exact ⟨hax.trans hdx, lo ++ [s.regs.rbx.toBitVec], ra.toBitVec,
        by simp [hb.len], hmem ▸ hb.kb.mem⟩

end
end Bbu.Unit.EntryU
