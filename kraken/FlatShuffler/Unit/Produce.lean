module

import Kraken.X64.Parser

public import FlatShuffler.Unit.ProduceLemmas
import all FlatShuffler.Unit.ProduceLemmas
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-!
# `produce`

`Names.produce` in `build/kraken/c/build_bottom_up.S`: 6 `pushq` and `subq $24`, with 12 free words for the
saved registers, locals, callee return address and callee scratch words.
It reads the target word `m_target[t]` and calls `shallowestCopyPosition`,
then `push`, `dup` or `isSpilled` and `push`, or writes `m_blocked`. Then it asserts
`m_positionOf[t] = size - 1` and decrements `m_pendingGenerations`.

The preconditions of the callees: the target word is in the view (`t < n`); its id is in
`splIds` (`isSpilledA`), and `Pre.ok` gives `G.Ok.spl` to `isSpilled`; the copy for `dup` is
below `size ≤ n`; `len < n` and `nops < 6n` (`pushA`, `dupA`). The caller is `generate`, after
its check `t < n`.

The proof is a CFG proof (`Program.WP.cfg`). Between the pushes and the pops the state is
`ProduceProof.Bd`; `8(%rsp)` holds the copy position `cp`. The invariant at each label names the
part of `Flat.produce` that is left: `act` (the action on the target slot) and `fin` (the check
after it). Assertion paths reach `exit(1)` with the stores made before the failed
assertion. The lemmas are in `FlatShuffler.Unit.ProduceLemmas`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit
open FlatShuffler.Sep

local macro "bd_next% " h:term:max : term =>
  `(ProduceProof.Bd.next $h (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl))

local macro "bd_step% " h:term:max hm:term:max : term =>
  `(ProduceProof.Bd.step $h $hm (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl))

namespace ProduceProof

def Inv (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (w cp : Word) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .label l, t =>
    if l = Names.produce then t = s.pushRa ra
    else if l = ".LB.Emission.produce.0" then ∃ y, Bd S g F s ra w y cp t
      ∧ isJunk (StackSlot.ofWord w) = false
      ∧ act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
        = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
    else if l = ".LB.Emission.produce.1" ∨ l = ".LB.Emission.produce.3" then ∃ y, Bd S g F s ra w y cp t
      ∧ act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
        = Flat.push (flat g) (StackSlot.ofWord w) s.regs.rsi.toBitVec
    else if l = ".LB.Emission.produce.2" then ∃ g1 y r, Bd S g1 F s ra w y cp t ∧ g1.Ok ∧ Keep g g1
      ∧ Flat.produce (flat g) s.regs.rsi.toBitVec = fin r s.regs.rsi.toBitVec
      ∧ flat g1 = r.2 ∧ al t = code r.1 ∧ code r.1 ≠ ASSERTION_FAILED
    else if l = ".LB.Emission.produce.9" then ∃ g1 y, Bd S g1 F s ra w y cp t ∧ g1.Ok ∧ produceQ g g1 s t
    else if l = ".LB.Emission.produce.4" then ∃ y, Bd S g F s ra w y cp t ∧ cp.toNat < g.h.len.toNat
      ∧ act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
        = Flat.dup (flat g) cp s.regs.rsi.toBitVec
    else if l = ".LB.Emission.produce.5" then ∃ y, Bd S g F s ra w y cp t
      ∧ canBeFreelyGenerated (StackSlot.ofWord w) = false
      ∧ act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
        = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
    else if l = ".LB.Emission.produce.6" ∨ l = ".LB.Emission.produce.7" then ∃ g1 y, Bd S g1 F s ra w y cp t ∧ g1.Ok ∧ Keep g g1
      ∧ Flat.produce (flat g) s.regs.rsi.toBitVec = (.assertionFailed, flat g1)
    else if l = ".LB.Emission.produce.8" then ∃ g1 y, Bd S g1 F s ra w y cp t ∧ g1.Ok ∧ Keep g g1
      ∧ Flat.produce (flat g) s.regs.rsi.toBitVec = (.done, {flat g1 with pend := g1.h.pend - 1})
      ∧ al t = 0#8
    else False
  | .exit, _ => False

def V (l : Label) (_t : MachineData) : Nat :=
  if l = ".LB.Emission.produce.9" then 0 else if l = ".LB.Emission.produce.8" then 1 else if l = ".LB.Emission.produce.2" ∨ l = ".LB.Emission.produce.7" ∨ l = ".LB.Emission.produce.1" then 2 else 3

def E [Host] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (a : Int64) (t : MachineData) : Prop :=
  (a = ra ∧ Sep.Post S F 12 (fun g' t => produceQ g g' s t) s t ∧ Sep.mod.Agree s t) ∨
    (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧
      Sep.Post S F 12 (fun g' t => produceX g g' s t) s t)

def Obl [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (w cp : Word) (blk : Program.Block) : Prop :=
  ∀ t, Inv S g F s ra w cp blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra w cp c u ∧ Program.Decreases V blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels produceAsm) (s.pushRa ra) I' (E S g F s ra)) t

section
variable [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
  (w cp : Word)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_9
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.9" → Obl S g F s ra w cp blk := by
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self] at ht
  obtain ⟨g1, y, hbd, hok1, hQ⟩ := ht
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hbd.isSome_pops
  kvcgen64
  all_goals try symexec_norm
  all_goals try dsimp only [V]
  vc_by_shape
  | load =>
    first
    | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
    | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
  | retAddr =>
    refine (congrArg Option.isSome (hbd.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).retAddr).trans rfl
    all_goals rfl
  | ret =>
    refine ProofKit.intercept_mono_exit
      (E := fun a t => a = ra ∧ Sep.Post S F 12 (fun g' t => produceQ g g' s t) s t
        ∧ Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
    refine Kp.ret (hbd.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by rfl) hok1 fun t' _ hax =>
      NormalResult.of_returnRegister_eq hQ hax
    all_goals rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_6
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels produceAsm, label l ≠ label "exit")
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.6" → Obl S g F s ra w cp blk := by
  have he := ProofKit.external_call_spec "exit" hexit
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
  obtain ⟨g1, y, hbd, hok1, hK1, hP⟩ := ht
  kvcgen64 [he]
  all_goals symexec_norm
  all_goals try dsimp only [V]
  vc_by_shape
  | load => with_reducible exact hbd.isSome_exit
  | jumpOut =>
    apply ProofKit.intercept_exit hout
    refine Or.inr ⟨rfl, rfl, g1, _, ra.toBitVec,
      ?_, hok1, ?_, hbd.mem_exit _⟩
    · dsimp only [produceX, ExitRes, rsi, Reg64s.get64_rsi]
      rw [hP]
      exact ⟨hK1, rfl, rfl⟩
    · rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_7
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels produceAsm, label l ≠ label "exit")
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.7" → Obl S g F s ra w cp blk := by
  have he := ProofKit.external_call_spec "exit" hexit
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
  obtain ⟨g1, y, hbd, hok1, hK1, hP⟩ := ht
  kvcgen64 [he]
  all_goals symexec_norm
  all_goals try dsimp only [V]
  vc_by_shape
  | load => with_reducible exact hbd.isSome_exit
  | jumpOut =>
    apply ProofKit.intercept_exit hout
    refine Or.inr ⟨rfl, rfl, g1, _, ra.toBitVec,
      ?_, hok1, ?_, hbd.mem_exit _⟩
    · dsimp only [produceX, ExitRes, rsi, Reg64s.get64_rsi]
      rw [hP]
      exact ⟨hK1, rfl, rfl⟩
    · rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_2
    (hpre : Sep.Pre S g F produceA 12 s)
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels produceAsm, label l ≠ label "exit")
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.2" → Obl S g F s ra w cp blk := by
  have hTn : s.regs.rsi.toBitVec.toNat < g.h.n.toNat := hpre.args.1
  have he := ProofKit.external_call_spec "exit" hexit
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
  obtain ⟨g1, y, r, hbd, hok1, hK1, hP, hf, hal, normalStatus⟩ := ht
  have hTm : s.regs.rsi.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hTn hpre.ok.n
  have hbx1 := hbd.bx
  have hr14 := hbd.r14
  have hm1 := hbd.mem
  kvcgen64 [he]
  all_goals symexec_norm
  all_goals simp only [hbx1, hr14, rd_len' hm1, rd_pos' hm1 hTm, add_neg_one] at *
  all_goals try dsimp only [V]
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_len' hm1
    | with_reducible exact isSome_pos' hm1 hTm
    | with_reducible exact hbd.isSome_exit
  | goto ".LB.Emission.produce.9" =>
    have hne : al t ≠ 0#8 := al_ne (by with_reducible assumption)
    have hr : r.1 ≠ .done := fun e => hne (hal.trans (by rw [e]; rfl))
    cfg_goto
    · exact (bd_next% hbd).stack
    · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨g1, y, bd_next% hbd, hok1,
        prodQ hK1 (hP.trans (fin_ne hr)) hf ((al_eq (by with_reducible rfl)).trans hal) normalStatus⟩
    · simp [V]
  | goto ".LB.Emission.produce.8" =>
    have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
    have hd : r.1 = .done := code_eq_zero (hal.symm.trans hal0)
    have heq : g1.h.pos[s.regs.rsi.toBitVec.toNat] = g1.h.len - 1#64 :=
      eq_of_z (by with_reducible assumption)
    have hF : Flat.produce (flat g) s.regs.rsi.toBitVec
        = (.done, {flat g1 with pend := g1.h.pend - 1}) := by
      have h2 : Flat.get r.2.pos s.regs.rsi.toBitVec = r.2.size - 1 := by
        rw [← hf]; show Flat.get g1.h.pos _ = g1.h.len - 1; rw [get_eq _ hTm]; exact heq
      rw [hP, fin_ok hd h2, ← hf]
      rfl
    cfg_goto
    · exact (bd_next% hbd).stack
    · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨g1, y, bd_next% hbd, hok1, hK1, hF,
        (al_eq (by with_reducible rfl)).trans hal0⟩
    · simp [V]
  | jumpOut =>
    have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
    have hd : r.1 = .done := code_eq_zero (hal.symm.trans hal0)
    have hne : g1.h.pos[s.regs.rsi.toBitVec.toNat] ≠ g1.h.len - 1#64 := ne_of_z (by with_reducible assumption)
    have hF : Flat.produce (flat g) s.regs.rsi.toBitVec = (.assertionFailed, flat g1) := by
      have h2 : Flat.get r.2.pos s.regs.rsi.toBitVec ≠ r.2.size - 1 := by
        rw [← hf]; show Flat.get g1.h.pos _ ≠ g1.h.len - 1; rw [get_eq _ hTm]; exact hne
      rw [hP, fin_bad hd h2, hf]
    apply ProofKit.intercept_exit hout
    refine Or.inr ⟨rfl, rfl, g1, _, ra.toBitVec,
      ?_, hok1, ?_, hbd.mem_exit _⟩
    · dsimp only [produceX, ExitRes, rsi, Reg64s.get64_rsi]
      rw [hF]
      exact ⟨hK1, rfl, rfl⟩
    · rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_8
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.8" → Obl S g F s ra w cp blk := by
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
  obtain ⟨g1, y, hbd, hok1, hK1, hF, hal0⟩ := ht
  have hm1 := hbd.mem
  have hb := hbd.bx
  kvcgen64
  all_goals symexec_norm
  all_goals simp only [hb, rd_pend' hm1] at *
  all_goals try dsimp only [V]
  vc_by_shape
  | load => with_reducible exact isSome_pend' hm1
  | closed => simp [V]
  | other =>
    have hm2 := store_pend' hm1 (g1.h.pend - 1#64)
    try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
    exact ⟨withPend g1 (g1.h.pend - 1#64), y, bd_step% hbd hm2, Ok.withPend hok1 _,
      prodQ (Keep.trans hK1 (Keep.withPend _)) hF (flat_withPend _)
        ((al_eq (by with_reducible rfl)).trans hal0) (by change 0#8 ≠ 2#8; decide)⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_1
    (hpre : Sep.Pre S g F produceA 12 s)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec)
    (hout : ∀ l ∈ Program.labels produceAsm, label l ≠ label "exit")
    (hpush : Sep.SpecWithExit Names.push pushA 2 pushQ pushX)
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.1" → Obl S g F s ra w cp blk := by
  have hTn : s.regs.rsi.toBitVec.toNat < g.h.n.toNat := hpre.args.1
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true] at ht
  obtain ⟨y, hbd, hact⟩ := ht
  simp only [Names.push] at hpush
  kvcgen64 [hpush]
  all_goals try symexec_norm
  refine Bd.callX (bd_next% hbd) hbd.bx hpre.ok
    ⟨hpre.args.2.1, hpre.args.2.2, show t.regs.r12.toBitVec.toNat < _ by rw [hbd.r12]; exact hTn⟩ ?_ ?_
  · intro _ t2 g2 y2 hbd2 hQ hok2
    obtain ⟨hK2, hf2, hal2⟩ := pushQ_of hQ (show t.regs.rbp.toBitVec = w from hbd.bp)
      (show t.regs.r12.toBitVec = s.regs.rsi.toBitVec from hbd.r12)
    kvcgen64
    all_goals try symexec_norm
    all_goals try dsimp only [V]
    vc_by_shape
    | closed => simp [V]
    | goto ".LB.Emission.produce.2" =>
      cfg_goto
      · exact (bd_next% hbd2).stack
      · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
          (al_eq (by with_reducible rfl)).trans hal2, fun failed => hQ.2 (hal2.trans failed)⟩
      · simp [V]
    | other =>
      try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
        (al_eq (by with_reducible rfl)).trans hal2, fun failed => hQ.2 (hal2.trans failed)⟩
  · intro tx hp harg
    apply ProofKit.intercept_exit hout
    refine Or.inr ⟨rfl, harg, hp.imp ?_⟩
    intro g2 hX
    dsimp only [pushX, rsi, rdx, Reg64s.get64_rsi, Reg64s.get64_rdx] at hX
    rw [hbd.bp, hbd.r12] at hX
    exact prodX_of (hprod.trans (by rw [hact]; rfl)) hX

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_3
    (hpre : Sep.Pre S g F produceA 12 s)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec)
    (hout : ∀ l ∈ Program.labels produceAsm, label l ≠ label "exit")
    (hpush : Sep.SpecWithExit Names.push pushA 2 pushQ pushX)
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.3" → Obl S g F s ra w cp blk := by
  have hTn : s.regs.rsi.toBitVec.toNat < g.h.n.toNat := hpre.args.1
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true] at ht
  obtain ⟨y, hbd, hact⟩ := ht
  simp only [Names.push] at hpush
  kvcgen64 [hpush]
  all_goals try symexec_norm
  refine Bd.callX (bd_next% hbd) hbd.bx hpre.ok
    ⟨hpre.args.2.1, hpre.args.2.2, show t.regs.r12.toBitVec.toNat < _ by rw [hbd.r12]; exact hTn⟩ ?_ ?_
  · intro _ t2 g2 y2 hbd2 hQ hok2
    obtain ⟨hK2, hf2, hal2⟩ := pushQ_of hQ (show t.regs.rbp.toBitVec = w from hbd.bp)
      (show t.regs.r12.toBitVec = s.regs.rsi.toBitVec from hbd.r12)
    kvcgen64
    all_goals try symexec_norm
    all_goals try dsimp only [V]
    vc_by_shape
    | goto ".LB.Emission.produce.2" =>
      cfg_goto
      · exact (bd_next% hbd2).stack
      · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
          (al_eq (by with_reducible rfl)).trans hal2, fun failed => hQ.2 (hal2.trans failed)⟩
      · simp [V]
    | other =>
      try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
        (al_eq (by with_reducible rfl)).trans hal2, fun failed => hQ.2 (hal2.trans failed)⟩
  · intro tx hp harg
    apply ProofKit.intercept_exit hout
    refine Or.inr ⟨rfl, harg, hp.imp ?_⟩
    intro g2 hX
    dsimp only [pushX, rsi, rdx, Reg64s.get64_rsi, Reg64s.get64_rdx] at hX
    rw [hbd.bp, hbd.r12] at hX
    exact prodX_of (hprod.trans (by rw [hact]; rfl)) hX

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_4
    (hpre : Sep.Pre S g F produceA 12 s)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec)
    (hout : ∀ l ∈ Program.labels produceAsm, label l ≠ label "exit")
    (hdup : Sep.SpecWithExit Names.dup dupA 2 dupQ dupX)
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.4" → Obl S g F s ra w cp blk := by
  have hTn : s.regs.rsi.toBitVec.toNat < g.h.n.toNat := hpre.args.1
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true] at ht
  obtain ⟨y, hbd, hlt, hact⟩ := ht
  have hk := hbd.rd_k
  simp only [Names.dup] at hdup
  kvcgen64 [hdup]
  all_goals try symexec_norm
  all_goals try dsimp only [V]
  vc_by_shape
  | load => with_reducible exact hbd.isSome_k
  | other =>
    refine Bd.callX (bd_next% hbd) hbd.bx hpre.ok
      ⟨show (BitVec.ofInt 64 (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).get!).toNat < _ by
          rw [hk]; exact Nat.lt_trans hlt hpre.args.2.1,
        hpre.args.2.1, hpre.args.2.2,
        show t.regs.r12.toBitVec.toNat < _ by rw [hbd.r12]; exact hTn⟩ ?_ ?_
    · intro _ t2 g2 y2 hbd2 hQ hok2
      obtain ⟨hK2, hf2, hal2⟩ := dupQ_of hQ hk
        (show t.regs.r12.toBitVec = s.regs.rsi.toBitVec from hbd.r12)
      kvcgen64
      all_goals try symexec_norm
      all_goals try dsimp only [V]
      vc_by_shape
      | goto ".LB.Emission.produce.2" =>
        cfg_goto
        · exact (bd_next% hbd2).stack
        · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
          exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
            (al_eq (by with_reducible rfl)).trans hal2, fun failed => hQ.2 (hal2.trans failed)⟩
        · simp [V]
    · intro tx hp harg
      apply ProofKit.intercept_exit hout
      refine Or.inr ⟨rfl, harg, hp.imp ?_⟩
      intro g2 hX
      dsimp only [dupX, rsi, rdx, Reg64s.get64_rsi, Reg64s.get64_rdx] at hX
      rw [hk, hbd.r12] at hX
      exact prodX_of (hprod.trans (by rw [hact]; rfl)) hX

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_0
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.0" → Obl S g F s ra w cp blk := by
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
  obtain ⟨y, hbd, hj, hact⟩ := ht
  have h13 := hbd.kind
  have h15 := hbd.opcode
  kvcgen64
  all_goals try symexec_norm
  all_goals try dsimp only [V]
  vc_by_shape
  | goto ".LB.Emission.produce.1" =>
    rename_i _ hc
    simp only [BitVec.and_self, beq_iff_eq, h15] at hc
    cfg_goto
    · exact (bd_next% hbd).stack
    · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true,
        true_or]
      exact ⟨y, bd_next% hbd, hact.trans (tail_push (by rw [free_of_const hc]; rfl))⟩
    · simp [V]
  | goto ".LB.Emission.produce.5" =>
    rename_i _ hc hl
    simp only [BitVec.and_self, beq_eq_false_iff_ne, h15] at hc
    rw [sub_beq8, h13, Bool.not_eq_true', beq_eq_false_iff_ne] at hl
    cfg_goto
    · exact (bd_next% hbd).stack
    · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨y, bd_next% hbd, not_free hj hl hc, hact⟩
    · simp [V]
  | closed => simp [V]
  | other =>
    rename_i _ hc hl
    rw [sub_beq8, h13, Bool.not_eq_false', beq_iff_eq] at hl
    try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true,
      true_or]
    exact ⟨y, bd_next% hbd, hact.trans (tail_push (by rw [free_of_label hl]; rfl))⟩

omit [Host] [FunDecls] in
private theorem fin_tail_zero {st : Flat.St} {x : StackSlot} {cp t : Word}
    (h : (canBeFreelyGenerated x || Flat.isSpilled st x) = false)
    (hc : cp ≠ Flat.NONE) (hz : Flat.depthOf st cp - Flat.maxDupDepth = 0) :
    fin (tail st x cp t) t = (.assertionFailed, st) := by
  rw [tail_block h hc, Flat.blockDupUnreachable, block_zero hz, fin_ne (by simp)]

omit [Host] [FunDecls] in
private theorem fin_tail_blocked {st : Flat.St} {x : StackSlot} {cp t e : Word}
    (h : (canBeFreelyGenerated x || Flat.isSpilled st x) = false)
    (hc : cp ≠ Flat.NONE) (hne : Flat.depthOf st cp - Flat.maxDupDepth ≠ 0)
    (he : e = Flat.depthOf st cp - Flat.maxDupDepth) :
    fin (tail st x cp t) t = (.blocked, {st with blockedOffset := cp, blockedExcess := e}) := by
  rw [tail_block h hc, Flat.blockDupUnreachable, block_ne hne, fin_ne (by simp)]
  exact congrArg (fun v => (Flat.Status.blocked,
    {st with blockedOffset := cp, blockedExcess := v})) he.symm

omit [Host] [FunDecls] in
private theorem blockedQ {g : G} {s t : MachineData} {w cp : Word}
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec)
    (hact : act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
      = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec)
    (hns : (canBeFreelyGenerated (StackSlot.ofWord w)
      || Flat.isSpilled (flat g) (StackSlot.ofWord w)) = false)
    (hc : cp ≠ Flat.NONE) (hne : Flat.depthOf (flat g) cp - Flat.maxDupDepth ≠ 0)
    (ha : al t = 1#8) :
    produceQ g (withExc (withOff g cp) (g.h.len + (18446744073709551600#64 - cp))) s t := by
  have hmodel := (congrArg (fun r => fin r s.regs.rsi.toBitVec) hact).trans
    (fin_tail_blocked hns hc hne (exc_eq g cp))
  exact prodQ (Keep.withBlk _ _) (hprod.trans hmodel) (flat_withBlk _ _) ha (by change 1#8 ≠ 2#8; decide)

omit [Host] [FunDecls] in
private theorem inv_result {S : Addr} {g g1 : G} {F : MProp 64} {s t : MachineData}
    {ra : Int64} {w cp : Word} {y : Scratch}
    (hbd : Bd S g1 F s ra w y cp t) (hok : g1.Ok) (hQ : produceQ g g1 s t) :
    Inv S g F s ra w cp (.label ".LB.Emission.produce.9") t := by
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self]
  exact ⟨g1, y, hbd, hok, hQ⟩

omit [Host] [FunDecls] in
private theorem produce_labels :
    Program.labels produceAsm = [Names.produce,
      ".LB.Emission.produce.0", ".LB.Emission.produce.1", ".LB.Emission.produce.2",
      ".LB.Emission.produce.3", ".LB.Emission.produce.4", ".LB.Emission.produce.5",
      ".LB.Emission.produce.6", ".LB.Emission.produce.7", ".LB.Emission.produce.8",
      ".LB.Emission.produce.9"] := rfl

-- Split the post-call block at instruction boundaries to bound kernel reduction.
-- Each slice is checked against the production block by definitional equality.
private def afterIsSpilledAsm : Program :=
  match Program.blockAt produceAsm ".LB.Emission.produce.5" with
  | some blk => blk.body.drop 3
  | none => []

omit [Host] [FunDecls] in
private theorem afterIsSpilledAsm_eq :
    afterIsSpilledAsm = parse("
	testb	%al, %al
	jne	.LB.Emission.produce.1
	cmpq	$-1, 8(%rsp)
	je	.LB.Emission.produce.7
	movq	$-16, %rax
	movq	8(%rsp), %rcx
	subq	%rcx, %rax
	addq	32(%rbx), %rax
	je	.LB.Emission.produce.6
	movq	8(%rsp), %rcx
	movq	%rcx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.9
") := rfl

omit [Host] [FunDecls] in
private theorem afterArithmeticAsm_eq :
    afterIsSpilledAsm.drop 8 = parse("
	je	.LB.Emission.produce.6
	movq	8(%rsp), %rcx
	movq	%rcx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.9
") := rfl

omit [Host] [FunDecls] in
private theorem afterTestsAsm_eq :
    afterIsSpilledAsm.drop 4 = parse("
	movq	$-16, %rax
	movq	8(%rsp), %rcx
	subq	%rcx, %rax
	addq	32(%rbx), %rax
	je	.LB.Emission.produce.6
	movq	8(%rsp), %rcx
	movq	%rcx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.9
") := rfl

omit [Host] [FunDecls] in
private theorem afterSubAsm_eq :
    afterIsSpilledAsm.drop 7 = parse("
	addq	32(%rbx), %rax
	je	.LB.Emission.produce.6
	movq	8(%rsp), %rcx
	movq	%rcx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.9
") := rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
private theorem afterArithmetic (t0 : MachineData) (y2 : Scratch)
    (hok2 : g.Ok)
    (_hfree : canBeFreelyGenerated (StackSlot.ofWord w) = false)
    (hact : act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
      = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec) :
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra w cp c u ∧
        Program.Decreases V (.label ".LB.Emission.produce.5") 7 t0 c j u
    ⦃ fun t2 => ∃ c, Bd S g F s ra w y2 cp c ∧
        t2.dmem = c.dmem ∧
        t2.regs.rsp = c.regs.rsp ∧ t2.regs.rbx = c.regs.rbx ∧
        t2.regs.rbp = c.regs.rbp ∧ t2.regs.r12 = c.regs.r12 ∧
        t2.regs.r13 = c.regs.r13 ∧ t2.regs.r14 = c.regs.r14 ∧
        t2.regs.r15 = c.regs.r15 ∧
        (canBeFreelyGenerated (StackSlot.ofWord w) ||
          Flat.isSpilled (flat g) (StackSlot.ofWord w)) = false ∧
        cp ≠ Flat.NONE ∧
        rax t2 = g.h.len + (18446744073709551600#64 - cp) ∧
        t2.status.zf = ((g.h.len + (18446744073709551600#64 - cp)) == 0#64) ⦄
      (afterIsSpilledAsm.drop 8)
    ⦃ (I' (.label ".LB.Emission.produce.6") 8); (Program.Intercept (Program.labels produceAsm) (s.pushRa ra) I' (E S g F s ra)) ⦄ := by
  dsimp only
  rw [afterArithmeticAsm_eq]
  refine ⟨?_⟩
  intro t2 ⟨c, hbd0, hdmem, hsp, hbx, hbp, h12, h13, h14, h15, hns, hc, hax, hzf⟩
  have hbd2 : Bd S g F s ra w y2 cp t2 :=
    hbd0.next hdmem hsp hbx hbp h12 h13 h14 h15
  have hk := hbd2.rd_k
  have hbx2 := hbd2.bx
  have hm2 := hbd2.mem
  have hax' : t2.regs.rax.toBitVec = g.h.len + (18446744073709551600#64 - cp) := hax
  rw [produce_labels]
  kvcgen64
  all_goals try symexec_norm
  all_goals simp only [hbx2, hk, hax', hzf, rd_len' hm2] at *
  all_goals try dsimp only [V]
  vc_by_shape
  | load =>
    first
    | with_reducible exact hbd2.isSome_k
    | with_reducible exact isSome_off' hm2
    | with_reducible exact isSome_exc' (store_off' hm2 cp)
  | goto ".LB.Emission.produce.6" =>
    have hz0 : Flat.depthOf (flat g) cp - Flat.maxDupDepth = 0 :=
      (exc_eq g cp).symm.trans (beq_iff_eq.mp (by assumption))
    cfg_goto
    · exact hbd2.stack
    · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨g, y2, bd_next% hbd2, hok2, Keep.refl _,
        hprod.trans ((congrArg (fun r => fin r s.regs.rsi.toBitVec) hact).trans
          (fin_tail_zero hns hc hz0))⟩
    · simp [V]
  | goto ".LB.Emission.produce.9" =>
    have hne : Flat.depthOf (flat g) cp - Flat.maxDupDepth ≠ 0 := by
      rw [← exc_eq]; exact beq_eq_false_iff_ne.mp (by assumption)
    have hm3 := store_exc' (store_off' hm2 cp) (g.h.len + (18446744073709551600#64 - cp))
    cfg_goto
    · exact hbd2.stack
    · refine inv_result (g1 := withExc (withOff g cp)
        (g.h.len + (18446744073709551600#64 - cp))) (y := y2) ?_ (Ok.withBlk hok2 _ _) ?_
      · exact bd_step% hbd2 hm3
      · exact blockedQ (g := g) (s := s) (w := w) (cp := cp) hprod hact hns hc hne rfl
    · simp [V]
  | closed => simp [V]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
private theorem afterSub (t0 : MachineData) (y2 : Scratch)
    (hok2 : g.Ok)
    (hfree : canBeFreelyGenerated (StackSlot.ofWord w) = false)
    (hact : act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
      = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec) :
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra w cp c u ∧
        Program.Decreases V (.label ".LB.Emission.produce.5") 7 t0 c j u
    ⦃ fun t2 => ∃ c, Bd S g F s ra w y2 cp c ∧
        t2.dmem = c.dmem ∧
        t2.regs.rsp = c.regs.rsp ∧ t2.regs.rbx = c.regs.rbx ∧
        t2.regs.rbp = c.regs.rbp ∧ t2.regs.r12 = c.regs.r12 ∧
        t2.regs.r13 = c.regs.r13 ∧ t2.regs.r14 = c.regs.r14 ∧
        t2.regs.r15 = c.regs.r15 ∧
        (canBeFreelyGenerated (StackSlot.ofWord w) ||
          Flat.isSpilled (flat g) (StackSlot.ofWord w)) = false ∧
        cp ≠ Flat.NONE ∧ rax t2 = 18446744073709551600#64 - cp ⦄
      (afterIsSpilledAsm.drop 7)
    ⦃ (I' (.label ".LB.Emission.produce.6") 8); (Program.Intercept (Program.labels produceAsm) (s.pushRa ra) I' (E S g F s ra)) ⦄ := by
  dsimp only
  rw [afterSubAsm_eq]
  refine ⟨?_⟩
  intro t2 ⟨c, hbd0, hdmem, hsp, hbx, hbp, h12, h13, h14, h15, hns, hc, hax⟩
  have hbd2 : Bd S g F s ra w y2 cp t2 :=
    hbd0.next hdmem hsp hbx hbp h12 h13 h14 h15
  have hlast := afterArithmetic S g F s ra w cp t0 y2 hok2 hfree hact hprod
  dsimp only at hlast
  rw [afterArithmeticAsm_eq] at hlast
  have hbx2 := hbd2.bx
  have hm2 := hbd2.mem
  have hax' : t2.regs.rax.toBitVec = 18446744073709551600#64 - cp := hax
  rw [produce_labels] at hlast ⊢
  kvcgen64 [hlast]
  all_goals try symexec_norm
  all_goals simp only [hbx2, hax', rd_len' hm2] at *
  vc_by_shape
  | load => with_reducible exact isSome_len' hm2
  | other =>
    exact ⟨t2, hbd2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hns, hc, True.intro, rfl⟩

omit [Host] [FunDecls] in
private theorem afterLoadAsm_eq :
    afterIsSpilledAsm.drop 6 = parse("
	subq	%rcx, %rax
	addq	32(%rbx), %rax
	je	.LB.Emission.produce.6
	movq	8(%rsp), %rcx
	movq	%rcx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.9
") := rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
private theorem afterLoad (t0 : MachineData) (y2 : Scratch)
    (hok2 : g.Ok)
    (hfree : canBeFreelyGenerated (StackSlot.ofWord w) = false)
    (hact : act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
      = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec) :
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra w cp c u ∧
        Program.Decreases V (.label ".LB.Emission.produce.5") 7 t0 c j u
    ⦃ fun t2 => ∃ c, Bd S g F s ra w y2 cp c ∧
        t2.dmem = c.dmem ∧
        t2.regs.rsp = c.regs.rsp ∧ t2.regs.rbx = c.regs.rbx ∧
        t2.regs.rbp = c.regs.rbp ∧ t2.regs.r12 = c.regs.r12 ∧
        t2.regs.r13 = c.regs.r13 ∧ t2.regs.r14 = c.regs.r14 ∧
        t2.regs.r15 = c.regs.r15 ∧
        (canBeFreelyGenerated (StackSlot.ofWord w) ||
          Flat.isSpilled (flat g) (StackSlot.ofWord w)) = false ∧
        cp ≠ Flat.NONE ∧ rax t2 = 18446744073709551600#64 ∧ t2.regs.rcx.toBitVec = cp ⦄
      (afterIsSpilledAsm.drop 6)
    ⦃ (I' (.label ".LB.Emission.produce.6") 8);
      (Program.Intercept (Program.labels produceAsm) (s.pushRa ra) I' (E S g F s ra)) ⦄ := by
  dsimp only
  rw [afterLoadAsm_eq]
  refine ⟨?_⟩
  intro t2 ⟨c, hbd0, hdmem, hsp, hbx, hbp, h12, h13, h14, h15, hns, hc, hax, hcx⟩
  have hbd2 : Bd S g F s ra w y2 cp t2 :=
    hbd0.next hdmem hsp hbx hbp h12 h13 h14 h15
  have hnext := afterSub S g F s ra w cp t0 y2 hok2 hfree hact hprod
  dsimp only at hnext
  rw [afterSubAsm_eq] at hnext
  have hax' : t2.regs.rax.toBitVec = 18446744073709551600#64 := hax
  have hcx' : t2.regs.rcx.toBitVec = cp := hcx
  rw [produce_labels] at hnext ⊢
  kvcgen64 [hnext]
  all_goals try symexec_norm
  all_goals simp only [hax', hcx'] at *
  vc_by_shape
  | other =>
    exact ⟨t2, hbd2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hns, hc, (by trivial)⟩

omit [Host] [FunDecls] in
private theorem afterMoveAsm_eq :
    afterIsSpilledAsm.drop 5 = parse("
	movq	8(%rsp), %rcx
	subq	%rcx, %rax
	addq	32(%rbx), %rax
	je	.LB.Emission.produce.6
	movq	8(%rsp), %rcx
	movq	%rcx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.9
") := rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
private theorem afterMove (t0 : MachineData) (y2 : Scratch)
    (hok2 : g.Ok)
    (hfree : canBeFreelyGenerated (StackSlot.ofWord w) = false)
    (hact : act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
      = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec) :
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra w cp c u ∧
        Program.Decreases V (.label ".LB.Emission.produce.5") 7 t0 c j u
    ⦃ fun t2 => ∃ c, Bd S g F s ra w y2 cp c ∧
        t2.dmem = c.dmem ∧
        t2.regs.rsp = c.regs.rsp ∧ t2.regs.rbx = c.regs.rbx ∧
        t2.regs.rbp = c.regs.rbp ∧ t2.regs.r12 = c.regs.r12 ∧
        t2.regs.r13 = c.regs.r13 ∧ t2.regs.r14 = c.regs.r14 ∧
        t2.regs.r15 = c.regs.r15 ∧
        (canBeFreelyGenerated (StackSlot.ofWord w) ||
          Flat.isSpilled (flat g) (StackSlot.ofWord w)) = false ∧
        cp ≠ Flat.NONE ∧ rax t2 = 18446744073709551600#64 ⦄
      (afterIsSpilledAsm.drop 5)
    ⦃ (I' (.label ".LB.Emission.produce.6") 8);
      (Program.Intercept (Program.labels produceAsm) (s.pushRa ra) I' (E S g F s ra)) ⦄ := by
  dsimp only
  rw [afterMoveAsm_eq]
  refine ⟨?_⟩
  intro t2 ⟨c, hbd0, hdmem, hsp, hbx, hbp, h12, h13, h14, h15, hns, hc, hax⟩
  have hbd2 : Bd S g F s ra w y2 cp t2 :=
    hbd0.next hdmem hsp hbx hbp h12 h13 h14 h15
  have hnext := afterLoad S g F s ra w cp t0 y2 hok2 hfree hact hprod
  dsimp only at hnext
  rw [afterLoadAsm_eq] at hnext
  have hk := hbd2.rd_k
  have hax' : t2.regs.rax.toBitVec = 18446744073709551600#64 := hax
  rw [produce_labels] at hnext ⊢
  kvcgen64 [hnext]
  all_goals try symexec_norm
  all_goals simp only [hk, hax'] at *
  vc_by_shape
  | load => with_reducible exact hbd2.isSome_k
  | other =>
    exact ⟨t2, hbd2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hns, hc, (by trivial), (by trivial)⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
private theorem afterTests (t0 : MachineData) (y2 : Scratch)
    (hok2 : g.Ok)
    (hfree : canBeFreelyGenerated (StackSlot.ofWord w) = false)
    (hact : act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
      = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec) :
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra w cp c u ∧
        Program.Decreases V (.label ".LB.Emission.produce.5") 7 t0 c j u
    ⦃ fun t2 => ∃ c, Bd S g F s ra w y2 cp c ∧
        t2.dmem = c.dmem ∧
        t2.regs.rsp = c.regs.rsp ∧ t2.regs.rbx = c.regs.rbx ∧
        t2.regs.rbp = c.regs.rbp ∧ t2.regs.r12 = c.regs.r12 ∧
        t2.regs.r13 = c.regs.r13 ∧ t2.regs.r14 = c.regs.r14 ∧
        t2.regs.r15 = c.regs.r15 ∧
        Flat.isSpilled (flat g) (StackSlot.ofWord w) = false ∧ cp ≠ Flat.NONE ⦄
      (afterIsSpilledAsm.drop 4)
    ⦃ (I' (.label ".LB.Emission.produce.6") 8); (Program.Intercept (Program.labels produceAsm) (s.pushRa ra) I' (E S g F s ra)) ⦄ := by
  dsimp only
  rw [afterTestsAsm_eq]
  refine ⟨?_⟩
  intro t2 ⟨c, hbd0, hdmem, hsp, hbx, hbp, h12, h13, h14, h15, hs, hc⟩
  have hbd2 : Bd S g F s ra w y2 cp t2 :=
    hbd0.next hdmem hsp hbx hbp h12 h13 h14 h15
  have hlast := afterMove S g F s ra w cp t0 y2 hok2 hfree hact hprod
  dsimp only at hlast
  rw [afterMoveAsm_eq] at hlast
  have hk := hbd2.rd_k
  have hbx2 := hbd2.bx
  have hm2 := hbd2.mem
  rw [produce_labels] at hlast ⊢
  kvcgen64 [hlast]
  all_goals try symexec_norm
  all_goals simp only [hbx2, hk, rd_len' hm2] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact hbd2.isSome_k
    | with_reducible exact isSome_len' hm2
  | other =>
    refine ⟨t2, hbd2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hc, (by trivial)⟩
    rw [hfree, hs]; rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
private theorem afterIsSpilled (t0 t2 : MachineData) (y2 : Scratch)
    (hbd2 : Bd S g F s ra w y2 cp t2)
    (hok2 : g.Ok)
    (hal2 : al t2 = if Flat.isSpilled (flat g) (StackSlot.ofWord w) then 1#8 else 0#8)
    (hfree : canBeFreelyGenerated (StackSlot.ofWord w) = false)
    (hact : act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
      = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec) :
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra w cp c u ∧
        Program.Decreases V (.label ".LB.Emission.produce.5") 7 t0 c j u
    WP.wp afterIsSpilledAsm (I' (.label ".LB.Emission.produce.6") 8)
      (Program.Intercept (Program.labels produceAsm) (s.pushRa ra) I' (E S g F s ra)) t2 := by
  dsimp only
  have hrest := afterTests S g F s ra w cp t0 y2 hok2 hfree hact hprod
  dsimp only at hrest
  rw [afterTestsAsm_eq] at hrest
  have hk := hbd2.rd_k
  have hbx2 := hbd2.bx
  have hm2 := hbd2.mem
  rw [produce_labels] at hrest ⊢
  change WP.wp (parse("
	testb	%al, %al
	jne	.LB.Emission.produce.1
	cmpq	$-1, 8(%rsp)
	je	.LB.Emission.produce.7
	movq	$-16, %rax
	movq	8(%rsp), %rcx
	subq	%rcx, %rax
	addq	32(%rbx), %rax
	je	.LB.Emission.produce.6
	movq	8(%rsp), %rcx
	movq	%rcx, 16448(%rbx)
	movq	%rax, 16456(%rbx)
	movl	$1, %eax
	jmp	.LB.Emission.produce.9
")) _ _ t2
  kvcgen64 [hrest]
  all_goals try symexec_norm
  all_goals simp only [hbx2, hk, rd_len' hm2] at *
  all_goals try dsimp only [V]
  vc_by_shape
  | load =>
    first
    | with_reducible exact hbd2.isSome_k
    | with_reducible exact isSome_len' hm2
  | goto ".LB.Emission.produce.1" =>
    rename_i _ hz
    have hs := bit_true hal2 (al_ne hz)
    cfg_goto
    · exact (bd_next% hbd2).stack
    · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true,
        true_or]
      exact ⟨y2, bd_next% hbd2, hact.trans (tail_push (by rw [hs, Bool.or_true]))⟩
    · simp [V]
  | goto ".LB.Emission.produce.7" =>
    rename_i hz hn
    have hns : (canBeFreelyGenerated (StackSlot.ofWord w)
        || Flat.isSpilled (flat g) (StackSlot.ofWord w)) = false := by
      rw [hfree, bit_false hal2 (al_zero hz)]; rfl
    have hnone : cp = Flat.NONE := eq_of_z hn
    cfg_goto
    · exact (bd_next% hbd2).stack
    · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨g, y2, bd_next% hbd2, hok2, Keep.refl _,
        hprod.trans (by rw [hact, tail_none hns hnone, fin_ne (by simp)])⟩
    · simp [V]
  | other =>
    refine ⟨t2, hbd2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · apply bit_false hal2; apply al_zero; assumption
    · apply ne_of_z; assumption

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_5
    (hpre : Sep.Pre S g F produceA 12 s)
    (hw : g.tgt[s.regs.rsi.toBitVec.toNat]'hpre.args.1 = w)
    (hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec)
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.produce.5" → Obl S g F s ra w cp blk := by
  have hTn : s.regs.rsi.toBitVec.toNat < g.h.n.toNat := hpre.args.1
  have hspill := hspill.with_free 2
  simp only [Names.isSpilled] at hspill
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
  obtain ⟨y, hbd, hfree, hact⟩ := ht
  kvcgen64 [hspill]
  all_goals try symexec_norm
  refine Bd.call (bd_next% hbd) hbd.bx hpre.ok
    (fun i h => spill_mem hTn hw i (by rw [← hbd.bp]; exact h)) ?_
  intro _ t2 g2 y2 hbd2 hQ hok2
  obtain ⟨rfl, hal2⟩ := spillQ_of hQ (show t.regs.rbp.toBitVec = w from hbd.bp)
  simpa only [produce_labels, Names.produce, afterIsSpilledAsm_eq, Program.Decreases] using
    (afterIsSpilled S g2 F s ra w cp t t2 y2 hbd2 hok2 hal2 hfree hact hprod)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_entry
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .entry → Obl S g F s ra w cp blk := by
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv] at ht
  subst ht
  kvcgen64
  simp only [Inv, Names.produce, ↓reduceIte]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
theorem b_fn
    (hpre : Sep.Pre S g F produceA 12 s)
    (hw : g.tgt[s.regs.rsi.toBitVec.toNat]'hpre.args.1 = w)
    (hcp : Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord w) = cp)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    : produceAsm.ForallBlocks fun blk =>
      blk.label = .label Names.produce → Obl S g F s ra w cp blk := by
  have hTn : s.regs.rsi.toBitVec.toNat < g.h.n.toNat := hpre.args.1
  have hcopy := hcopy.with_free 2
  simp only [Names.shallowestCopyPosition] at hcopy
  cfg_block [Obl, Names.produce]
  intro t ht
  simp only [Inv, Names.produce, ↓reduceIte] at ht
  subst ht
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  have hk0 : Kp S g F s ra fr (s.pushRa ra) := Kp.init hm
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, rfl⟩ := split12 hfr
  have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
  have hr : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  obtain ⟨p1, p2, p3, p4, p5, p6, hm6⟩ := pushes (r := (s.pushRa ra).regs.rsp.toBitVec)
    (a := (s.pushRa ra).regs.r15.toBitVec) (b := (s.pushRa ra).regs.r14.toBitVec)
    (c := (s.pushRa ra).regs.r13.toBitVec) (d := (s.pushRa ra).regs.r12.toBitVec)
    (e := (s.pushRa ra).regs.rbp.toBitVec) (f := (s.pushRa ra).regs.rbx.toBitVec)
    hk0.mem hr rfl rfl rfl rfl rfl rfl
  have hTn' : (s.pushRa ra).regs.rsi.toBitVec.toNat < g.h.n.toNat := hTn
  obtain ⟨q1, q2, q3, q4⟩ := tgt_isSome hm6 hS hTn'
  kvcgen64 [not_reg_spec, hcopy]
  all_goals try symexec_norm
  all_goals try dsimp only [V]
  vc_by_shape
  | load =>
    first
    | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
    | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
    | with_reducible exact q1 | with_reducible exact q2 | with_reducible exact q3
    | with_reducible exact q4
  | closed => decide
  | other =>
    refine Bd.call (Bd.entry (y := ⟨x0, x1, x2, x3, x5⟩) (k := x4)
      hm6 hTn' hS rfl hr rfl rfl rfl rfl rfl rfl rfl hw) hS hpre.ok trivial ?_
    intro hbd0 t1 g1 y1 hbd1 hQ hok1
    obtain ⟨hg, hax⟩ := copyQ_of hQ (by exact hbd0.bp)
    subst hg
    rw [hcp] at hax
    have hm1k := hbd1.mem_k cp
    have hbx1 := hbd1.bx
    have hst := hbd1.rd_st
    have h13 := hbd1.kind
    kvcgen64 [not_reg_spec]
    all_goals try symexec_norm
    all_goals try simp only [hax, hbx1, hst, rd_len' hm1k] at *
    all_goals try dsimp only [V]
    vc_by_shape
    | load =>
      first
      | with_reducible exact hbd1.isSome_k | with_reducible exact hbd1.isSome_st _
      | with_reducible exact isSome_len' hm1k
    | goto ".LB.Emission.produce.3" =>
      rename_i hl
      rw [sub_beq8, h13, ← junk_iff] at hl
      cfg_goto
      · exact (bd_step% hbd1 hm1k).stack
      · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true]
        exact ⟨y1, bd_step% hbd1 hm1k, act_junk hl⟩
      · simp [V]
    | goto ".LB.Emission.produce.0" =>
      rename_i hl hn
      rw [sub_beq8, h13, ← junk_iff] at hl
      cfg_goto
      · exact (bd_step% hbd1 hm1k).stack
      · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨y1, bd_step% hbd1 hm1k, hl, act_tail hl (Or.inl (eq_of_z hn))⟩
      · simp [V]
    | goto ".LB.Emission.produce.4" =>
      rename_i hl hn hb
      rw [sub_beq8, h13, ← junk_iff] at hl
      have hc : cp ≠ Flat.NONE := ne_of_z hn
      cfg_goto
      · exact (bd_step% hbd1 hm1k).stack
      · try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨y1, bd_step% hbd1 hm1k, copy_lt hcp hc,
          act_dup hl hc ((reach_iff (flat g1) cp).mpr (le_of_be hb))⟩
      · simp [V]
    | closed => simp [V]
    | other =>
      rename_i hl hn hb
      rw [sub_beq8, h13, ← junk_iff] at hl
      try simp only [Inv, Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨y1, bd_step% hbd1 hm1k, hl, act_tail hl (Or.inr (Bool.eq_false_iff.mpr
        fun h => not_le_of_be hb ((reach_iff (flat g1) cp).mp h)))⟩

end
end ProduceProof

theorem produce_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels produceAsm, label l ≠ label "exit")
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    (hpush : Sep.SpecWithExit Names.push pushA 2 pushQ pushX)
    (hdup : Sep.SpecWithExit Names.dup dupA 2 dupQ dupX) :
    UnitThmWithExit produceAsm produceA 12 produceQ produceX := by
  intro S g F s ra
  refine ⟨fun t ⟨ht, hpre⟩ => ?_⟩
  subst ht
  let w := g.tgt[s.regs.rsi.toBitVec.toNat]'hpre.args.1
  let cp := Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord w)
  have hw : g.tgt[s.regs.rsi.toBitVec.toNat]'hpre.args.1 = w := rfl
  have hcp : Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord w) = cp := rfl
  have hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = ProduceProof.fin (ProduceProof.act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec)
        s.regs.rsi.toBitVec := by
    rw [ProduceProof.produce_eq, ProduceProof.get_target (i := s.regs.rsi.toBitVec) hpre.ok hpre.args.1, hw, hcp]
  refine Program.WP.cfg (ProduceProof.Inv S g F s ra w cp) ProduceProof.V ?_ rfl
  refine forallBlocks_cases [.label ".LB.Emission.produce.9",
    .label ".LB.Emission.produce.6",
    .label ".LB.Emission.produce.7",
    .label ".LB.Emission.produce.2",
    .label ".LB.Emission.produce.8",
    .label ".LB.Emission.produce.1",
    .label ".LB.Emission.produce.3",
    .label ".LB.Emission.produce.4",
    .label ".LB.Emission.produce.0",
    .label ".LB.Emission.produce.5",
    .entry,
    .label Names.produce] (by simp only [Names.produce]; cfg_labels) ?_
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ProduceProof.b_9 S g F s ra w cp
  · exact ProduceProof.b_6 S g F s ra w cp hexit hout
  · exact ProduceProof.b_7 S g F s ra w cp hexit hout
  · exact ProduceProof.b_2 S g F s ra w cp hpre hexit hout
  · exact ProduceProof.b_8 S g F s ra w cp
  · exact ProduceProof.b_1 S g F s ra w cp hpre hprod hout hpush
  · exact ProduceProof.b_3 S g F s ra w cp hpre hprod hout hpush
  · exact ProduceProof.b_4 S g F s ra w cp hpre hprod hout hdup
  · exact ProduceProof.b_0 S g F s ra w cp
  · exact ProduceProof.b_5 S g F s ra w cp hpre hw hprod hspill
  · exact ProduceProof.b_entry S g F s ra w cp
  · exact ProduceProof.b_fn S g F s ra w cp hpre hw hcp hcopy

end FlatShuffler.Unit
