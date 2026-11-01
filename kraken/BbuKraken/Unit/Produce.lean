module

public import BbuKraken.Unit.ProduceLemmas
import all BbuKraken.Unit.ProduceLemmas

@[expose] public section

/-!
# `produce`

`c/bbu/<Names.produce>.S`: 6 `pushq` and `subq $8`, so 8 free words (7 and one for the return
address of a callee). It reads the target word `m_target[t]` and calls `shallowestCopyPosition`,
then `push`, `dup` or `isSpilled` and `push`, or writes `m_blocked`. Then it asserts
`m_positionOf[t] = size - 1` and decrements `m_pendingGenerations`.

The preconditions of the callees: the target word is in the view (`t < n`); its id is in
`splIds` (`isSpilledA`), and `Pre.ok` gives `G.Ok.spl` to `isSpilled`; the copy for `dup` is
below `size ≤ n`; `len < n` and `nops < 6n` (`pushA`, `dupA`). The caller is `generate`, after
its check `t < n`.

The proof is a CFG proof (`Program.WP.cfg`). Between the pushes and the pops the state is
`ProduceProof.Bd`; `(%rsp)` holds the copy position `cp`. The invariant at each label names the
part of `Flat.produce` that is left: `act` (the action on the target slot) and `fin` (the check
after it). The lemmas are in `BbuKraken.Unit.ProduceLemmas`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep

local macro "bd_next% " h:term:max : term =>
  `(ProduceProof.Bd.next $h (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl))

local macro "bd_step% " h:term:max hm:term:max : term =>
  `(ProduceProof.Bd.step $h $hm (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl))

set_option linter.unusedSimpArgs false in
open ProduceProof in
theorem produce_unit [Host] [FunDecls]
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    (hpush : Sep.Spec Names.push pushA 0 pushQ)
    (hdup : Sep.Spec Names.dup dupA 0 dupQ) :
    UnitThm produceAsm produceA 8 produceQ := by
  simp only [Names.shallowestCopyPosition, Names.isSpilled, Names.push, Names.dup]
    at hcopy hspill hpush hdup
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  have hk0 : Kp S g F s ra fr (s.pushRa ra) := Kp.init hm
  have hTn : s.regs.rsi.toBitVec.toNat < g.h.n.toNat := hpre.args.1
  obtain ⟨w, hw⟩ : ∃ w, g.tgt[s.regs.rsi.toBitVec.toNat] = w := ⟨_, rfl⟩
  obtain ⟨cp, hcp⟩ : ∃ cp, Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord w) = cp :=
    ⟨_, rfl⟩
  have hprod : Flat.produce (flat g) s.regs.rsi.toBitVec
      = fin (act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec) s.regs.rsi.toBitVec := by
    rw [produce_eq, get_target hpre.ok hTn, hw, hcp]
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.produce then t = s.pushRa ra
        else if l = ".LB.Emission.produce.0" then ∃ y, Bd S g F s ra w y cp t
          ∧ isJunk (StackSlot.ofWord w) = false
          ∧ act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
            = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
        else if l = ".LB.Emission.produce.1" ∨ l = ".LB.Emission.produce.4" then ∃ y, Bd S g F s ra w y cp t
          ∧ act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
            = Flat.push (flat g) (StackSlot.ofWord w) s.regs.rsi.toBitVec
        else if l = ".LB.Emission.produce.2" then ∃ g1 y r, Bd S g1 F s ra w y cp t ∧ g1.Ok ∧ Keep g g1
          ∧ Flat.produce (flat g) s.regs.rsi.toBitVec = fin r s.regs.rsi.toBitVec
          ∧ flat g1 = r.2 ∧ al t = code r.1
        else if l = ".LB.Emission.produce.3" then ∃ g1 y, Bd S g1 F s ra w y cp t ∧ g1.Ok ∧ produceQ g g1 s t
        else if l = ".LB.Emission.produce.5" then ∃ y, Bd S g F s ra w y cp t ∧ cp.toNat < g.h.len.toNat
          ∧ act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
            = Flat.dup (flat g) cp s.regs.rsi.toBitVec
        else if l = ".LB.Emission.produce.6" then ∃ y, Bd S g F s ra w y cp t
          ∧ canBeFreelyGenerated (StackSlot.ofWord w) = false
          ∧ act (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
            = tail (flat g) (StackSlot.ofWord w) cp s.regs.rsi.toBitVec
        else if l = ".LB.Emission.produce.7" then ∃ g1 y, Bd S g1 F s ra w y cp t ∧ g1.Ok ∧ Keep g g1
          ∧ Flat.produce (flat g) s.regs.rsi.toBitVec = (.assertionFailed, flat g1)
        else False
      | .exit, _ => False)
    (fun l _ => if l = ".LB.Emission.produce.3" then 0 else if l = ".LB.Emission.produce.2" ∨ l = ".LB.Emission.produce.7" ∨ l = ".LB.Emission.produce.1" then 1 else 2)
    ?_ rfl
  cfg_blocks
  case «.LB.Emission.produce.3» t ht =>
    simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self] at ht
    obtain ⟨g1, y, hbd, hok1, hQ⟩ := ht
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hbd.isSome_pops
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | load =>
      first
      | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
      | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
    | retAddr =>
      refine (congrArg Option.isSome (hbd.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).retAddr).trans rfl
      all_goals rfl
    | ret =>
      refine Kp.ret (hbd.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) rfl hok1 fun t' _ hax =>
        ⟨hQ.1, hQ.2.1, by show (rax t').setWidth 8 = _; rw [hax]; exact hQ.2.2⟩
      all_goals rfl
  case «.LB.Emission.produce.7» t ht =>
    simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
    obtain ⟨g1, y, hbd, hok1, hK1, hP⟩ := ht
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.Emission.produce.3" =>
      cfg_goto
      · exact (bd_next% hbd).stack
      · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨g1, y, bd_next% hbd, hok1, prodQ hK1 hP rfl rfl⟩
      · simp
  case «.LB.Emission.produce.2» t ht =>
    simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
    obtain ⟨g1, y, r, hbd, hok1, hK1, hP, hf, hal⟩ := ht
    have hTm : s.regs.rsi.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hTn hpre.ok.n
    have hbx1 := hbd.bx
    have hr14 := hbd.r14
    have hm1 := hbd.mem
    kvcgen64
    all_goals try symexec_norm
    all_goals simp only [hbx1, hr14, rd_len' hm1, rd_pos' hm1 hTm, rd_pend' hm1, add_neg_one] at *
    vc_by_shape
    | load =>
      first
      | with_reducible exact isSome_len' hm1
      | with_reducible exact isSome_pos' hm1 hTm
      | with_reducible exact isSome_pend' hm1
    | goto ".LB.Emission.produce.3" =>
      have hne : al t ≠ 0#8 := al_ne (by with_reducible assumption)
      have hr : r.1 ≠ .done := fun e => hne (hal.trans (by rw [e]; rfl))
      cfg_goto
      · exact (bd_next% hbd).stack
      · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨g1, y, bd_next% hbd, hok1,
          prodQ hK1 (hP.trans (fin_ne hr)) hf ((al_eq (by with_reducible rfl)).trans hal)⟩
      · simp
    | goto ".LB.Emission.produce.7" =>
      have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
      have hd : r.1 = .done := code_eq_zero (hal.symm.trans hal0)
      have hne : g1.h.pos[s.regs.rsi.toBitVec.toNat] ≠ g1.h.len - 1#64 :=
        ne_of_nz (by with_reducible assumption)
      have hF : Flat.produce (flat g) s.regs.rsi.toBitVec = (.assertionFailed, flat g1) := by
        have h2 : Flat.get r.2.pos s.regs.rsi.toBitVec ≠ r.2.size - 1 := by
          rw [← hf]; show Flat.get g1.h.pos _ ≠ g1.h.len - 1; rw [get_eq _ hTm]; exact hne
        rw [hP, fin_bad hd h2, hf]
      cfg_goto
      · exact (bd_next% hbd).stack
      · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨g1, y, bd_next% hbd, hok1, hK1, hF⟩
      · simp
    | closed => simp
    | other =>
      have hal0 : al t = 0#8 := al_zero (by with_reducible assumption)
      have hd : r.1 = .done := code_eq_zero (hal.symm.trans hal0)
      have heq : g1.h.pos[s.regs.rsi.toBitVec.toNat] = g1.h.len - 1#64 :=
        eq_of_nz (by with_reducible assumption)
      have hF : Flat.produce (flat g) s.regs.rsi.toBitVec = (.done, { r.2 with pend := r.2.pend - 1 }) := by
        have h2 : Flat.get r.2.pos s.regs.rsi.toBitVec = r.2.size - 1 := by
          rw [← hf]; show Flat.get g1.h.pos _ = g1.h.len - 1; rw [get_eq _ hTm]; exact heq
        rw [hP, fin_ok hd h2]
      have hm2 := store_pend' hm1 (g1.h.pend - 1#64)
      simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨withPend g1 (g1.h.pend - 1#64), y, bd_step% hbd hm2, Ok.withPend hok1 _,
        prodQ (Keep.trans hK1 (Keep.withPend _)) hF (by rw [flat_withPend, ← hf]; rfl)
          ((al_eq (by with_reducible rfl)).trans hal0)⟩
  case «.LB.Emission.produce.1» t ht =>
    simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true] at ht
    obtain ⟨y, hbd, hact⟩ := ht
    kvcgen64 [hpush]
    all_goals try symexec_norm
    refine Bd.call (bd_next% hbd) hbd.bx hpre.ok
      ⟨hpre.args.2.1, hpre.args.2.2, show t.regs.r12.toBitVec.toNat < _ by rw [hbd.r12]; exact hTn⟩ ?_
    intro _ t2 g2 y2 hbd2 hQ hok2
    obtain ⟨hK2, hf2, hal2⟩ := pushQ_of hQ (show t.regs.rbp.toBitVec = w from hbd.bp)
      (show t.regs.r12.toBitVec = s.regs.rsi.toBitVec from hbd.r12)
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | closed => simp
    | goto ".LB.Emission.produce.2" =>
      cfg_goto
      · exact (bd_next% hbd2).stack
      · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
          (al_eq (by with_reducible rfl)).trans hal2⟩
      · simp
    | other =>
      simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
        (al_eq (by with_reducible rfl)).trans hal2⟩
  case «.LB.Emission.produce.4» t ht =>
    simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true] at ht
    obtain ⟨y, hbd, hact⟩ := ht
    kvcgen64 [hpush]
    all_goals try symexec_norm
    refine Bd.call (bd_next% hbd) hbd.bx hpre.ok
      ⟨hpre.args.2.1, hpre.args.2.2, show t.regs.r12.toBitVec.toNat < _ by rw [hbd.r12]; exact hTn⟩ ?_
    intro _ t2 g2 y2 hbd2 hQ hok2
    obtain ⟨hK2, hf2, hal2⟩ := pushQ_of hQ (show t.regs.rbp.toBitVec = w from hbd.bp)
      (show t.regs.r12.toBitVec = s.regs.rsi.toBitVec from hbd.r12)
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.Emission.produce.2" =>
      cfg_goto
      · exact (bd_next% hbd2).stack
      · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
          (al_eq (by with_reducible rfl)).trans hal2⟩
      · simp
    | other =>
      simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
      exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
        (al_eq (by with_reducible rfl)).trans hal2⟩
  case «.LB.Emission.produce.5» t ht =>
    simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true] at ht
    obtain ⟨y, hbd, hlt, hact⟩ := ht
    have hk := hbd.rd_k
    kvcgen64 [hdup]
    all_goals try symexec_norm
    vc_by_shape
    | load => with_reducible exact hbd.isSome_k
    | other =>
      refine Bd.call (bd_next% hbd) hbd.bx hpre.ok
        ⟨show (BitVec.ofInt 64 (t.dmem.loadInt t.regs.rsp.toBitVec 8).get!).toNat < _ by
            rw [hk]; exact Nat.lt_trans hlt hpre.args.2.1,
          hpre.args.2.1, hpre.args.2.2,
          show t.regs.r12.toBitVec.toNat < _ by rw [hbd.r12]; exact hTn⟩ ?_
      intro _ t2 g2 y2 hbd2 hQ hok2
      obtain ⟨hK2, hf2, hal2⟩ := dupQ_of hQ hk
        (show t.regs.r12.toBitVec = s.regs.rsi.toBitVec from hbd.r12)
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | goto ".LB.Emission.produce.2" =>
        cfg_goto
        · exact (bd_next% hbd2).stack
        · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
          exact ⟨g2, y2, _, bd_next% hbd2, hok2, hK2, hprod.trans (by rw [hact]), hf2,
            (al_eq (by with_reducible rfl)).trans hal2⟩
        · simp
  case «.LB.Emission.produce.0» t ht =>
    simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
    obtain ⟨y, hbd, hj, hact⟩ := ht
    have h13 := hbd.r13
    have h15 := hbd.r15
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.Emission.produce.1" =>
      rename_i _ hl
      rw [sub_beq8, h13, beq_iff_eq] at hl
      cfg_goto
      · exact (bd_next% hbd).stack
      · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true,
          true_or]
        exact ⟨y, bd_next% hbd, hact.trans (tail_push (by rw [free_of_label hl]; rfl))⟩
      · simp
    | goto ".LB.Emission.produce.6" =>
      rename_i _ hc _ hl
      rw [sub_beq8, h13, beq_eq_false_iff_ne] at hl
      rw [test_beq8, h15, bne_iff_ne] at hc
      cfg_goto
      · exact (bd_next% hbd).stack
      · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨y, bd_next% hbd, not_free hj hl hc, hact⟩
      · simp
    | closed => simp
    | other =>
      rename_i _ hc _ _
      rw [test_beq8, h15, bne_eq_false_iff_eq] at hc
      simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true,
        true_or]
      exact ⟨y, bd_next% hbd, hact.trans (tail_push (by rw [free_of_const hc]; rfl))⟩
  case «.LB.Emission.produce.6» t ht =>
    simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or] at ht
    obtain ⟨y, hbd, hfree, hact⟩ := ht
    kvcgen64 [hspill]
    all_goals try symexec_norm
    refine Bd.call (bd_next% hbd) hbd.bx hpre.ok
      (fun i h => spill_mem hTn hw i (by rw [← hbd.bp]; exact h)) ?_
    intro _ t2 g2 y2 hbd2 hQ hok2
    obtain ⟨rfl, hal2⟩ := spillQ_of hQ (show t.regs.rbp.toBitVec = w from hbd.bp)
    have hk := hbd2.rd_k
    have hbx2 := hbd2.bx
    have hm2 := hbd2.mem
    kvcgen64
    all_goals try symexec_norm
    all_goals simp only [hbx2, hk, rd_len' hm2] at *
    vc_by_shape
    | load =>
      first
      | with_reducible exact hbd2.isSome_k
      | with_reducible exact isSome_len' hm2
      | with_reducible exact isSome_off' hm2
      | with_reducible exact isSome_exc' (store_off' hm2 cp)
    | goto ".LB.Emission.produce.1" =>
      rename_i _ hz
      have hs := bit_true hal2 (al_ne hz)
      cfg_goto
      · exact (bd_next% hbd2).stack
      · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true,
          true_or]
        exact ⟨y2, bd_next% hbd2, hact.trans (tail_push (by rw [hs, Bool.or_true]))⟩
      · simp
    | goto ".LB.Emission.produce.3" =>
      first
      | rename_i hz hn
        have hns : (canBeFreelyGenerated (StackSlot.ofWord w)
            || Flat.isSpilled (flat g2) (StackSlot.ofWord w)) = false := by
          rw [hfree, bit_false hal2 (al_zero hz)]; rfl
        have hnone : cp = Flat.NONE := eq_of_z hn
        cfg_goto
        · exact (bd_next% hbd2).stack
        · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
          exact ⟨g2, y2, bd_next% hbd2, hok2, prodQ (r := (.assertionFailed, flat g2)) (Keep.refl _)
            (hprod.trans (by rw [hact, tail_none hns hnone, fin_ne (by simp)])) rfl rfl⟩
        · simp
      | rename_i hz hn he
        have hns : (canBeFreelyGenerated (StackSlot.ofWord w)
            || Flat.isSpilled (flat g2) (StackSlot.ofWord w)) = false := by
          rw [hfree, bit_false hal2 (al_zero hz)]; rfl
        have hc : cp ≠ Flat.NONE := ne_of_z hn
        have hz0 : Flat.depthOf (flat g2) cp - Flat.maxDupDepth = 0 :=
          (exc_eq g2 cp).symm.trans (beq_iff_eq.mp he)
        cfg_goto
        · exact (bd_next% hbd2).stack
        · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
          exact ⟨g2, y2, bd_next% hbd2, hok2, prodQ (r := (.assertionFailed, flat g2)) (Keep.refl _)
            (hprod.trans (by rw [hact, tail_block hns hc, Flat.blockDupUnreachable, block_zero hz0,
              fin_ne (by simp)])) rfl rfl⟩
        · simp
      | rename_i hz hn he
        have hns : (canBeFreelyGenerated (StackSlot.ofWord w)
            || Flat.isSpilled (flat g2) (StackSlot.ofWord w)) = false := by
          rw [hfree, bit_false hal2 (al_zero hz)]; rfl
        have hc : cp ≠ Flat.NONE := ne_of_z hn
        have hne : Flat.depthOf (flat g2) cp - Flat.maxDupDepth ≠ 0 := by
          rw [← exc_eq]; exact beq_eq_false_iff_ne.mp he
        have hm3 := store_exc' (store_off' hm2 cp) (g2.h.len + (18446744073709551600#64 - cp))
        cfg_goto
        · exact (bd_step% hbd2 hm3).stack
        · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
          exact ⟨withExc (withOff g2 cp) (g2.h.len + (18446744073709551600#64 - cp)), y2,
            bd_step% hbd2 hm3, Ok.withBlk hok2 _ _,
            prodQ (r := (.blocked, flat (withExc (withOff g2 cp) (g2.h.len + (18446744073709551600#64 - cp)))))
              (Keep.withBlk _ _)
              (hprod.trans (by rw [hact, tail_block hns hc, Flat.blockDupUnreachable, block_ne hne,
                fin_ne (by simp), flat_withBlk, exc_eq])) rfl rfl⟩
        · simp
    | closed => simp
  case entry t ht =>
    subst ht
    kvcgen64
    simp only [Names.produce, ↓reduceIte]
  case «_ZN12_GLOBAL__N_18Emission7produceE11StackOffset» t ht =>
    simp only [Names.produce, ↓reduceIte] at ht
    subst ht
    clear hspill hpush hdup
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := split8 hfr
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
    vc_by_shape
    | load =>
      first
      | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
      | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
      | with_reducible exact q1 | with_reducible exact q2 | with_reducible exact q3
      | with_reducible exact q4
    | closed => decide
    | other =>
      refine Bd.call (Bd.entry hm6 hTn' hS rfl hr rfl rfl rfl rfl rfl rfl rfl hw) hS hpre.ok trivial ?_
      intro hbd0 t1 g1 y1 hbd1 hQ hok1
      obtain ⟨hg, hax⟩ := copyQ_of hQ (by exact hbd0.bp)
      subst hg
      clear hcopy
      rw [hcp] at hax
      have hm1k := hbd1.mem_k cp
      have hbx1 := hbd1.bx
      have hst := hbd1.rd_st
      have h13 := hbd1.r13
      kvcgen64 [not_reg_spec]
      all_goals try symexec_norm
      all_goals try simp only [hax, hbx1, hst, rd_len' hm1k] at *
      vc_by_shape
      | load =>
        first
        | with_reducible exact hbd1.isSome_k | with_reducible exact hbd1.isSome_st _
        | with_reducible exact isSome_len' hm1k
      | goto ".LB.Emission.produce.4" =>
        rename_i hl
        rw [sub_beq8, h13, ← junk_iff] at hl
        cfg_goto
        · exact (bd_step% hbd1 hm1k).stack
        · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or, or_true]
          exact ⟨y1, bd_step% hbd1 hm1k, act_junk hl⟩
        · simp
      | goto ".LB.Emission.produce.0" =>
        rename_i hl hn
        rw [sub_beq8, h13, ← junk_iff] at hl
        cfg_goto
        · exact (bd_step% hbd1 hm1k).stack
        · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
          exact ⟨y1, bd_step% hbd1 hm1k, hl, act_tail hl (Or.inl (eq_of_z hn))⟩
        · simp
      | goto ".LB.Emission.produce.5" =>
        rename_i hl hn hb
        rw [sub_beq8, h13, ← junk_iff] at hl
        have hc : cp ≠ Flat.NONE := ne_of_z hn
        cfg_goto
        · exact (bd_step% hbd1 hm1k).stack
        · simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
          exact ⟨y1, bd_step% hbd1 hm1k, copy_lt hcp hc,
            act_dup hl hc ((reach_iff (flat g1) cp).mpr (le_of_be hb))⟩
        · simp
      | closed => simp
      | other =>
        rename_i hl hn hb
        rw [sub_beq8, h13, ← junk_iff] at hl
        simp only [Names.produce, String.reduceEq, ↓reduceIte, or_self, or_false, false_or]
        exact ⟨y1, bd_step% hbd1 hm1k, hl, act_tail hl (Or.inr (Bool.eq_false_iff.mpr
          fun h => not_le_of_be hb ((reach_iff (flat g1) cp).mp h)))⟩

end Bbu.Unit
