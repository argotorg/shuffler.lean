module

public import BbuKraken.Unit.Loop.Step
import all BbuKraken.Unit.Loop.Step

@[expose] public section

/-!
# `buildBottomUp`: `swapWith` and `placeTop` (part P6)

The blocks `.11` (`swapWith(p)`), `.12` (`placeTop`), `.17` (`swapWith(T)`), `.22`
and `.23` (`blockSwapUnreachable`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Loop

/-! ## Memory facts of this part (private: `Urgent.lean` has the same facts) -/

section
variable {S : Addr} {g : G} {F : MProp 64} {m : Mem 64}

private theorem isSome_blkOff (h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.blocked_offset S) 8).isSome = true :=
  isSome_of_eq g.h.blkOff h (by unfold View Em; ecancel)

private theorem isSome_blkExc (h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.blocked_excess S) 8).isSome = true :=
  isSome_of_eq g.h.blkExc h (by unfold View Em; ecancel)

private theorem rd_dest (h : (View S g ∗ F).get m) {i : Nat} (hi : i < MAX_N) :
    rd m (Fld.mapping_destinationOf S i) = g.h.dest[i] := by
  obtain ⟨R, h'⟩ := View.arr_dest h
  exact (Arr.rd h' (by simpa using hi)).trans (by simp)

end

-- The test of `al` after a call (`testb %al,%al`): zero iff the status is `done`.
private theorem test_code {x : Word} {st : Flat.Status} (hal : BitVec.setWidth 8 x = code st) :
    (BitVec.extractLsb' 0 8 x &&& BitVec.extractLsb' 0 8 x == BitVec.zero 8)
      = decide (st = .done) := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide), hal, BitVec.and_self]
  cases st <;> decide

-- `x - 1`: the kernel unfolds `x + BitVec.ofInt 64 (-1)` into a chain of `Nat.succ`.
private theorem add_ofInt_neg_one (x : BitVec 64) : x + BitVec.ofInt 64 (-1) = x - 1#64 := by
  rw [BitVec.sub_eq_add_neg]; rfl

theorem b_11 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s)
    (hout : ∀ l ∈ Program.labels loopAsm, label l ≠ label "exit")
    (hswap : Sep.SpecWithExit Names.swapWith swapWithA 2 swapWithQ
      (fun g g' s _ => ExitRes (Flat.swapWith · (rsi s)) g g')) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.12" →
      Obl S g F s ra blk := by
  simp only [Names.swapWith] at hswap
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, h15, hbx, hsi, hax, hf, hb, hR⟩ := ht
  have hsz : (flat g').size = g'.h.len := rfl
  kvcgen64 [hswap]
  all_goals try symexec_norm
  all_goals try simp only [add_ofInt_neg_one]
  vc_by_shape
  | goto ".LB.Emission.buildBottomUp.29" =>
    rename_i hc
    idioms at hc
    have hpT : t.regs.rax.toBitVec = t.regs.r14.toBitVec := by bv_omega
    have hT : t.regs.r14.toBitVec < g'.h.len := hpT ▸ hax
    rw [Flat.kBoundSw, ite_eq_left hpT, Flat.kfin] at hR
    cfg_goto
    · exact hM.stack_of rfl
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hpT, hT,
        Flat.Bud.next hf hT hb, hR⟩
    · loop_dec
      refine Or.inr ⟨?_, by decide⟩
      simp only [H]
  | goto ".LB.Emission.buildBottomUp.13" =>
    rename_i hc1 hc2
    idioms at hc1 hc2
    have hne : t.regs.rax.toBitVec ≠ t.regs.r14.toBitVec := by bv_omega
    have hpL : t.regs.rax.toBitVec = (flat g').size - 1 := by rw [hsz]; bv_omega
    rw [Flat.kBoundSw, ite_eq_right hne, ite_eq_right (fun h => h hpL)] at hR
    cfg_goto
    · exact hM.stack_of rfl
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hbx, hf, hb.mono, hR⟩
    · loop_dec
      refine Or.inr ⟨?_, by decide⟩
      simp only [H]
  | goto ".LB.Emission.buildBottomUp.25" =>
    rename_i hc1 hc2 hc3
    idioms at hc1 hc2 hc3
    have hne : t.regs.rax.toBitVec ≠ t.regs.r14.toBitVec := by bv_omega
    have hne2 : t.regs.rax.toBitVec ≠ (flat g').size - 1 := by rw [hsz]; bv_omega
    have hnr : Flat.isSwapReachable (flat g') t.regs.rax.toBitVec = false := by
      simp only [Flat.isSwapReachable, Flat.depthOf, Flat.maxSwapDepth, hsz,
        decide_eq_false_iff_not]
      bv_omega
    simp only [Flat.kBoundSw, hne, hne2, hnr, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, Flat.kfin] at hR
    cfg_goto
    · exact hM.stack_of rfl
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ?_, ?_, hR.symm⟩
      · bv_omega
      · bv_omega
    · loop_dec
  | other =>
    rename_i hc1 hc2 hc3
    idioms at hc1 hc2 hc3
    have hne : t.regs.rax.toBitVec ≠ t.regs.r14.toBitVec := by bv_omega
    have hne2 : t.regs.rax.toBitVec ≠ (flat g').size - 1 := by rw [hsz]; bv_omega
    have hsr : Flat.isSwapReachable (flat g') t.regs.rax.toBitVec = true := by
      simp only [Flat.isSwapReachable, Flat.depthOf, Flat.maxSwapDepth, hsz,
        decide_eq_true_eq]
      simp only [Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq, beq_iff_eq] at hc3
      bv_omega
    simp only [Flat.kBoundSw, hne, hne2, hsr, ne_eq, not_false_eq_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at hR
    refine Mid.callExit (S := S) (g := g') (F := F) (s := s) (ra := ra)
      (x0 := x0) (x2 := x2) (lo := lo) (w := w) (u := u)
      (d := 2) (A := swapWithA) (Q := swapWithQ)
      (X := fun g g' c _ => ExitRes (Flat.swapWith · (rsi c)) g g')
      (by decide) ?_ ?_ hok ?_ ?_ ?_
    · exact hM.next rfl rfl rfl
    · simpa only [rdi, Reg64s.get64_rdi] using hM.r12
    · exact swapWithA_of hok hf hb
    · intro t2 g'' lo' w' hmid hQ hok' hsv
      obtain ⟨hk2, hfl, hal2⟩ := hQ
      replace hfl : flat g'' = (Flat.swapWith (flat g') t.regs.rax.toBitVec).2 :=
        hfl.trans (by rw [← hsi]; rfl)
      replace hal2 : al t2 = code (Flat.swapWith (flat g') t.regs.rax.toBitVec).1 :=
        hal2.trans (by rw [← hsi]; rfl)
      have hc := test_code hal2
      have h14 : t2.regs.r14.toBitVec = t.regs.r14.toBitVec := by rw [hsv.r14]
      have hbx2 : t2.regs.rbx.toBitVec = t.regs.rbx.toBitVec := by rw [hsv.bx]
      kvcgen64
      all_goals try symexec_norm
      all_goals try simp only [add_ofInt_neg_one]
      vc_by_shape
      | goto ".LB.Emission.buildBottomUp.15" =>
        rename_i _ hz
        rw [hc] at hz
        replace hz := of_decide_eq_false (by simpa only [Bool.not_eq_true'] using hz)
        simp only [hz, not_false_eq_true, ↓reduceIte, Flat.kfin] at hR
        cfg_goto
        · exact hmid.stack
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
            keep_trans hk hk2, ?_, ?_⟩
          · rw [hfl, ← hR]
          · rw [al, rax, Reg64s.get64_rax, ← hR]; exact hal2
        · loop_dec
      | other =>
        rename_i _ hz
        rw [hc] at hz
        replace hz := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hz)
        simp only [hz, not_true_eq_false, ↓reduceIte] at hR
        obtain ⟨hf', hb', hp', -⟩ := Flat.Bud.swapWith hf hb hz
        rw [← hfl] at hf' hb' hp' hR
        rw [← hk2.xo] at hb'
        first
          | (simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
             refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
               ?_, hf', ?_, ?_⟩
             · rw [hbx2, h14]; exact hbx
             · rw [h14]; exact hb'
             · rw [h14]; exact hR)
          | (have hpp : g''.h.pend = g'.h.pend := hp'
             refine Or.inr ⟨?_, by decide⟩
             simp only [V, H, Names.buildBottomUp, String.reduceEq, ↓reduceIte, or_self, or_false,
               or_true, h14, hM.rd_pend, hmid.rd_pend, hpp])

    · intro tx hp harg
      rw [asm_labels] at hout
      apply ProofKit.intercept_exit (ls := codeLabels) (E := E S g F s ra) hout
      apply E_exit harg
      refine hp.imp ?_
      intro g'' hx
      dsimp only [ExitRes, rsi, Reg64s.get64_rsi] at hx
      obtain ⟨hk2, hfl, hfail⟩ := hx
      rw [hsi] at hfl hfail
      have hne : (Flat.swapWith (flat g') t.regs.rax.toBitVec).1 ≠ .done := by rw [hfail]; decide
      simp only [hne, not_false_eq_true, ↓reduceIte, Flat.kfin] at hR
      dsimp only [loopX, ExitRes]
      rw [← hR]
      exact ⟨keep_trans hk hk2, hfl, hfail⟩

theorem b_12 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s)
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels loopAsm, label l ≠ label "exit") :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.13" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hbx, hf, hb, hR⟩ := ht
  have hS := hM.r12
  have hlen : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.r12.toBitVec + 32#64) 8).get!
      = g'.h.len := by
    rw [hS, Fld.fold_stack_size]; exact View.rd_len hM.mem
  have hlenS : (Mem.loadInt t.dmem (t.regs.r12.toBitVec + 32#64) 8).isSome = true := by
    rw [hS, Fld.fold_stack_size]; exact View.isSome_len hM.mem
  have hda : t.regs.r12.toBitVec + t.regs.rbx.toBitVec + 56#64
      = Fld.mapping_destinationOf S t.regs.r14.toBitVec.toNat := by
    rw [hS, hbx, ← Fld.fold_mapping_destinationOf]; bv_omega
  have hdst (hT : t.regs.r14.toBitVec.toNat < g'.h.len.toNat) :
      BitVec.ofInt 64
          (Mem.loadInt t.dmem (Fld.mapping_destinationOf S t.regs.r14.toBitVec.toNat) 8).get!
        = Flat.get (flat g').dest t.regs.r14.toBitVec := by
    have h1 := hf.lt_max_of_size (BitVec.lt_def.mpr hT)
    show rd _ _ = _
    rw [rd_dest hM.mem h1]
    simp only [Flat.get, h1, ↓reduceDIte]
    rfl
  have he := ProofKit.external_call_spec "exit" hexit
  kvcgen64 [he]
  all_goals try symexec_norm
  all_goals simp only [hlen, hda] at *
  vc_by_shape
  | load => first
    | with_reducible exact hM.isSome_exit
    | exact hlenS
    | (rename_i hj; idioms at hj
       exact View.isSome_dest hM.mem (hf.lt_max_of_size (BitVec.lt_def.mpr hj)))
  | goto ".LB.Emission.buildBottomUp.27" =>
    rename_i hj; idioms at hj
    have hlt : ¬t.regs.r14.toBitVec < (flat g').size := fun h => hj (BitVec.lt_def.mp h)
    cfg_goto
    · exact hM.stack_of rfl
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ?_⟩
      rw [← hR, Flat.placeTop_eq]
      simp only [hlt, not_false_eq_true, ↓reduceIte, Flat.kfin]
    · loop_dec
  | goto ".LB.Emission.buildBottomUp.19" =>
    rename_i hj hj'; idioms at hj hj'
    rw [hdst hj] at hj'
    have hlt : t.regs.r14.toBitVec < (flat g').size := BitVec.lt_def.mpr hj
    have hnf : ¬Flat.isFinal (flat g') t.regs.r14.toBitVec = true := by
      simpa only [Flat.isFinal, beq_iff_eq] using hj'
    cfg_goto
    · exact hM.stack_of rfl
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, rfl, hlt, hf, hb, ?_⟩
      rw [← hR, Flat.placeTop_eq]
      simp only [hlt, hnf, not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
    · exact Or.inr ⟨rfl, by decide⟩
  | jumpOut =>
    rename_i exitra hj hj'
    idioms at hj hj'
    rw [hdst hj] at hj'
    have hlt : t.regs.r14.toBitVec < (flat g').size := BitVec.lt_def.mpr hj
    have hfin : Flat.isFinal (flat g') t.regs.r14.toBitVec = true := by
      simpa only [Flat.isFinal, beq_iff_eq] using hj'
    have hR' : Flat.buildBottomUp (flat g) = (.assertionFailed, flat g') := by
      rw [← hR, Flat.placeTop_eq]
      simp only [hlt, hfin, not_true_eq_false, ↓reduceIte, Flat.kfin]
    rw [asm_labels] at hout
    apply ProofKit.intercept_exit (ls := codeLabels) (E := E S g F s ra) hout
    apply E_exit rfl
    apply hM.directExitPost hok exitra rfl
    dsimp only [loopX, ExitRes]
    rw [hR']
    exact ⟨hk, rfl, rfl⟩

theorem b_17 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s)
    (hout : ∀ l ∈ Program.labels loopAsm, label l ≠ label "exit")
    (hswap : Sep.SpecWithExit Names.swapWith swapWithA 2 swapWithQ
      (fun g g' s _ => ExitRes (Flat.swapWith · (rsi s)) g g')) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.19" →
      Obl S g F s ra blk := by
  simp only [Names.swapWith] at hswap
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hax, hT, hf, hb, hR⟩ := ht
  have hsz : (flat g').size = g'.h.len := rfl
  have h1024 : t.regs.r14.toBitVec.toNat < 1024 := hf.lt_max_of_size hT
  have hp1 := hM.rd_pend
  kvcgen64 [hswap]
  all_goals try symexec_norm
  all_goals try simp only [add_ofInt_neg_one]
  vc_by_shape
  | goto ".LB.Emission.buildBottomUp.30" =>
    rename_i hc
    idioms at hc
    have hTL : t.regs.r14.toBitVec = (flat g').size - 1 := by rw [hsz]; bv_omega
    rw [Flat.kTail, ite_eq_right (fun h => h hTL), Flat.kfin] at hR
    cfg_goto
    · exact hM.stack_of rfl
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, Flat.Bud.next hf hT hb, hR⟩
    · loop_dec
      simp only [H, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
  | goto ".LB.Emission.buildBottomUp.28" =>
    rename_i hc1 hc2
    idioms at hc1 hc2
    have hTL : t.regs.r14.toBitVec ≠ (flat g').size - 1 := by rw [hsz]; bv_omega
    have hnr : Flat.isSwapReachable (flat g') t.regs.r14.toBitVec = false := by
      simp only [Flat.isSwapReachable, Flat.depthOf, Flat.maxSwapDepth, hsz,
        decide_eq_false_iff_not]
      bv_omega
    simp only [Flat.kTail, hTL, hnr, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, Flat.kfin] at hR
    cfg_goto
    · exact hM.stack_of rfl
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ?_, ?_, hR.symm⟩
      · bv_omega
      · bv_omega
    · loop_dec
  | other =>
    rename_i hc1 hc2
    idioms at hc1 hc2
    have hTL : t.regs.r14.toBitVec ≠ (flat g').size - 1 := by rw [hsz]; bv_omega
    have hsr : Flat.isSwapReachable (flat g') t.regs.r14.toBitVec = true := by
      simp only [Flat.isSwapReachable, Flat.depthOf, Flat.maxSwapDepth, hsz,
        decide_eq_true_eq]
      simp only [Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq, beq_iff_eq] at hc2
      bv_omega
    simp only [Flat.kTail, hTL, hsr, ne_eq, not_false_eq_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at hR
    refine Mid.callExit (S := S) (g := g') (F := F) (s := s) (ra := ra)
      (x0 := x0) (x2 := x2) (lo := lo) (w := w) (u := u)
      (d := 2) (A := swapWithA) (Q := swapWithQ)
      (X := fun g g' c _ => ExitRes (Flat.swapWith · (rsi c)) g g')
      (by decide) ?_ ?_ hok ?_ ?_ ?_
    · exact hM.next rfl rfl rfl
    · simpa only [rdi, Reg64s.get64_rdi] using hM.r12
    · exact swapWithA_of hok hf hb
    · intro t2 g'' lo' w' hmid hQ hok' hsv
      obtain ⟨hk2, hfl, hal2⟩ := hQ
      replace hfl : flat g'' = (Flat.swapWith (flat g') t.regs.r14.toBitVec).2 := hfl
      replace hal2 : al t2 = code (Flat.swapWith (flat g') t.regs.r14.toBitVec).1 := hal2
      have hc := test_code hal2
      have h14 : t2.regs.r14.toBitVec = t.regs.r14.toBitVec := by rw [hsv.r14]
      have hp2 := hmid.rd_pend
      kvcgen64
      all_goals try symexec_norm
      all_goals try simp only [add_ofInt_neg_one]
      vc_by_shape
      | goto ".LB.Emission.buildBottomUp.15" =>
        rename_i _ hz
        rw [hc] at hz
        replace hz := of_decide_eq_false (by simpa only [Bool.not_eq_false'] using hz)
        simp only [hz, not_false_eq_true, ↓reduceIte, Flat.kfin] at hR
        cfg_goto
        · exact hmid.stack_of rfl
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
            keep_trans hk hk2, ?_, ?_⟩
          · rw [hfl, ← hR]
          · rw [al, rax, Reg64s.get64_rax, ← hR]; exact hal2
        · loop_dec
      | goto ".LB.Emission.buildBottomUp.30" =>
        rename_i _ hz
        rw [hc] at hz
        replace hz := of_decide_eq_true (by simpa only [Bool.not_eq_true'] using hz)
        simp only [hz, not_true_eq_false, ↓reduceIte, Flat.kfin] at hR
        obtain ⟨hf', hb', hp', hs'⟩ := Flat.Bud.swapWith (k := 0) hf hb hz
        rw [← hfl] at hf' hb' hp' hs' hR
        rw [← hk2.xo] at hb'
        have hT' : t.regs.r14.toBitVec < (flat g'').size := by rw [hs']; exact hT
        have hpp : g''.h.pend = g'.h.pend := hp'
        cfg_goto
        · exact hmid.stack_of rfl
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
            ?_, ?_⟩
          · rw [h14]; exact Flat.Bud.next hf' hT' hb'
          · rw [h14]; exact hR
        · loop_dec
          simp only [H, BitVec.toNat_add, BitVec.toNat_ofNat, h14, hp1, hp2, hpp]
          omega
    · intro tx hp harg
      rw [asm_labels] at hout
      apply ProofKit.intercept_exit (ls := codeLabels) (E := E S g F s ra) hout
      apply E_exit harg
      refine hp.imp ?_
      intro g'' hx
      dsimp only [ExitRes, rsi, Reg64s.get64_rsi] at hx
      obtain ⟨hk2, hfl, hfail⟩ := hx
      have hne : (Flat.swapWith (flat g') t.regs.r14.toBitVec).1 ≠ .done := by rw [hfail]; decide
      simp only [hne, not_false_eq_true, ↓reduceIte, Flat.kfin] at hR
      dsimp only [loopX, ExitRes]
      rw [← hR]
      exact ⟨keep_trans hk hk2, hfl, hfail⟩

theorem b_22 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.25" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, h15, hgt, hR⟩ := ht
  have hS := hM.r12
  have hm1 := store_blkOff hM.mem t.regs.rax.toBitVec
  have hm2 := store_blkExc hm1 (t.regs.r15.toBitVec - 17#64)
  kvcgen64
  all_goals try symexec_norm
  · rw [hS, Fld.fold_blocked_offset]
    exact isSome_blkOff hM.mem
  · rw [hS, Fld.fold_blocked_offset, Fld.fold_blocked_excess]
    exact isSome_blkExc hm1
  rw [hS, Fld.fold_blocked_offset, Fld.fold_blocked_excess]
  cfg_goto
  · exact Mid.stack (hM.step hm2 rfl rfl)
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    have hex : Flat.depthOf (flat g') t.regs.rax.toBitVec - Flat.maxSwapDepth
        = t.regs.r15.toBitVec - 17#64 := by
      simp only [Flat.depthOf, Flat.maxSwapDepth, flat]; rw [h15]; bv_omega
    have hne : ¬t.regs.r15.toBitVec - 17#64 = 0 := by bv_omega
    refine ⟨_, u, ⟨x0, x2, lo, w, hM.step hm2 rfl rfl, ?_, ?_⟩, ?_⟩
    · exact ⟨hok.len, hok.n, hok.xs, hok.xo, hok.nops, hok.spl⟩
    · exact ⟨hk.tgtp, hk.n, hk.splp, hk.data, hk.ops, hk.xs, hk.xo, hk.tgt, hk.spl⟩
    refine ⟨⟨hk.tgtp, hk.n, hk.splp, hk.data, hk.ops, hk.xs, hk.xo, hk.tgt, hk.spl⟩, ?_, ?_⟩
    · simp only [hR, Flat.blockSwapUnreachable, hex, Flat.block, hne, ↓reduceIte]; rfl
    · simp only [hR, Flat.blockSwapUnreachable, hex, Flat.block, hne, ↓reduceIte]; rfl
  · loop_dec

theorem b_23 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.28" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hax, hgt, hR⟩ := ht
  have hS := hM.r12
  have hm1 := store_blkOff hM.mem t.regs.r14.toBitVec
  have hm2 := store_blkExc hm1 (t.regs.rax.toBitVec - 17#64)
  kvcgen64
  all_goals try symexec_norm
  · rw [hS, Fld.fold_blocked_offset]
    exact isSome_blkOff hM.mem
  · rw [hS, Fld.fold_blocked_offset, Fld.fold_blocked_excess]
    exact isSome_blkExc hm1
  rw [hS, Fld.fold_blocked_offset, Fld.fold_blocked_excess]
  cfg_goto
  · exact Mid.stack (hM.step hm2 rfl rfl)
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    have hex : Flat.depthOf (flat g') t.regs.r14.toBitVec - Flat.maxSwapDepth
        = t.regs.rax.toBitVec - 17#64 := by
      simp only [Flat.depthOf, Flat.maxSwapDepth, flat]; rw [hax]; bv_omega
    have hne : ¬t.regs.rax.toBitVec - 17#64 = 0 := by bv_omega
    refine ⟨_, u, ⟨x0, x2, lo, w, hM.step hm2 rfl rfl, ?_, ?_⟩, ?_⟩
    · exact ⟨hok.len, hok.n, hok.xs, hok.xo, hok.nops, hok.spl⟩
    · exact ⟨hk.tgtp, hk.n, hk.splp, hk.data, hk.ops, hk.xs, hk.xo, hk.tgt, hk.spl⟩
    refine ⟨⟨hk.tgtp, hk.n, hk.splp, hk.data, hk.ops, hk.xs, hk.xo, hk.tgt, hk.spl⟩, ?_, ?_⟩
    · simp only [hR, Flat.blockSwapUnreachable, hex, Flat.block, hne, ↓reduceIte]; rfl
    · simp only [hR, Flat.blockSwapUnreachable, hex, Flat.block, hne, ↓reduceIte]; rfl
  · loop_dec


end Loop
end Bbu.Unit
