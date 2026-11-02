module

public import FlatShuffler.Unit.Loop.Step
import all FlatShuffler.Unit.Loop.Step

@[expose] public section

set_option experimental.vcgen true

/-!
# `buildBottomUp`: the generations (part P4)

The blocks `.6` (the end of `urgentToDup`), `.7` (the test for the generation at the
top), `.14` (`generate(u)`), `.15` (`generate(size)`) and `.16` (`generate(T)`, then
`placeTop`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Loop

theorem setWidth_replaceLow8 (x : Word) (v : BitVec 8) : BitVec.setWidth 8 (x.replaceLow v) = v := by
  conv => rhs; rw [← BitVec.take_replaceLow_8 x v]
  ext i hi
  simp [BitVec.take]

-- `sete %al` after `cmpq $-1`: `al = (u = NONE)`.
theorem al_sete (x u : Word) :
    BitVec.setWidth 8
        (x.replaceLow (BitVec.ofNat 8 (u - 18446744073709551615#64 == BitVec.zero 64).toNat))
      = if u = Flat.NONE then 1#8 else 0#8 := by
  rw [setWidth_replaceLow8, BitVec.zero_eq, Idioms.sub_beq_zero]
  by_cases h : u = Flat.NONE
  · subst h; rfl
  · rw [ite_eq_right h, beq_eq_false_iff_ne.mpr (fun e => h (e.trans (by decide)))]; rfl

-- `testb %al, %al` with `al = (u = NONE)`.
theorem al_test {x u : Word} (hal : BitVec.setWidth 8 x = if u = Flat.NONE then 1#8 else 0#8) :
    (BitVec.extractLsb' 0 8 x &&& BitVec.extractLsb' 0 8 x == BitVec.zero 8)
      = !decide (u = Flat.NONE) := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide), hal]
  by_cases h : u = Flat.NONE <;> simp [h]

-- `testb %al, %al` after a call with `al = code st`.
theorem test_code {x : Word} {st : Flat.Status} (hal : BitVec.setWidth 8 x = code st) :
    (BitVec.extractLsb' 0 8 x &&& BitVec.extractLsb' 0 8 x == BitVec.zero 8)
      = decide (st = .done) := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide), hal, BitVec.and_self]
  cases st <;> decide

theorem get_lt {α : Type} [Inhabited α] (v : Vector α maxStackSize) {i : Word} (hi : i.toNat < maxStackSize) :
    Flat.get v i = v[i.toNat] := by
  simp [Flat.get, hi]

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

-- `8248(%r12,%x,8)`: `pos[x]`.
theorem rd_pos' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < maxStackSize) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 8248#64) 8).get! = g.h.pos[x.toNat] := by
  rw [Fld.fold_mapping_positionOf]; exact View.rd_pos h hx

theorem isSome_pos' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < maxStackSize) :
    (m.loadInt (S + x * 8#64 + 8248#64) 8).isSome = true := by
  rw [Fld.fold_mapping_positionOf]; exact View.isSome_pos h hx

-- `32(%r12)`: `len`.
theorem rd_len' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 32#64) 8).get! = g.h.len := by
  rw [Fld.fold_stack_size]; exact View.rd_len h

theorem isSome_len' (h : (View S g ∗ R).get m) : (m.loadInt (S + 32#64) 8).isSome = true := by
  rw [Fld.fold_stack_size]; exact View.isSome_len h

-- `56(%r12,%rbx)` with `rbx = 8*x`: `dest[x]`.
theorem rd_dest8 (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < maxStackSize) :
    BitVec.ofInt 64 (m.loadInt (S + 8#64 * x + 56#64) 8).get! = g.h.dest[x.toNat] := by
  rw [BitVec.mul_comm, Fld.fold_mapping_destinationOf]
  obtain ⟨R, h'⟩ := View.arr_dest h
  exact (Arr.rd h' (by simpa using hx)).trans (by simp)

theorem isSome_dest8 (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < maxStackSize) :
    (m.loadInt (S + 8#64 * x + 56#64) 8).isSome = true := by
  rw [BitVec.mul_comm, Fld.fold_mapping_destinationOf]; exact View.isSome_dest h hx

end

theorem b_6 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.7" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hHd, hR⟩ := ht
  have hu : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 8#64) 8).get! = u :=
    hM.rd_u
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hu] at *
  vc_by_shape
  | load => exact hM.isSome_u
  | goto ".LB.Emission.buildBottomUp.8" =>
    rename_i hj
    idioms at hj
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hHd, al_sete _ _, ?_⟩
      rw [Flat.kU, ite_eq_right (fun h => h.2.1 hj)] at hR
      exact hR
    · exact Or.inr ⟨rfl, by decide⟩
  | goto ".LB.Emission.buildBottomUp.14" =>
    rename_i _ hne hj
    idioms at hne hj
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hHd,
        fun e => hj (e.trans (by decide)), hne, hR⟩
    · exact Or.inr ⟨rfl, by decide⟩
  | other =>
    first
    | exact Or.inr ⟨rfl, by decide⟩
    | rename_i _ _ hj
      idioms at hj
      simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hHd, al_sete _ _, ?_⟩
      rw [Flat.kU, ite_eq_right (fun h => h.1 (hj.trans (by decide)))] at hR
      exact hR

theorem b_7 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.8" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hHd, hal, hR⟩ := ht
  have hal' := al_test hal
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.buildBottomUp.9" =>
    rename_i _ hj
    idioms at hj
    have e : Flat.kU2 (flat g') t.regs.r14.toBitVec u = Flat.kU3 (flat g') t.regs.r14.toBitVec := by
      rw [Flat.kU2, ite_eq_right]
      intro h
      have h1 : t.regs.r15.toBitVec.toNat < t.regs.r13.toBitVec.toNat := by
        rw [hHd.1, hHd.2.1]; exact BitVec.lt_def.mp h.2.2.1
      have h2 : t.regs.r14.toBitVec.toNat < t.regs.r15.toBitVec.toNat := by
        rw [hHd.2.1]; exact BitVec.lt_def.mp h.2.1
      simp only [h1, h2, decide_true, Bool.and_self, Bool.true_eq_false] at hj
    rw [e] at hR
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hHd, hR⟩
    · exact Or.inl (Nat.add_lt_add_left (by decide : 2101 < 2102) _)
  | goto ".LB.Emission.buildBottomUp.17" =>
    rename_i _ hj _ ha
    idioms at hj
    rw [hal'] at ha
    simp only [Bool.not_not, decide_eq_true_eq] at ha
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hHd, ha, ?_, ?_, hR⟩
      · rw [← hHd.2.1]; exact BitVec.lt_def.mpr hj.1
      · rw [← hHd.2.1, ← hHd.1]; exact BitVec.lt_def.mpr hj.2
    · exact Or.inr ⟨rfl, by decide⟩
  | other =>
    first
    | exact Or.inl (Nat.add_lt_add_left (by decide : 2101 < 2102) _)
    | rename_i _ _ _ ha
      rw [hal'] at ha
      simp only [Bool.not_not, decide_eq_false_iff_not] at ha
      rw [Flat.kU2, ite_eq_right (fun h => ha h.1)] at hR
      simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hHd, hR⟩

theorem b_14 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s)
    (hout : ∀ l ∈ Program.labels loopAsm, label l ≠ label "exit")
    (hgen : Sep.SpecWithExit Names.generate generateA 16 generateQ generateX) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.14" →
      Obl S g F s ra blk := by
  simp only [Names.generate] at hgen
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hHd, hne, hneT, hR⟩ := ht
  have hu : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 8#64) 8).get! = u :=
    hM.rd_u
  kvcgen64 [hgen]
  all_goals try symexec_norm
  all_goals try simp only [hu] at *
  vc_by_shape
  | load => exact hM.isSome_u
  | goto ".LB.Emission.buildBottomUp.9" =>
    rename_i hj
    idioms at hj
    have e : Flat.kU (flat g') t.regs.r14.toBitVec u = Flat.kU3 (flat g') t.regs.r14.toBitVec := by
      rw [Flat.kU, ite_eq_right, Flat.kU2, ite_eq_right (fun h => hne h.1)]
      intro h
      have h3 : t.regs.r15.toBitVec - t.regs.r14.toBitVec < 16#64 := by
        rw [hHd.2.1]; exact h.2.2
      bv_omega
    rw [e] at hR
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hHd, hR⟩
    · exact Or.inl (Nat.add_lt_add_left (by decide : 2101 < 2102) _)
  | other =>
    rename_i hj
    idioms at hj
    simp only [Bool.and_eq_false_iff, Bool.not_eq_false', beq_iff_eq] at hj
    replace hj := hj.imp_left of_decide_eq_true
    have hlt : (flat g').size - t.regs.r14.toBitVec < Flat.maxSwapDepth := by
      show g'.h.len - _ < 16#64
      rw [← hHd.2.1]
      bv_omega
    rw [Flat.kU, ite_eq_left ⟨hne, hneT, hlt⟩] at hR
    refine Mid.callExit (d := 16) (Q := generateQ) (X := generateX) (by decide) (hM.next rfl rfl rfl) ?_ hok
      (generateA_of hok hHd.2.2.2.1 hHd.2.2.2.2) ?_ ?_
    · exact hM.r12
    · intro t2 g'' lo' w' hmid hQ hok' hsv
      obtain ⟨⟨hk2, hfl, hal2⟩, hnormal⟩ := hQ
      have hc := test_code hal2
      have h14 : t2.regs.r14.toBitVec = t.regs.r14.toBitVec := by rw [hsv.r14]
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | other => first
        | (loop_dec; done)
        | (rename_i _ hz
           rw [hc] at hz
           replace hz := of_decide_eq_false (by simpa only [Bool.not_eq_true'] using hz)
           simp only [Flat.kGenAt, ne_eq, hz, not_false_eq_true, ↓reduceIte, Flat.kfin] at hR
           simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
           refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
             ⟨keep_trans hk hk2, ?_, ?_⟩, hnormal⟩
           · rw [hfl, hR]
           · rw [al, rax, Reg64s.get64_rax, ← hR]; exact hal2)
      | closed => loop_dec
      | goto ".LB.Emission.buildBottomUp.16" =>
        rename_i _ hz
        rw [hc] at hz
        replace hz := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hz)
        simp only [Flat.kGenAt, ne_eq, hz, not_true_eq_false, ↓reduceIte, Flat.kfin] at hR
        have hG := Flat.HInv.gen hHd.2.2.2.1 hHd.2.2.1 hHd.2.2.2.2 hz
        rw [← hk2.xo] at hG
        rw [← hfl] at hG hR
        cfg_goto
        · exact (hmid.next rfl rfl rfl).stack
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
            ?_, ?_⟩
          · simpa only [BitVec.sub_add_cancel, h14] using hG.2.2.1
          · simpa only [BitVec.sub_add_cancel, h14] using hR
        · have hp1 := hM.rd_pend
          have hp2 := hmid.rd_pend
          have hpd : g''.h.pend.toNat + 1 = g'.h.pend.toNat := hG.2.2.2
          loop_dec
          simp only [H, h14, hp1, hp2]
          omega

    · intro tx hp harg
      rw [asm_labels] at hout
      apply ProofKit.intercept_exit (ls := codeLabels) (E := E S g F s ra) hout
      apply E_exit harg
      refine hp.imp ?_
      intro g'' hx
      dsimp only [generateX, ExitRes, rsi, Reg64s.get64_rsi] at hx
      obtain ⟨hk2, hfl, hfail⟩ := hx
      have hne : (Flat.generate (flat g') u).1 ≠ .done := by rw [hfail]; decide
      have hR' : Flat.generate (flat g') u = Flat.buildBottomUp (flat g) := by
        simpa only [Flat.kGenAt, ne_eq, hne, not_false_eq_true, ↓reduceIte, Flat.kfin] using hR
      dsimp only [loopX, ExitRes]
      rw [← hR']
      exact ⟨keep_trans hk hk2, hfl, hfail⟩

theorem b_15 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s)
    (hout : ∀ l ∈ Program.labels loopAsm, label l ≠ label "exit")
    (hgen : Sep.SpecWithExit Names.generate generateA 16 generateQ generateX) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.17" →
      Obl S g F s ra blk := by
  simp only [Names.generate] at hgen
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hHd, hN, hTl, hln, hR⟩ := ht
  have hlN : g'.h.len.toNat < maxStackSize := by
    have := hok.n; have := BitVec.lt_def.mp hln; omega
  have hp : BitVec.ofInt 64
      (Mem.loadInt t.dmem (t.regs.r12.toBitVec + t.regs.r15.toBitVec * 8#64 + 8248#64) 8).get!
        = g'.h.pos[g'.h.len.toNat] := by
    rw [hM.r12, hHd.2.1]; exact rd_pos' hM.mem hlN
  have hgp : Flat.get (flat g').pos (flat g').size = g'.h.pos[g'.h.len.toNat] := get_lt _ hlN
  kvcgen64 [hgen]
  all_goals try symexec_norm
  all_goals try simp only [hp] at *
  vc_by_shape
  | load => rw [hM.r12, hHd.2.1]; exact isSome_pos' hM.mem hlN
  | goto ".LB.Emission.buildBottomUp.9" =>
    have e : Flat.kU2 (flat g') t.regs.r14.toBitVec u = Flat.kU3 (flat g') t.regs.r14.toBitVec := by
      rw [Flat.kU2, ite_eq_right]
      intro h
      rw [hgp] at h
      first
      | rename_i hpn
        idioms at hpn
        exact hpn (h.2.2.2.1.trans (by decide))
      | rename_i hja _
        idioms at hja
        have h3 : t.regs.r15.toBitVec - t.regs.r14.toBitVec < 16#64 := by
          rw [hHd.2.1]; exact h.2.2.2.2
        bv_omega
    rw [e] at hR
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hHd, hR⟩
    · exact Or.inl (Nat.add_lt_add_left (by decide : 2101 < 2102) _)
  | other =>
    rename_i hj hpn
    idioms at hpn
    idioms at hj
    simp only [Bool.and_eq_false_iff, Bool.not_eq_false', beq_iff_eq] at hj
    replace hj := hj.imp_left of_decide_eq_true
    have hlt : (flat g').size - t.regs.r14.toBitVec < Flat.maxSwapDepth := by
      show g'.h.len - _ < 16#64
      rw [← hHd.2.1]
      bv_omega
    rw [Flat.kU2, ite_eq_left ⟨hN, hTl, hln, hgp.trans (hpn.trans (by decide)), hlt⟩] at hR
    have e2 : (flat g').size = g'.h.len := rfl
    rw [e2] at hR
    refine Mid.callExit (d := 16) (Q := generateQ) (X := generateX) (by decide) (hM.next rfl rfl rfl) ?_ hok
      (generateA_of hok hHd.2.2.2.1 hHd.2.2.2.2) ?_ ?_
    · exact hM.r12
    · intro t2 g'' lo' w' hmid hQ hok' hsv
      obtain ⟨⟨hk2, hfl, hal2⟩, hnormal⟩ := hQ
      replace hfl : flat g'' = (Flat.generate (flat g') g'.h.len).2 :=
        hfl.trans (congrArg (fun x => (Flat.generate (flat g') x).2) hHd.2.1)
      replace hal2 : al t2 = code (Flat.generate (flat g') g'.h.len).1 :=
        hal2.trans (congrArg (fun x => code (Flat.generate (flat g') x).1) hHd.2.1)
      have hc := test_code hal2
      have h14 : t2.regs.r14.toBitVec = t.regs.r14.toBitVec := by rw [hsv.r14]
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | goto ".LB.Emission.buildBottomUp.15" =>
        rename_i _ hz
        rw [hc] at hz
        replace hz := of_decide_eq_false (by simpa only [Bool.not_eq_true'] using hz)
        simp only [Flat.kGenAt, ne_eq, hz, not_false_eq_true, ↓reduceIte, Flat.kfin] at hR
        cfg_goto
        · exact (hmid.next rfl rfl rfl).stack
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
            ⟨keep_trans hk hk2, ?_, ?_⟩, hnormal⟩
          · rw [hfl, hR]
          · rw [al, rax, Reg64s.get64_rax, ← hR]; exact hal2
        · loop_dec
      | goto ".LB.Emission.buildBottomUp.30" =>
        rename_i _ hz
        rw [hc] at hz
        replace hz := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hz)
        simp only [Flat.kGenAt, ne_eq, hz, not_true_eq_false, ↓reduceIte, Flat.kfin] at hR
        have hG := Flat.HInv.gen hHd.2.2.2.1 hHd.2.2.1 hHd.2.2.2.2 hz
        rw [← hk2.xo] at hG
        rw [← hfl] at hG hR
        cfg_goto
        · exact (hmid.next rfl rfl rfl).stack
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
            ?_, ?_⟩
          · simpa only [BitVec.sub_add_cancel, h14] using hG.2.2.1
          · simpa only [BitVec.sub_add_cancel, h14] using hR
        · have hp1 := hM.rd_pend
          have hp2 := hmid.rd_pend
          have hpd : g''.h.pend.toNat + 1 = g'.h.pend.toNat := hG.2.2.2
          loop_dec
          simp only [H, BitVec.sub_add_cancel, h14, hp1, hp2]
          omega

    · intro tx hp harg
      rw [asm_labels] at hout
      apply ProofKit.intercept_exit (ls := codeLabels) (E := E S g F s ra) hout
      apply E_exit harg
      refine hp.imp ?_
      intro g'' hx
      dsimp only [generateX, ExitRes, rsi, Reg64s.get64_rsi] at hx
      obtain ⟨hk2, hfl, hfail⟩ := hx
      simp only [hHd.2.1] at hfl hfail
      have hne : (Flat.generate (flat g') g'.h.len).1 ≠ .done := by rw [hfail]; decide
      have hR' : Flat.generate (flat g') g'.h.len = Flat.buildBottomUp (flat g) := by
        simpa only [Flat.kGenAt, ne_eq, hne, not_false_eq_true, ↓reduceIte, Flat.kfin] using hR
      dsimp only [loopX, ExitRes]
      rw [← hR']
      exact ⟨keep_trans hk hk2, hfl, hfail⟩

theorem b_16 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s)
    (hout : ∀ l ∈ Program.labels loopAsm, label l ≠ label "exit")
    (hgen : Sep.SpecWithExit Names.generate generateA 16 generateQ generateX) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.18" →
      Obl S g F s ra blk := by
  simp only [Names.generate] at hgen
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hHd, hbx, hR⟩ := ht
  kvcgen64 [hgen]
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    refine Mid.callExit (d := 16) (Q := generateQ) (X := generateX) (by decide) (hM.next rfl rfl rfl) ?_ hok
      (generateA_of hok hHd.2.2.2.1 hHd.2.2.2.2) ?_ ?_
    · exact hM.r12
    · intro t2 g'' lo' w' hmid hQ hok' hsv
      obtain ⟨⟨hk2, hfl, hal2⟩, hnormal⟩ := hQ
      replace hfl : flat g'' = (Flat.generate (flat g') t.regs.r14.toBitVec).2 := hfl
      replace hal2 : al t2 = code (Flat.generate (flat g') t.regs.r14.toBitVec).1 := hal2
      have hc := test_code hal2
      have h14 : t2.regs.r14.toBitVec = t.regs.r14.toBitVec := by rw [hsv.r14]
      have hbx2 : t2.regs.rbx.toBitVec = t.regs.rbx.toBitVec := by rw [hsv.bx]
      have hTN : t.regs.r14.toBitVec.toNat < maxStackSize := by
        have := hok.n; have := BitVec.lt_def.mp hHd.2.2.1; omega
      have hlen : BitVec.ofInt 64 (Mem.loadInt t2.dmem (t2.regs.r12.toBitVec + 32#64) 8).get!
          = g''.h.len := by
        rw [hmid.r12]; exact rd_len' hmid.mem
      have hdst : BitVec.ofInt 64
          (Mem.loadInt t2.dmem (t2.regs.r12.toBitVec + t2.regs.rbx.toBitVec + 56#64) 8).get!
            = g''.h.dest[t.regs.r14.toBitVec.toNat] := by
        rw [hmid.r12, hbx2, hbx]; exact rd_dest8 hmid.mem hTN
      have hp1 := hM.rd_pend
      have hp2 := hmid.rd_pend
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | goto ".LB.Emission.buildBottomUp.15" =>
        rename_i _ hz
        rw [hc] at hz
        replace hz := of_decide_eq_false (by simpa only [Bool.not_eq_true'] using hz)
        simp only [Flat.kGenT, ne_eq, hz, not_false_eq_true, ↓reduceIte, Flat.kfin] at hR
        cfg_goto
        · exact (hmid.next rfl rfl rfl).stack
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
            ⟨keep_trans hk hk2, ?_, ?_⟩, hnormal⟩
          · rw [hfl, hR]
          · rw [al, rax, Reg64s.get64_rax, ← hR]; exact hal2
        · loop_dec
      | load =>
        first
        | (rw [hmid.r12, hbx2, hbx]; with_reducible exact isSome_dest8 hmid.mem hTN)
        | (rw [hmid.r12]; with_reducible exact isSome_len' hmid.mem)
      | goto ".LB.Emission.buildBottomUp.26" =>
        rename_i _ hz hcf
        rw [hc] at hz
        replace hz := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hz)
        rw [hlen] at hcf
        idioms at hcf
        rw [h14] at hcf
        have hnl : ¬ t.regs.r14.toBitVec < (flat g'').size := fun h => hcf (BitVec.lt_def.mp h)
        simp only [Flat.kGenT, ne_eq, hz, not_true_eq_false, ↓reduceIte] at hR
        rw [← hfl] at hR
        simp only [hnl, not_false_eq_true, ↓reduceIte, Flat.kfin] at hR
        cfg_goto
        · exact (hmid.next rfl rfl rfl).stack
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          exact ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩, hR.symm⟩
        · loop_dec
      | goto ".LB.Emission.buildBottomUp.30" =>
        rename_i _ hz hcf hd
        rw [hc] at hz
        replace hz := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hz)
        have hG := Flat.HInv.gen hHd.2.2.2.1 hHd.2.2.1 hHd.2.2.2.2 hz
        rw [← hk2.xo] at hG
        rw [← hfl] at hG
        rw [hlen] at hcf
        rw [hdst] at hd
        idioms at hcf
        rw [h14] at hcf hd
        have hlt : t.regs.r14.toBitVec < (flat g'').size := BitVec.lt_def.mpr hcf
        have hfin : Flat.isFinal (flat g'') t.regs.r14.toBitVec = true := by
          have e : g''.h.dest[t.regs.r14.toBitVec.toNat] = t.regs.r14.toBitVec := by
            replace hd : _ - _ = 0#64 := beq_iff_eq.mp hd
            bv_omega
          simp only [Flat.isFinal, beq_iff_eq]
          exact (get_lt _ hTN).trans e
        simp only [Flat.kGenT, ne_eq, hz, not_true_eq_false, ↓reduceIte] at hR
        rw [← hfl] at hR
        simp only [hlt, hfin, not_true_eq_false, ↓reduceIte, Flat.kfin] at hR
        have hHn := Flat.Bud.next hG.1 hlt hG.2.1
        cfg_goto
        · exact (hmid.next rfl rfl rfl).stack
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
            ?_, ?_⟩
          · simp only [h14]; exact hHn
          · simp only [h14]; exact hR
        · have hpd : g''.h.pend.toNat + 1 = g'.h.pend.toNat := hG.2.2.2
          have h1024 : maxStackSize = 1024 := rfl
          have hT1 : (t.regs.r14.toBitVec + 1#64).toNat = t.regs.r14.toBitVec.toNat + 1 := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
          loop_dec
          simp only [H, h14, hp1, hp2, hT1]
          omega
      | other =>
        rename_i _ hz hcf hd
        rw [hc] at hz
        replace hz := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hz)
        have hG := Flat.HInv.gen hHd.2.2.2.1 hHd.2.2.1 hHd.2.2.2.2 hz
        rw [← hk2.xo] at hG
        rw [← hfl] at hG
        have hpd : g''.h.pend.toNat + 1 = g'.h.pend.toNat := hG.2.2.2
        first
        | (loop_dec
           simp only [H, h14, hp1, hp2]
           omega)
        | (simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
           rw [hlen] at hcf
           rw [hdst] at hd
           idioms at hcf
           rw [h14] at hcf hd
           have hlt : t.regs.r14.toBitVec < (flat g'').size :=
             BitVec.lt_def.mpr hcf
           have hfin : Flat.isFinal (flat g'') t.regs.r14.toBitVec = false := by
             have e : g''.h.dest[t.regs.r14.toBitVec.toNat] ≠ t.regs.r14.toBitVec := by
               intro e; rw [e, BitVec.sub_self] at hd; exact absurd hd (by decide)
             simp only [Flat.isFinal, beq_eq_false_iff_ne]
             exact fun h => e ((get_lt _ hTN).symm.trans h)
           simp only [Flat.kGenT, ne_eq, hz, not_true_eq_false, ↓reduceIte] at hR
           rw [← hfl] at hR
           simp only [hlt, hfin, Bool.false_eq_true, not_true_eq_false, ↓reduceIte,
             Flat.placeTop_eq] at hR
           refine ⟨g'', u, ⟨x0, x2, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
             ?_, ?_, hG.1, ?_, ?_⟩
           · exact hlen
           · simp only [h14]; exact hlt
           · simpa only [h14] using hG.2.1
           · simpa only [h14] using hR)
    · intro tx hp harg
      rw [asm_labels] at hout
      apply ProofKit.intercept_exit (ls := codeLabels) (E := E S g F s ra) hout
      apply E_exit harg
      refine hp.imp ?_
      intro g'' hx
      dsimp only [generateX, ExitRes, rsi, Reg64s.get64_rsi] at hx
      obtain ⟨hk2, hfl, hfail⟩ := hx
      have hne : (Flat.generate (flat g') t.regs.r14.toBitVec).1 ≠ .done := by rw [hfail]; decide
      have hR' : Flat.generate (flat g') t.regs.r14.toBitVec = Flat.buildBottomUp (flat g) := by
        simpa only [Flat.kGenT, ne_eq, hne, not_false_eq_true, ↓reduceIte, Flat.kfin] using hR
      dsimp only [loopX, ExitRes]
      rw [← hR']
      exact ⟨keep_trans hk hk2, hfl, hfail⟩


theorem b_repeat [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.16" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hH, hR⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  cfg_goto
  · exact (hM.next rfl rfl rfl).stack
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ?_, ?_⟩
    · simpa only [BitVec.sub_add_cancel] using hH
    · simpa only [BitVec.sub_add_cancel] using hR
  · loop_dec
    simp only [H, BitVec.sub_add_cancel]
    exact Or.inl (Nat.lt_succ_self _)

end Loop
end FlatShuffler.Unit
