module

public import FlatShuffler.Unit.Loop.Step
import all FlatShuffler.Unit.Loop.Step

@[expose] public section

/-!
# `buildBottomUp`: the `urgentToDup` loop (part P3)

The blocks `.5` (one offset: `isSpilled`, `shallowestCopyPosition`, the update of `u` at
`8(%rsp)`), `.4` (the next offset) and `.3` (`blockDupUnreachable`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Loop

/-! ## Memory facts of this part -/

section
variable {S : Addr} {g : G} {F : MProp 64} {m : Mem 64}

theorem isSome_blkOff (h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.blocked_offset S) 8).isSome = true :=
  isSome_of_eq g.h.blkOff h (by unfold View Em; ecancel)

theorem isSome_blkExc (h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.blocked_excess S) 8).isSome = true :=
  isSome_of_eq g.h.blkExc h (by unfold View Em; ecancel)

-- The loads of `.5` at the offset `T`, with `d = r12`.
theorem urg_loads (hm : (View S g ∗ F).get m) {d T : Word} (hd : d = S)
    (hT : T.toNat < g.h.n.toNat) (hn : g.h.n.toNat ≤ maxStackSize) :
    BitVec.ofInt 64 (m.loadInt (d + T * 8#64 + 8248#64) 8).get! = g.h.pos[T.toNat]
    ∧ BitVec.ofInt 64 (m.loadInt d 8).get! = g.h.tgt
    ∧ BitVec.ofInt 64 (m.loadInt (g.h.tgt + T * 8#64) 8).get! = g.tgt[T.toNat]
    ∧ BitVec.ofInt 8 (m.loadInt (g.h.tgt + T * 8#64 + 4#64) 1).get!
      = g.tgt[T.toNat].extractLsb' 32 8
    ∧ BitVec.ofInt 8 (m.loadInt (g.h.tgt + T * 8#64 + 5#64) 1).get!
      = g.tgt[T.toNat].extractLsb' 40 8 := by
  subst hd
  rw [Fld.fold_mapping_positionOf, fold_slot]
  exact ⟨View.rd_pos hm (by omega), rd_of_eq hm (P := View d g) (a := Fld.target d)
    (by unfold View Em; ecancel), View.rd_tgt hm hT, View.rdb_tgt_byte hm hT (j := 4) (by decide),
    View.rdb_tgt_byte hm hT (j := 5) (by decide)⟩

theorem urg_isSome (hm : (View S g ∗ F).get m) {d T : Word} (hd : d = S)
    (hT : T.toNat < g.h.n.toNat) (hn : g.h.n.toNat ≤ maxStackSize) :
    (m.loadInt (d + T * 8#64 + 8248#64) 8).isSome = true
    ∧ (m.loadInt d 8).isSome = true
    ∧ (m.loadInt (g.h.tgt + T * 8#64) 8).isSome = true
    ∧ (m.loadInt (g.h.tgt + T * 8#64 + 4#64) 1).isSome = true
    ∧ (m.loadInt (g.h.tgt + T * 8#64 + 5#64) 1).isSome = true := by
  subst hd
  rw [Fld.fold_mapping_positionOf, fold_slot]
  refine ⟨View.isSome_pos hm (by omega), isSome_of_eq g.h.tgt hm (P := View d g)
    (a := Fld.target d) (by unfold View Em; ecancel), View.isSome_tgt hm hT, ?_, ?_⟩
  · obtain ⟨_, h⟩ := View.b8_tgt hm hT (j := 4) (by decide); exact B8.isSome h
  · obtain ⟨_, h⟩ := View.b8_tgt hm hT (j := 5) (by decide); exact B8.isSome h

end

/-! ## The slot word at the offset -/

-- `movzbl`: the low byte of a byte that is zero-extended.
theorem urg_byte (b : BitVec 8) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 b)).extractLsb' 0 8 = b := by
  bv_decide

-- The two `andq`/`orq` pairs that put bytes 4 and 5 of `w` back into `w`.
theorem urg_pack (w : Word) :
    (w &&& 18446742978492891135#64
        ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (w.extractLsb' 32 8))).shiftLeft 32)
      &&& 18446463698244468735#64
      ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (w.extractLsb' 40 8))).shiftLeft 40 = w := by
  bv_decide

theorem urg_get_pos {g : G} {i : Word} (hi : i.toNat < maxStackSize) :
    Flat.get (flat g).pos i = g.h.pos[i.toNat] := by
  simp [Flat.get, flat, hi]

theorem urg_get_tgt {g : G} (hok : g.Ok) {i : Word} (hi : i.toNat < g.h.n.toNat) :
    Flat.get (flat g).target i = StackSlot.ofWord g.tgt[i.toNat] := by
  simp [Flat.get, flat, vec, Nat.lt_of_lt_of_le hi hok.n, hi]

-- The variable id of a slot of the target is in the target.
theorem urg_spill_mem {g : G} {i : Nat} (hi : i < g.h.n.toNat) :
    ∀ j, spillId (StackSlot.ofWord g.tgt[i]) = some j → j ∈ splIds g.tgt.toList :=
  fun _ h => List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨_, by simp, h⟩)

theorem urg_junk (w : Word) : isJunk (StackSlot.ofWord w) = (w.extractLsb' 32 8 == 1#8) := rfl

/-! ## The tests of `.5`, in the form of the asm -/

-- `cmpq $-1, 8248(%r12,%rbx,8)`.
theorem urg_pos_ne {p : Word} (h : (!p - 18446744073709551615#64 == BitVec.zero 64) = true) :
    p ≠ Flat.NONE := by
  revert h; simp only [Flat.NONE, BitVec.zero_eq]; bv_decide

theorem urg_pos_eq {p : Word} (h : (!p - 18446744073709551615#64 == BitVec.zero 64) = false) :
    p = Flat.NONE := by
  revert h; simp only [Flat.NONE, BitVec.zero_eq]; bv_decide

section
variable (st : Flat.St) {w : Word}

-- `cmpb $1, %dl; je`: a junk slot.
theorem urg_free_junk (h : (w.extractLsb' 32 8 - 1#8 == BitVec.zero 8) = true) :
    (isJunk (StackSlot.ofWord w) || canBeFreelyGenerated (StackSlot.ofWord w)
      || Flat.isSpilled st (StackSlot.ofWord w)) = true := by
  have hj : (w.extractLsb' 32 8 == 1#8) = true := by
    revert h; simp only [BitVec.zero_eq]; bv_decide
  simp only [urg_junk, hj, Bool.true_or]

-- `testb %cl, %cl; je`: a literal.
theorem urg_free_const (h : (w.extractLsb' 40 8 &&& w.extractLsb' 40 8 == BitVec.zero 8) = true) :
    (isJunk (StackSlot.ofWord w) || canBeFreelyGenerated (StackSlot.ofWord w)
      || Flat.isSpilled st (StackSlot.ofWord w)) = true := by
  have hc : w.extractLsb' 40 8 = 0#8 := by
    revert h; simp only [BitVec.zero_eq]; bv_decide
  simp [canBeFreelyGenerated, isLiteralValue, StackSlot.ofWord, hc, Const]

-- `cmpb $2, %dl; je`: a return label.
theorem urg_free_label (h : (w.extractLsb' 32 8 - 2#8 == BitVec.zero 8) = true) :
    (isJunk (StackSlot.ofWord w) || canBeFreelyGenerated (StackSlot.ofWord w)
      || Flat.isSpilled st (StackSlot.ofWord w)) = true := by
  have hl : w.extractLsb' 32 8 = 2#8 := by
    revert h; simp only [BitVec.zero_eq]; bv_decide
  simp [canBeFreelyGenerated, StackSlot.ofWord, hl, FunctionCallReturnLabel]


-- No test of the free slots is true.
theorem urg_not_free (hj : (w.extractLsb' 32 8 - 1#8 == BitVec.zero 8) = false)
    (hc : (w.extractLsb' 40 8 &&& w.extractLsb' 40 8 == BitVec.zero 8) = false)
    (hl : (w.extractLsb' 32 8 - 2#8 == BitVec.zero 8) = false)
    (hs : Flat.isSpilled st (StackSlot.ofWord w) = false) :
    (isJunk (StackSlot.ofWord w) || canBeFreelyGenerated (StackSlot.ofWord w)
      || Flat.isSpilled st (StackSlot.ofWord w)) = false := by
  have hj' : w.extractLsb' 32 8 ≠ 1#8 := by revert hj; simp only [BitVec.zero_eq]; bv_decide
  have hc' : w.extractLsb' 40 8 ≠ 0#8 := by revert hc; simp only [BitVec.zero_eq]; bv_decide
  have hl' : w.extractLsb' 32 8 ≠ 2#8 := by revert hl; simp only [BitVec.zero_eq]; bv_decide
  rw [hs, urg_junk]
  simp [canBeFreelyGenerated, isLiteralValue, StackSlot.ofWord, Const, Junk,
    FunctionCallReturnLabel, hj', hc', hl']
end

-- `testb %al, %al` after `isSpilled`.
theorem urg_spill_true {a : Word} {b : Bool}
    (h : BitVec.setWidth 8 a = if b = true then 1#8 else 0#8)
    (hz : (!a.extractLsb' 0 8 &&& a.extractLsb' 0 8 == BitVec.zero 8) = true) : b = true := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    revert h hz; simp only [BitVec.zero_eq]; bv_decide
  · rfl

theorem urg_spill_false {a : Word} {b : Bool}
    (h : BitVec.setWidth 8 a = if b = true then 1#8 else 0#8)
    (hz : (!a.extractLsb' 0 8 &&& a.extractLsb' 0 8 == BitVec.zero 8) = false) : b = false := by
  cases b
  · rfl
  · simp only [↓reduceIte] at h
    revert h hz; simp only [BitVec.zero_eq]; bv_decide

/-! ## The tests after `shallowestCopyPosition`, in the form of the asm -/

-- `cmpq $-1, %rax; je` after `shallowestCopyPosition`.
theorem urg_cp_none {c : Word} (h : (c - 18446744073709551615#64 == BitVec.zero 64) = true) :
    c = Flat.NONE := by
  revert h; simp only [Flat.NONE, BitVec.zero_eq]; bv_decide

theorem urg_cp_some {c : Word} (h : (c - 18446744073709551615#64 == BitVec.zero 64) = false) :
    c ≠ Flat.NONE := by
  revert h; simp only [Flat.NONE, BitVec.zero_eq]; bv_decide

section
variable {st : Flat.St} {r c : Word} (hr : r = st.size)
include hr

-- `rdx = rcx - 1` is the depth of `c`.
theorem urg_depth : Flat.depthOf st c = r - c + BitVec.ofInt 64 (-1) := by
  subst hr; simp only [Flat.depthOf]
  rw [show BitVec.ofInt 64 (-1) = 18446744073709551615#64 from rfl]; bv_decide

-- `cmpq $15, %rdx; ja`: the jump is taken.
theorem urg_ja_true
    (h : (!((((r - c + BitVec.ofInt 64 (-1) - 15#64).toNat : Int)
        != ((r - c + BitVec.ofInt 64 (-1)).toNat : Int) - 15))
      && !(r - c + BitVec.ofInt 64 (-1) - 15#64 == BitVec.zero 64)) = true) :
    15#64 < r - c - 1#64 ∧ Flat.isDupReachable st c = false := by
  rw [Idioms.cf_sub_imm _ 15 (by decide)] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  have h1 : r - c + BitVec.ofInt 64 (-1) - 15#64 ≠ 0#64 := h.2
  have h0 : BitVec.ofInt 64 (-1) = 18446744073709551615#64 := rfl
  rw [h0] at h1 h
  have hlt : 15#64 < r - c - 1#64 := by bv_omega
  refine ⟨hlt, ?_⟩
  simp only [Flat.isDupReachable, urg_depth hr, h0, Flat.maxDupDepth, decide_eq_false_iff_not]
  bv_omega

-- `cmpq $15, %rdx; ja`: the jump is not taken.
theorem urg_ja_false
    (h : (!((((r - c + BitVec.ofInt 64 (-1) - 15#64).toNat : Int)
        != ((r - c + BitVec.ofInt 64 (-1)).toNat : Int) - 15))
      && !(r - c + BitVec.ofInt 64 (-1) - 15#64 == BitVec.zero 64)) = false) :
    Flat.isDupReachable st c = true := by
  rw [Idioms.cf_sub_imm _ 15 (by decide)] at h
  have h0 : BitVec.ofInt 64 (-1) = 18446744073709551615#64 := rfl
  simp only [Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq, beq_iff_eq] at h
  simp only [Flat.isDupReachable, urg_depth hr, Flat.maxDupDepth, decide_eq_true_eq]
  rw [h0] at h ⊢
  rcases h with h | h
  · bv_omega
  · have : r - c + 18446744073709551615#64 - 15#64 = 0#64 := h
    bv_omega

-- `sete %al; setne %dl; orb %dl, %al; jne`: the jump is taken.
theorem urg_or_true {T u : Word}
    (h : (!(BitVec.ofNat 8 (c - T == BitVec.zero 64).toNat
      ||| BitVec.ofNat 8 (!(r - c + BitVec.ofInt 64 (-1) - 15#64 == BitVec.zero 64)).toNat
        == BitVec.zero 8)) = true) :
    ¬ (Flat.depthOf st c = Flat.maxDupDepth ∧ c ≠ T ∧ u = Flat.NONE) := by
  rintro ⟨hd, hc, -⟩
  rw [urg_depth hr] at hd
  have h1 : (c - T == BitVec.zero 64) = false := by
    simp only [BitVec.zero_eq, beq_eq_false_iff_ne]; intro e; exact hc (by bv_omega)
  have h2 : (r - c + BitVec.ofInt 64 (-1) - 15#64 == BitVec.zero 64) = true := by
    simp only [hd, Flat.maxDupDepth, BitVec.zero_eq, beq_iff_eq]; decide
  simp only [h1, h2] at h
  revert h; decide

-- `sete %al; setne %dl; orb %dl, %al; jne`: the jump is not taken.
theorem urg_or_false {T : Word}
    (h : (!(BitVec.ofNat 8 (c - T == BitVec.zero 64).toNat
      ||| BitVec.ofNat 8 (!(r - c + BitVec.ofInt 64 (-1) - 15#64 == BitVec.zero 64)).toNat
        == BitVec.zero 8)) = false) :
    Flat.depthOf st c = Flat.maxDupDepth ∧ c ≠ T := by
  rw [urg_depth hr]
  have h0 : BitVec.ofInt 64 (-1) = 18446744073709551615#64 := rfl
  cases h1 : (c - T == BitVec.zero 64) <;>
    cases h2 : (r - c + BitVec.ofInt 64 (-1) - 15#64 == BitVec.zero 64) <;>
    simp only [h1, h2] at h <;> try exact absurd h (by decide)
  simp only [BitVec.zero_eq, beq_iff_eq, beq_eq_false_iff_ne] at h1 h2
  rw [h0] at h2 ⊢
  exact ⟨by simp only [Flat.maxDupDepth]; bv_omega, fun e => h1 (by bv_omega)⟩
end

-- `cmpq $-1, 8(%rsp); cmove %rbx, %rax; movq %rax, 8(%rsp)`.
theorem urg_sel {u o : Word} {P Q : Prop} [Decidable P] [Decidable Q] (hP : P) (hQ : Q) :
    (if (u - 18446744073709551615#64 == BitVec.zero 64) = true then o else u)
      = if P ∧ Q ∧ u = Flat.NONE then o else u := by
  have e : (u - 18446744073709551615#64 == BitVec.zero 64) = true ↔ u = Flat.NONE := by
    simp only [Flat.NONE, BitVec.zero_eq, beq_iff_eq]; bv_decide
  by_cases hu : u = Flat.NONE
  · rw [ite_eq_left (e.mpr hu), ite_eq_left ⟨hP, hQ, hu⟩]
  · rw [ite_eq_right (mt e.mp hu), ite_eq_right (fun h => hu h.2.2)]

/-! ## The invariant and the variant at `.4` -/

-- `Hd` after a call: the callee keeps `r13`, `r14` and `r15`.
theorem urg_hd {g' : G} {t P : MachineData} (h : Hd g' t) (h13 : P.regs.r13 = t.regs.r13)
    (h14 : P.regs.r14 = t.regs.r14) (h15 : P.regs.r15 = t.regs.r15) : Hd g' P := by
  unfold Hd; rw [h13, h14, h15]; exact h

-- `.5` to `.4` at the same offset.
theorem urg_dec {S : Addr} {t P : MachineData}
    (hp : rd P.dmem (Fld.pendingGenerations S) = rd t.dmem (Fld.pendingGenerations S))
    (h14 : P.regs.r14 = t.regs.r14) (hbx : P.regs.rbx = t.regs.rbx) :
    V S ".LB.Emission.buildBottomUp.5" P < V S ".LB.Emission.buildBottomUp.6" t := by
  simp only [V, H, Names.buildBottomUp, String.reduceEq, ↓reduceIte, or_self, hp, h14,
    hbx]
  omega

theorem b_5 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s)
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.6" →
      Obl S g F s ra blk := by
  simp only [Names.isSpilled, Names.shallowestCopyPosition] at hspill hcopy
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hHd, hbx, hR⟩ := ht
  obtain ⟨h13, h15, h14, hH, hp⟩ := id hHd
  have hS := hM.r12
  have hn : g'.h.n.toNat ≤ maxStackSize := hok.n
  have hT : t.regs.rbx.toBitVec.toNat < g'.h.n.toNat := hbx
  have hbx' : t.regs.rbx.toBitVec < (flat g').targetSize := hbx
  have hgp : Flat.get (flat g').pos t.regs.rbx.toBitVec = g'.h.pos[t.regs.rbx.toBitVec.toNat] :=
    urg_get_pos (by omega)
  have hgt := urg_get_tgt hok hT
  obtain ⟨l0, l1, l2, l4, l5⟩ := urg_loads hM.mem hS hT hn
  obtain ⟨i0, i1, i2, i4, i5⟩ := urg_isSome hM.mem hS hT hn
  kvcgen64 [hspill]
  all_goals try symexec_norm
  all_goals try simp only [l0, l1] at *
  all_goals try simp only [l2, l4, l5, urg_byte, urg_pack] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact i0
    | with_reducible exact i1
    | with_reducible exact i2
    | with_reducible exact i4
    | with_reducible exact i5
  | closed => decide
  | goto ".LB.Emission.buildBottomUp.5" =>
    have hst : Flat.urgentFrom (flat g') t.regs.r14.toBitVec t.regs.rbx.toBitVec u
        = Flat.urgentFrom (flat g') t.regs.r14.toBitVec (t.regs.rbx.toBitVec + 1) u := by
      first
      | exact Flat.uf_pos hbx' (by rw [hgp]; apply urg_pos_ne; assumption)
      | exact Flat.uf_free hbx' (by rw [hgp]; apply urg_pos_eq; assumption)
          (by rw [hgt]; apply urg_free_junk; assumption)
      | exact Flat.uf_free hbx' (by rw [hgp]; apply urg_pos_eq; assumption)
          (by rw [hgt]; apply urg_free_const; assumption)
      | exact Flat.uf_free hbx' (by rw [hgp]; apply urg_pos_eq; assumption)
          (by rw [hgt]; apply urg_free_label; assumption)
    cfg_goto
    · exact Mid.stack (hM.next rfl rfl rfl)
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ⟨h13, h15, h14, hH, hp⟩,
               hbx, by rw [← hR, hst]; rfl⟩
    · loop_dec
      simp only [H]; omega
  | other =>
    refine Mid.call (by decide) (hM.next rfl rfl rfl) hS hok (urg_spill_mem hT) ?_
    intro t2 g2 lo2 w2 hM2 hQ hok2 hsv
    obtain ⟨rfl, hal⟩ := hQ
    have e13 : t2.regs.r13 = t.regs.r13 := hsv.r13
    have e14 : t2.regs.r14 = t.regs.r14 := hsv.r14
    have e15 : t2.regs.r15 = t.regs.r15 := hsv.r15
    have ebx : t2.regs.rbx = t.regs.rbx := hsv.bx
    have hd2 := urg_hd hHd e13 e14 e15
    kvcgen64 [hcopy]
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.Emission.buildBottomUp.5" =>
      rename_i hz
      have hsp := urg_spill_true hal hz
      have hst : Flat.urgentFrom (flat g2) t.regs.r14.toBitVec t.regs.rbx.toBitVec u
          = Flat.urgentFrom (flat g2) t.regs.r14.toBitVec (t.regs.rbx.toBitVec + 1) u :=
        Flat.uf_free hbx' (by rw [hgp]; apply urg_pos_eq; assumption)
          (by rw [hgt, hsp, Bool.or_true])
      cfg_goto
      · exact Mid.stack (hM2.next rfl rfl rfl)
      · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
        refine ⟨g2, u, ⟨x0, x2, lo2, w2, hM2.next rfl rfl rfl, hok2, hk⟩, hd2, ?_, ?_⟩
        · rw [ebx]; exact hbx
        · rw [e14, ebx, ← hR, hst]; rfl
      · exact Or.inl (urg_dec ((Mid.rd_pend (hM2.next rfl rfl rfl)).trans hM.rd_pend.symm) e14 ebx)
    | other =>
      rename_i hz
      have hns := urg_spill_false hal hz
      refine Mid.call (by decide) (hM2.next rfl rfl rfl) hM2.r12 hok2 trivial ?_
      intro t3 g3 lo3 w3 hM3 hQ3 hok3 hsv3
      obtain ⟨rfl, hax⟩ := hQ3
      have f13 : t3.regs.r13 = t.regs.r13 := hsv3.r13.trans e13
      have f14 : t3.regs.r14 = t.regs.r14 := hsv3.r14.trans e14
      have f15 : t3.regs.r15 = t.regs.r15 := hsv3.r15.trans e15
      have fbx : t3.regs.rbx = t.regs.rbx := hsv3.bx.trans ebx
      have hd3 : Hd g3 t3 := urg_hd hHd f13 f14 f15
      have hr : t3.regs.r15.toBitVec = (flat g3).size := by rw [f15, h15]; rfl
      have ebp : t2.regs.rbp.toBitVec = g3.tgt[t.regs.rbx.toBitVec.toNat] := by rw [hsv.bp]; rfl
      have hcp : Flat.shallowestCopyPosition (flat g3)
          (Flat.get (flat g3).target t.regs.rbx.toBitVec)
          = t3.regs.rax.toBitVec := by
        rw [hgt]
        exact (hax.trans (congrArg
          (fun x => Flat.shallowestCopyPosition (flat g3) (StackSlot.ofWord x)) ebp)).symm
      have hp0 : Flat.get (flat g3).pos t.regs.rbx.toBitVec = Flat.NONE := by
        rw [hgp]; apply urg_pos_eq; assumption
      have hf0 := urg_not_free (flat g3) (by assumption) (by assumption) (by assumption) hns
      rw [← hgt] at hf0
      have hu : BitVec.ofInt 64 (Mem.loadInt t3.dmem (t3.regs.rsp.toBitVec + 8#64) 8).get! = u :=
        hM3.rd_u
      kvcgen64
      all_goals try symexec_norm
      · rename_i hc
        have hst : Flat.urgentFrom (flat g3) t.regs.r14.toBitVec t.regs.rbx.toBitVec u
            = Flat.urgentFrom (flat g3) t.regs.r14.toBitVec (t.regs.rbx.toBitVec + 1) u :=
          Flat.uf_none hbx' hp0 hf0 (by rw [hcp]; exact urg_cp_none hc)
        cfg_goto
        · exact Mid.stack (hM3.next rfl rfl rfl)
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g3, u, ⟨x0, x2, lo3, w3, hM3.next rfl rfl rfl, hok3, hk⟩, hd3, ?_, ?_⟩
          · rw [fbx]; exact hbx
          · rw [f14, fbx, ← hR, hst]; rfl
        · exact Or.inl
            (urg_dec ((Mid.rd_pend (hM3.next rfl rfl rfl)).trans hM.rd_pend.symm) f14 fbx)
      · rename_i hc hja
        obtain ⟨hlt, hun⟩ := urg_ja_true hr hja
        have hb : Flat.urgentFrom (flat g3) t.regs.r14.toBitVec t.regs.rbx.toBitVec u
            = .error (Flat.blockDupUnreachable (flat g3) t3.regs.rax.toBitVec) := by
          rw [Flat.uf_block hbx' hp0 hf0 (by rw [hcp]; exact urg_cp_some hc)
            (by rw [hcp]; exact hun), hcp]
        cfg_goto
        · exact Mid.stack (hM3.next rfl rfl rfl)
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g3, u, ⟨x0, x2, lo3, w3, hM3.next rfl rfl rfl, hok3, hk⟩, ?_, hlt, ?_⟩
          · show t3.regs.r15.toBitVec - t3.regs.rax.toBitVec = _
            rw [f15, h15]
          · rw [← hR, hb]; rfl
        · loop_dec <;> omega
      · rename_i hc hja hb
        rw [f14] at hb
        have hst : Flat.urgentFrom (flat g3) t.regs.r14.toBitVec t.regs.rbx.toBitVec u
            = Flat.urgentFrom (flat g3) t.regs.r14.toBitVec (t.regs.rbx.toBitVec + 1) u := by
          rw [Flat.uf_next hbx' hp0 hf0 (by rw [hcp]; exact urg_cp_some hc)
            (by rw [hcp]; exact urg_ja_false hr hja), hcp, ite_eq_right (urg_or_true hr hb)]
        cfg_goto
        · exact Mid.stack (hM3.next rfl rfl rfl)
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g3, u, ⟨x0, x2, lo3, w3, hM3.next rfl rfl rfl, hok3, hk⟩, hd3, ?_, ?_⟩
          · rw [fbx]; exact hbx
          · rw [f14, fbx, ← hR, hst]; rfl
        · exact Or.inl
            (urg_dec ((Mid.rd_pend (hM3.next rfl rfl rfl)).trans hM.rd_pend.symm) f14 fbx)
      · exact hM3.isSome_u
      · exact hM3.isSome_u
      · rename_i hc hja hb
        rw [f14] at hb
        obtain ⟨hd15, hne⟩ := urg_or_false hr hb
        obtain ⟨u', hu'⟩ : ∃ u',
            u' = if Flat.depthOf (flat g3) t3.regs.rax.toBitVec = Flat.maxDupDepth
            ∧ t3.regs.rax.toBitVec ≠ t.regs.r14.toBitVec ∧ u = Flat.NONE
              then t.regs.rbx.toBitVec else u := ⟨_, rfl⟩
        have hst : Flat.urgentFrom (flat g3) t.regs.r14.toBitVec t.regs.rbx.toBitVec u
            = Flat.urgentFrom (flat g3) t.regs.r14.toBitVec (t.regs.rbx.toBitVec + 1) u' := by
          rw [Flat.uf_next hbx' hp0 hf0 (by rw [hcp]; exact urg_cp_some hc)
            (by rw [hcp]; exact urg_ja_false hr hja), hcp, hu']
        cfg_goto
        · exact Mid.stack (Mid.setU hM3 _ rfl rfl rfl)
        · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
          refine ⟨g3, u', ⟨x0, x2, lo3, w3, Mid.setU hM3 u' ?_ rfl rfl, hok3, hk⟩,
            hd3, ?_, ?_⟩
          · show Mem.storeInt _ _ _ _ = _
            rw [hu, fbx, hu', urg_sel hd15 hne]
          · rw [fbx]; exact hbx
          · rw [f14, fbx, ← hR, hst]; rfl
        · refine Or.inl (urg_dec ?_ ?_ ?_)
          · rw [Mid.rd_pend hM]
            refine Mid.rd_pend (Mid.setU hM3 u' ?_ ?_ ?_)
            · show Mem.storeInt _ _ _ _ = _
              rw [hu, fbx, hu', urg_sel hd15 hne]
            · rfl
            · rfl
          · exact f14
          · exact fbx

theorem b_4 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.5" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hHd, hbx, hR⟩ := ht
  have hn : g'.h.n.toNat ≤ 1024 := hok.n
  have hb : t.regs.rbx.toBitVec.toNat < 1024 := by bv_omega
  obtain ⟨h13, h15, h14, hH, hp⟩ := hHd
  kvcgen64
  all_goals try symexec_norm
  · rename_i hz
    simp only [beq_iff_eq, BitVec.zero_eq] at hz
    have he : ¬ t.regs.rbx.toBitVec + 1#64 < (flat g').targetSize := by
      show ¬ _ < g'.h.n; rw [← h13]; bv_omega
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ⟨h13, h15, h14, hH, hp⟩, ?_⟩
      rw [← hR, Flat.uf_ge he]; rfl
    · loop_dec
      simp only [H]; omega
  · rename_i hz
    simp only [BitVec.zero_eq, beq_eq_false_iff_ne, ne_eq] at hz
    simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    have hlt : 1#64 + t.regs.rbx.toBitVec < g'.h.n := by rw [← h13] at hbx ⊢; bv_omega
    refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ⟨h13, h15, h14, hH, hp⟩, hlt, ?_⟩
    rw [← hR, BitVec.add_comm]
  · have h1 : (1#64 + t.regs.rbx.toBitVec).toNat = t.regs.rbx.toBitVec.toNat + 1 := by bv_omega
    loop_dec
    simp only [H, h1]
    omega

theorem b_3 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.4" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hcx, hgt, hR⟩ := ht
  have hS := hM.r12
  have hm1 := store_blkOff hM.mem t.regs.rax.toBitVec
  have hm2 := store_blkExc hm1 (t.regs.rcx.toBitVec - 16#64)
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
    have hex : Flat.depthOf (flat g') t.regs.rax.toBitVec - Flat.maxDupDepth
        = t.regs.rcx.toBitVec - 16#64 := by
      simp only [Flat.depthOf, Flat.maxDupDepth, flat]; rw [hcx]; bv_omega
    have hne : ¬t.regs.rcx.toBitVec - 16#64 = 0 := by bv_omega
    refine ⟨_, u, ⟨x0, x2, lo, w, hM.step hm2 rfl rfl, ?_, ?_⟩, ?_⟩
    · exact ⟨hok.len, hok.n, hok.xs, hok.xo, hok.nops, hok.spl⟩
    · exact ⟨hk.tgtp, hk.n, hk.splp, hk.data, hk.ops, hk.xs, hk.xo, hk.tgt, hk.spl⟩
    refine ⟨⟨⟨hk.tgtp, hk.n, hk.splp, hk.data, hk.ops, hk.xs, hk.xo, hk.tgt, hk.spl⟩, ?_, ?_⟩, by change 1#8 ≠ 2#8; decide⟩
    · simp only [hR, Flat.blockDupUnreachable, hex, Flat.block, hne, ↓reduceIte]; rfl
    · simp only [hR, Flat.blockDupUnreachable, hex, Flat.block, hne, ↓reduceIte]; rfl
  · loop_dec

end Loop
end FlatShuffler.Unit
