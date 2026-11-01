module

public import BbuKraken.Unit.TopInv
import all BbuKraken.Unit.TopInv

@[expose] public section

/-!
# `build_bottom_up`: the position blocks

`.LB.build_bottom_up.8` and the loop `.LB.build_bottom_up.9`: `pos[j] = PP[j]` for `j < n`, then `pend = 0` and
`m_plannedMapping = S + offPD` (`locP`). The loop `.LB.build_bottom_up.11`/`.LB.build_bottom_up.10` counts the `j < n` with
`pos[j] = -1` in `pend`. `pos_copy`: the copy of `PP[0..n)` gives `Pm` (it needs `dest_lt`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Top
set_option experimental.vcgen true

-- The copy of the local `PP` into `pos` is the `pos` of the flat model.
theorem getElem_bindDest (A B : Vector Word MAX_N) {i : Nat} (hi : i < MAX_N) :
    ∀ k, k ≤ MAX_N → (Flat.bindDest A k B)[i] = if i < k then A[i] else B[i]
  | 0, _ => by simp
  | k + 1, hk => by
    rw [Flat.bindDest_succ, put_ofNat _ (by omega), get_ofNat _ (by omega), Vector.getElem_set,
      getElem_bindDest A B hi k (by omega)]
    by_cases h1 : k = i <;> by_cases h2 : i < k <;> simp [h1, h2] <;> omega

theorem getElem_clearPos (X : Vector Word MAX_N) {i : Nat} (hi : i < MAX_N) :
    ∀ k, k ≤ MAX_N → (Flat.clearPos k X)[i] = if i < k then Flat.NONE else X[i]
  | 0, _ => by simp
  | k + 1, hk => by
    rw [Flat.clearPos_succ, put_ofNat _ (by omega), Vector.getElem_set,
      getElem_clearPos X hi k (by omega)]
    by_cases h1 : k = i <;> by_cases h2 : i < k <;> simp [h1, h2] <;> omega


section
variable {d : Vector Word MAX_N} {m n : Nat}

-- `bindPos` writes only below `n`.
theorem getElem_bindPos_ge (hd : ∀ p < m, (Flat.get d (BitVec.ofNat 64 p)).toNat < n)
    (Q : Vector Word MAX_N) {i : Nat} (hi : i < MAX_N) (hni : n ≤ i) :
    ∀ k, k ≤ m → (Flat.bindPos d k Q)[i] = Q[i]
  | 0, _ => rfl
  | k + 1, hk => by
    have := hd k (by omega)
    rw [Flat.bindPos_succ, Flat.put_of_lt _ (by omega), Vector.getElem_set]
    split
    · omega
    · exact getElem_bindPos_ge hd Q hi hni k (by omega)

-- Below `n`, `bindPos` depends only on the values below `n`.
theorem getElem_bindPos_lt (hn : n ≤ MAX_N)
    (hd : ∀ p < m, (Flat.get d (BitVec.ofNat 64 p)).toNat < n) {Q Q' : Vector Word MAX_N}
    (hQ : ∀ j (hj : j < n), Q[j]'(by omega) = Q'[j]'(by omega)) {i : Nat} (hi : i < n) :
    ∀ k, k ≤ m → (Flat.bindPos d k Q)[i]'(by omega) = (Flat.bindPos d k Q')[i]'(by omega)
  | 0, _ => hQ i hi
  | k + 1, hk => by
    have := hd k (by omega)
    rw [Flat.bindPos_succ, Flat.bindPos_succ, Flat.put_of_lt _ (by omega),
      Flat.put_of_lt _ (by omega), Vector.getElem_set, Vector.getElem_set]
    split
    · rfl
    · exact getElem_bindPos_lt hn hd hQ hi k (by omega)

end

-- The copy of the local `PP` into `pos` is the `pos` of the flat model.
theorem pos_copy {s : MachineData} {ra : Int64} (hp : TopPre s) (hg : TopGuard s) :
    Flat.bindDest (locB s ra).pp (nArg s) (hdr0 s ra).pos = Pm s ra := by
  have hn : nArg s ≤ MAX_N := hg.2
  have hd := fun p (hp' : p < mArg s) => dest_lt (k := p) hp hg hp'
  refine Vector.ext fun i hi => ?_
  rw [getElem_bindDest _ _ hi _ hn]
  simp only [locB, Pm, Pn]
  split
  · exact getElem_bindPos_lt hn hd (fun j hj => by
      simp only [getElem_clearPos _ _ _ hn, hj, ↓reduceIte]) ‹_› _ (Nat.le_refl _)
  · rw [getElem_bindPos_ge hd _ hi (by omega) _ (Nat.le_refl _), getElem_clearPos _ hi _ hn]; simp only [‹¬_›, ↓reduceIte]


theorem Em.st_pend0 {S : Addr} {h : Hdr} {R : MProp 64} {m : Mem 64} (hm : (Em S h ∗ R).get m) :
    (Em S { h with pend := 0#64 } ∗ R).get (m.storeInt (S + 16440#64) 8 0) := by
  have := Em.st_pend hm 0#64; rwa [BitVec.toInt_zero] at this

theorem b_8 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.8" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hs, hsi⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    rename_i hz
    rw [hsi] at hz
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨zero_of_test hz, hs.step hs.mem rfl rfl rfl rfl rfl rfl rfl⟩
    · top_dec
  case vc2 =>
    rename_i hz
    rw [hsi] at hz
    simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
    refine ⟨0, pos_of_test hz, hs.step hs.mem rfl rfl rfl rfl rfl rfl rfl, rfl, ?_, ?_, ?_⟩
    · rw [hsi]; simp only [nArg, rsi, Reg64s.get64_rsi]; bv_omega
    · rw [hs.sp]
    · rw [hs.sp]
  case vc3 =>
    top_dec


theorem b_9 [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.9" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨j, hj, hs, hax, hdx, hdi, hsi⟩ := ht
  have hnN : nArg s ≤ MAX_N := hs.g.2
  have hjN : j < MAX_N := by omega
  have hax0 : t.regs.rax.toBitVec = 0#64 + BitVec.ofNat 64 (8 * j) := by rw [hax, BitVec.zero_add]
  have hdx0 : t.regs.rdx.toBitVec = 0#64 + BitVec.ofNat 64 (8 * nArg s) := by
    rw [hdx, BitVec.zero_add]
  have hpa : t.regs.rsi.toBitVec + t.regs.rax.toBitVec
      = topS s + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * j) := by rw [hsi, hax]
  have hqa : t.regs.rdi.toBitVec + t.regs.rax.toBitVec = Fld.mapping_positionOf (topS s) j := by
    rw [hdi, hax]; rfl
  have hrd : rd t.dmem (t.regs.rsi.toBitVec + t.regs.rax.toBitVec) = (locB s ra).pp[j] := by
    rw [hpa]; exact Lc.rd_pp hs.mem hjN
  unfold rd at hrd
  have hm' := Em.st_pos hs.mem hjN (locB s ra).pp[j]
  rw [← hqa] at hm'
  have hpos : (Flat.bindDest (locB s ra).pp j (hdr0 s ra).pos).set j (locB s ra).pp[j]
      = Flat.bindDest (locB s ra).pp (j + 1) (hdr0 s ra).pos := by
    rw [Flat.bindDest_succ, put_ofNat _ hjN, get_ofNat _ hjN]
  kvcgen64
  all_goals try symexec_norm
  case vc1 => rw [hpa]; exact Lc.isSome_pp hs.mem hjN
  case vc2 => rw [hqa]; exact Em.isSome_pos hs.mem hjN
  case vc3 =>
    rename_i hc
    have hj1 := succ_lt_of_je (by simpa only [Bool.not_eq_true'] using hc) hax0 hdx0 hj
    rw [hrd]
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      refine ⟨j + 1, hj1, TS.cast (hs.step hm' rfl rfl rfl rfl rfl rfl rfl) (by rw [← hpos]; rfl) rfl,
        ?_, hdx, hdi, hsi⟩
      rw [hax]; simp only [MAX_N] at hjN; bv_omega
    · top_dec
      exact Or.inl (by have := sub8_lt hax0 hdx0 hj1 hnN; omega)
  case vc4 => rw [hrd, hs.sp]; exact Em.isSome_pend hm'
  case vc5 => rw [hrd, hs.sp]; exact Lc.isSome_pm (Em.st_pend0 hm')
  case vc6 =>
    rename_i hc
    have he := succ_eq_of_je (by simpa only [Bool.not_eq_false'] using hc) hax0 hdx0 hj hnN
    have hP : Flat.bindDest (locB s ra).pp (j + 1) (hdr0 s ra).pos = Pm s ra := by
      rw [he]; exact pos_copy hpre hs.g
    have h2 := Lc.st_pm (Em.st_pend0 hm') (topS s + BitVec.ofNat 64 offPD)
    rw [hrd, hs.sp]
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      refine ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ j) (Nat.le_of_eq he), TS.cast (hs.step h2 rfl rfl rfl rfl rfl rfl rfl)
        (by rw [← hP, ← hpos]; rfl) rfl, ?_, ?_⟩
      · rw [hs.sp]; simp
      · exact congrArg (topS s + ·) hdx
    · top_dec


theorem b_10 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.10" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨j, hj, hs, hax, hdx⟩ := ht
  have hnN : nArg s ≤ MAX_N := hs.g.2
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    rename_i hc
    have he := succ_eq_of_je hc hax hdx hj hnN
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨locP s ra, TS.cast (hs.step hs.mem rfl rfl rfl rfl rfl rfl rfl) (by rw [he] <;> rfl) rfl⟩
    · top_dec
  case vc2 =>
    rename_i hc
    have hj1 := succ_lt_of_je hc hax hdx hj
    simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
    exact ⟨j + 1, hj1, hs.step hs.mem rfl rfl rfl rfl rfl rfl rfl, add8 hax, hdx⟩
  case vc3 =>
    rename_i hc
    have hj1 := succ_lt_of_je hc hax hdx hj
    have := sub8_add hax hdx hj1 hnN
    top_dec

theorem b_11 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.11" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨j, hj, hs, hax, hdx⟩ := ht
  have hnN : nArg s ≤ MAX_N := hs.g.2
  have hjN : j < MAX_N := by omega
  have hpa : t.regs.rax.toBitVec + 8248#64 = Fld.mapping_positionOf (topS s) j := by
    rw [hax]; exact posk_addr _ _
  have hrd : rd t.dmem (t.regs.rax.toBitVec + 8248#64) = (Pm s ra)[j] := by
    rw [hpa]; exact Em.rd_pos hs.mem hjN
  unfold rd at hrd
  have hpe : rd t.dmem (topS s + 16440#64) = Flat.countNone (Pm s ra) j 0 := Em.rd_pend hs.mem
  unfold rd at hpe
  kvcgen64
  all_goals try symexec_norm
  case vc1 => rw [hpa]; exact Em.isSome_pos hs.mem hjN
  case vc2 =>
    rename_i hc
    rw [hrd] at hc
    have hne := ne_none_of_jne hc
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨j, hj, TS.cast (hs.step hs.mem rfl rfl rfl rfl rfl rfl rfl)
        (by rw [Flat.countNone_succ, get_ofNat _ hjN, ite_eq_right_of_eq_false _ _ (eq_false hne)] <;> rfl) rfl, hax, hdx⟩
    · top_dec
  case vc3 => rw [hs.sp]; exact Em.isSome_pend hs.mem
  case vc4 =>
    rename_i hc
    rw [hrd] at hc
    have hne := none_of_jne hc
    have hm' := Em.st_pend hs.mem (1#64 + Flat.countNone (Pm s ra) j 0)
    rw [hs.sp, hpe]
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨j, hj, TS.cast (hs.step hm' rfl rfl rfl rfl rfl rfl rfl)
        (by rw [Flat.countNone_succ, get_ofNat _ hjN, ite_eq_left_of_eq_true _ _ (eq_true hne), BitVec.add_comm] <;> rfl) rfl, hax, hdx⟩
    · top_dec

end Top
end Bbu.Unit
