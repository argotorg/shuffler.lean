import BbuKraken.Fn.IsSpilled
import BbuKraken.Kit

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

/-! ## `positionOf` -/

theorem asm_positionOf_some {m : Mem 64} {S : Addr} {d : Word} {i : Nat}
    (hi : i < (rd m (wordAt S 0)).toNat) (h : rd m (wordAt S (DEST + i)) = d)
    (hb : ∀ j < i, rd m (wordAt S (DEST + j)) ≠ d) : positionOf (stOf m S) d.toNat = some i := by
  simp only [positionOf, stOf]
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨by simpa using hi, by simp [slotOf, h], fun j hj => ?_⟩
  simp only [List.getElem_map, List.getElem_range, slotOf, beq_iff_eq, BitVec.toNat_inj]
  exact hb j hj

theorem asm_positionOf_none {m : Mem 64} {S : Addr} {d : Word}
    (hb : ∀ j < (rd m (wordAt S 0)).toNat, rd m (wordAt S (DEST + j)) ≠ d) :
    positionOf (stOf m S) d.toNat = none := by
  simp only [positionOf, stOf]
  rw [List.findIdx?_eq_none_iff]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp]
  rintro _ j hj rfl
  simpa [slotOf, BitVec.toNat_inj] using hb j hj

-- The state at `.LB7` after `i` slots that are not bound for `rsi`.
def PosLoop (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  Keep s ra t ∧ rdi t = rdi s ∧ rsi t = rsi s
    ∧ rdx t = rd (s.pushRa ra).dmem (wordAt (rdi s) 0)
    ∧ ∃ i, rax t = BitVec.ofNat 64 i ∧ i < (rd (s.pushRa ra).dmem (wordAt (rdi s) 0)).toNat
      ∧ ∀ j < i, rd (s.pushRa ra).dmem (wordAt (rdi s) (DEST + j)) ≠ rsi s

theorem positionOf_body [Host] [FunDecls] : Body positionOfAsm positionOfF positionOfA positionOfR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨hw, -, hst, -⟩ := pushRa_keeps (ra := ra) hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "positionOf", t => t = s.pushRa ra
      | .label ".LB7", t => PosLoop s ra t
      | .label ".LB8", t => Keep s ra t ∧ positionOf (st s) (rsi s).toNat = none
      | .label ".LB5", t => Done s ra (encOpt (positionOf (st s) (rsi s).toNat)) t
      | _, _ => False)
    (fun l t => if l = ".LB7" then 2 ^ 64 - (rax t).toNat else if l = "positionOf" then 2 ^ 64 else 0)
    ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.left t ht =>
    subst ht
    kvcgen64
    case vc1 => exact hw.word_isSome hw.mapped (k := 0) (by decide)
    case vc2 _ hz =>
      have h0 := beq_iff_eq.mp ((Kit.z_test _ _).symm.trans hz)
      cfg_goto
      · exact stack_pushRa rfl
      · refine ⟨Keep.init.next rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
        rw [← hst]
        refine asm_positionOf_none fun j hj => ?_
        have : (rd (s.pushRa ra).dmem (wordAt (rdi s) 0)).toNat = 0 := by
          rw [show rd (s.pushRa ra).dmem (wordAt (rdi s) 0) = 0#64 from h0]; rfl
        exact absurd (Nat.lt_of_lt_of_eq hj this) (Nat.not_lt_zero j)
      · simp
    case vc3 _ hz =>
      have h0 := (beq_eq_false_iff_ne).mp ((Kit.z_test _ _).symm.trans hz)
      refine ⟨Keep.init.next rfl rfl rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl, 0, rfl, ?_, by simp⟩
      have : rd (s.pushRa ra).dmem (wordAt (rdi s) 0) ≠ 0#64 := h0
      have := BitVec.toNat_ne.mp this
      simp only [BitVec.toNat_ofNat] at this
      omega
    case vc4 => simp
  case right.right.left t ht =>
    obtain ⟨hk, hdi, hsi, hdx, i, hax, hi, hb⟩ := ht
    dsimp only [rdi, rsi, rdx, rax] at hdi hsi hdx hax
    have hi64 : i < 1024 := Nat.lt_of_lt_of_le hi hw.len_le
    have haddr : t.regs.get64 .rdi + t.regs.get64 .rax * 8#64 + BitVec.ofInt 64 (Int64.toInt 8256)
        = wordAt (rdi s) (DEST + i) := by
      have h : BitVec.ofInt 64 (Int64.toInt 8256) = 8256#64 := by decide
      rw [hdi, hax, h]
      simp only [DEST_eq, wordAt, rdi]
      bv_omega
    kvcgen64
    case vc1 =>
      rw [hk.mem, haddr]
      exact hw.word_isSome hw.mapped (by simp only [DEST_eq, WORDS_eq]; omega)
    case vc2 hz =>
      have heq : rd t.dmem (t.regs.get64 .rdi + t.regs.get64 .rax * 8#64
          + BitVec.ofInt 64 (Int64.toInt 8256)) = t.regs.get64 .rsi :=
        beq_iff_eq.mp ((Kit.z_sub _ _ _).symm.trans hz)
      rw [hk.mem, haddr, hsi] at heq
      cfg_goto
      · exact stack_pushRa hk.sp
      · refine Keep.done (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) ?_
        rw [← hst, asm_positionOf_some hi heq hb]
        exact hax
      · simp
        have := t.regs.rax.toNat_lt
        omega
    case vc3 hz hnz =>
      have hne : rd (s.pushRa ra).dmem (wordAt (rdi s) (DEST + i)) ≠ rsi s := by
        intro h
        have h' : rd t.dmem (t.regs.get64 .rdi + t.regs.get64 .rax * 8#64
            + BitVec.ofInt 64 (Int64.toInt 8256)) = t.regs.get64 .rsi := by
          rw [hk.mem, haddr, hsi]; exact h
        have := (Kit.z_sub _ _ _).symm.trans hz
        exact (beq_eq_false_iff_ne.mp this) h'
      have hnx : (1#64 + t.regs.get64 .rax == t.regs.get64 .rdx) = false := by
        simpa using (Kit.nz_sub _ _ _).symm.trans hnz
      rw [hax, hdx] at hnx
      have hi1 : i + 1 < (rd (s.pushRa ra).dmem (wordAt (rdi s) 0)).toNat := by
        refine Nat.lt_of_le_of_ne hi fun hc => ?_
        have : 1#64 + BitVec.ofNat 64 i = rd (s.pushRa ra).dmem (wordAt (rdi s) 0) := by
          apply BitVec.eq_of_toNat_eq
          rw [← hc]
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        exact (beq_eq_false_iff_ne.mp hnx) this
      have hti : (t.regs.get64 .rax).toNat = i := by
        rw [hax, BitVec.toNat_ofNat]; omega
      cfg_goto
      · exact stack_pushRa hk.sp
      · refine ⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hdi, hsi, hdx, i + 1, ?_, hi1, fun j hj => ?_⟩
        · show 1#64 + t.regs.get64 .rax = _
          rw [hax]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hb j hj
          · exact hne
      · left
        have h1 : t.regs.rax.toNat = i := hti
        simp
        omega
    case vc4 =>
      exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
    case vc5 hz hnz =>
      have hne : rd (s.pushRa ra).dmem (wordAt (rdi s) (DEST + i)) ≠ rsi s := by
        intro h
        have h' : rd t.dmem (t.regs.get64 .rdi + t.regs.get64 .rax * 8#64
            + BitVec.ofInt 64 (Int64.toInt 8256)) = t.regs.get64 .rsi := by
          rw [hk.mem, haddr, hsi]; exact h
        have := (Kit.z_sub _ _ _).symm.trans hz
        exact (beq_eq_false_iff_ne.mp this) h'
      have hnx : (1#64 + t.regs.get64 .rax == t.regs.get64 .rdx) = true := by
        simpa using (Kit.nz_sub _ _ _).symm.trans hnz
      rw [hax, hdx, beq_iff_eq] at hnx
      have hl : (rd (s.pushRa ra).dmem (wordAt (rdi s) 0)).toNat = i + 1 := by
        rw [← hnx]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      refine Done.ret (R := positionOfR) hpre
        (Keep.done (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) ?_)
        fun t' hm hax => ⟨hax, by rw [st', hm]; exact hst⟩
      show rax _ = encOpt (positionOf (stOf s.dmem (rdi s)) (rsi s).toNat)
      rw [← hst, asm_positionOf_none fun j hj => ?_]
      · rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_of_lt_of_eq hj hl) with hj | rfl
        · exact hb j hj
        · exact hne
  case right.right.right.left t ht =>
    kvcgen64
    · refine Keep.done (ht.1.next rfl rfl rfl rfl rfl rfl rfl rfl) ?_
      rw [ht.2]; rfl
    · simp
  case right.right.right.right t ht =>
    kvcgen64
    · simp [ht.retAddr]
    · exact Done.ret (R := positionOfR) hpre ht fun t' hm hax => ⟨hax, by rw [st', hm]; exact hst⟩

end Bbu
