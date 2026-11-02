module

public import FlatShuffler.Fn.IsSpilled
import all FlatShuffler.Fn.IsSpilled
public import FlatShuffler.Kit
import all FlatShuffler.Kit

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace FlatShuffler

/-! ## `shallowestCopyPosition` -/

theorem find?_range_reverse_none {p : Nat → Bool} {n : Nat} (h : ∀ j < n, p j = false) :
    (List.range n).reverse.find? p = none := by
  rw [List.find?_eq_none]
  intro x hx
  simpa using h x (by simpa using hx)

theorem find?_range_reverse_some {p : Nat → Bool} {n i : Nat} (hi : i < n) (hp : p i = true)
    (h : ∀ j, i < j → j < n → p j = false) : (List.range n).reverse.find? p = some i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.find?_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [h n hi (by omega)]
      exact ih hi fun j h1 h2 => h j h1 (by omega)
    · rw [hp]

theorem shallowestCopy_none {m : Mem 64} {S : Addr} {x : StackSlot}
    (h : ∀ j < (rd m (wordAt S 4)).toNat, StackSlot.ofWord (rd m (wordAt (dataOf m S) j)) ≠ x) :
    shallowestCopyPosition (stOf m S) x = none := by
  refine find?_range_reverse_none fun j hj => ?_
  rw [len_stOf] at hj
  simpa [val_stOf hj] using h j hj

theorem shallowestCopy_some {m : Mem 64} {S : Addr} {x : StackSlot} {i : Nat}
    (hi : i < (rd m (wordAt S 4)).toNat) (hv : StackSlot.ofWord (rd m (wordAt (dataOf m S) i)) = x)
    (h : ∀ j, i < j → j < (rd m (wordAt S 4)).toNat →
      StackSlot.ofWord (rd m (wordAt (dataOf m S) j)) ≠ x) :
    shallowestCopyPosition (stOf m S) x = some i := by
  refine find?_range_reverse_some (by rwa [len_stOf]) (by simp [val_stOf hi, hv])
    fun j h1 h2 => ?_
  rw [len_stOf] at h2
  simpa [val_stOf h2] using h j h1 h2

-- `xorq` then `salq $16` sets `nz` when the two words hold different slots.
theorem nz_xor_shl (a b : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result ((a ^^^ b).shiftLeft (((16#64).take 8).toNat &&& 63)) r)
      = !(StackSlot.ofWord a == StackSlot.ofWord b) := by
  rw [shiftLeft_imm, CondCode.interp_nz, StatusFlags.zf_from_result, Bool.eq_iff_iff]
  simp [ofWord_eq_iff]

-- Word `k < n` of the working stack is mapped.
theorem Wf.data_isSome {m : Mem 64} {S : Addr} (hw : Wf m S) {k : Nat} (hk : k < nOf m S) :
    (m.loadInt (wordAt (dataOf m S) k) 8).isSome = true := by
  have := hw.data_lt
  refine hw.mapped.loadInt_isSome (inside_append.mpr (Or.inl (inside_writable ?_)))
  right; right; left
  simp only [wordAt]
  bv_omega

-- The state at `.LB.Emission.shallowestCopyPosition.0` after the slots from `i` up that do not hold `rsi`.
def CopyLoop (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  Keep s ra t ∧ rdi t = rdi s ∧ rsi t = rsi s
    ∧ ∃ i, rax t = BitVec.ofNat 64 i ∧ i ≤ (rd (s.pushRa ra).dmem (wordAt (rdi s) 4)).toNat
      ∧ ∀ j, i ≤ j → j < (rd (s.pushRa ra).dmem (wordAt (rdi s) 4)).toNat
        → StackSlot.ofWord (rd (s.pushRa ra).dmem (wordAt (dataOf (s.pushRa ra).dmem (rdi s)) j))
          ≠ slot s

theorem shallowestCopy_body [Host] [FunDecls] :
    Body shallowestCopyAsm shallowestCopyF shallowestCopyA shallowestCopyR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨hw, -, hst, -⟩ := pushRa_keeps (ra := ra) hpre
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.shallowestCopyPosition then t = s.pushRa ra
        else if l = ".LB.Emission.shallowestCopyPosition.0" then CopyLoop s ra t
        else if l = ".LB.Emission.shallowestCopyPosition.1" then Keep s ra t ∧ shallowestCopyPosition (st s) (slot s) = none
        else if l = ".LB.Emission.shallowestCopyPosition.2" then Done s ra (encOpt (shallowestCopyPosition (st s) (slot s))) t
        else False
      | .exit, _ => False)
    (fun l t => if l = ".LB.Emission.shallowestCopyPosition.0" then (rax t).toNat + 1 else if l = Names.shallowestCopyPosition then 2 ^ 64 + 1 else 0)
    ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht; kvcgen64
    all_goals simp only [Names.shallowestCopyPosition, ↓reduceIte]
  case right.left t ht =>
    simp only [Names.shallowestCopyPosition, ↓reduceIte] at ht
    subst ht
    kvcgen64
    case vc1 => exact hw.word_isSome hw.mapped (k := 4) (by decide)
    case vc2 =>
      refine ⟨Keep.init.next rfl rfl rfl rfl rfl rfl rfl rfl, rfl, rfl,
        (rd (s.pushRa ra).dmem (wordAt (rdi s) 4)).toNat, ?_, Nat.le_refl _, fun j h1 h2 => ?_⟩
      · exact BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
      · exact absurd h2 (Nat.not_lt.mpr h1)
    case vc3 =>
      left
      simp only [Names.shallowestCopyPosition, ↓reduceIte, String.reduceEq]
      exact Nat.add_lt_add_right (BitVec.isLt _) 1
  case right.right.left t ht =>
    simp only [Names.shallowestCopyPosition, ↓reduceIte, String.reduceEq] at ht
    obtain ⟨hk, hdi, hsi, i, hax, hi, hb⟩ := ht
    dsimp only [rdi, rsi, rax] at hdi hsi hax
    have hdata : rd t.dmem (t.regs.get64 .rdi + BitVec.ofInt 64 (Int64.toInt 24))
        = dataOf (s.pushRa ra).dmem (rdi s) := by
      rw [hk.mem, hdi, disp _ 3 24]; rfl
    have haddr : i ≠ 0 → rd t.dmem (t.regs.get64 .rdi + BitVec.ofInt 64 (Int64.toInt 24))
        + (t.regs.get64 .rax - 1#64) * 8#64 + BitVec.ofInt 64 (Int64.toInt 0)
        = wordAt (dataOf (s.pushRa ra).dmem (rdi s)) (i - 1) := fun h0 => by
      have h : BitVec.ofInt 64 (Int64.toInt 0) = 0#64 := by decide
      rw [hdata, hax, h]
      simp only [wordAt]
      bv_omega
    have hz0 : (t.regs.get64 .rax == 0#64) = (i == 0) := by
      rw [hax]
      cases h : i == 0
      · have : i ≠ 0 := by simpa using h
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro hc
        have := congrArg BitVec.toNat hc
        simp only [BitVec.toNat_ofNat] at this
        omega
      · rw [beq_iff_eq.mp h]; rfl
    kvcgen64
    case vc1 _ hz =>
      have h0 : i = 0 := beq_iff_eq.mp (hz0 ▸ (Kit.z_test _ _).symm.trans hz)
      subst h0
      cfg_goto
      · exact stack_pushRa hk.sp
      · refine ⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
        rw [← hst]
        exact shallowestCopy_none fun j hj => hb j (Nat.zero_le j) hj
      · simp [Names.shallowestCopyPosition]
    case vc2 =>
      show (Mem.loadInt t.dmem (t.regs.get64 .rdi + BitVec.ofInt 64 (Int64.toInt 24)) 8).isSome = true
      rw [hk.mem, hdi, disp _ 3 24]
      exact hw.word_isSome hw.mapped (by simp only [WORDS_eq]; omega)
    case vc3 _ hz =>
      have h0 : i ≠ 0 := by simpa using hz0.symm.trans ((Kit.z_test _ _).symm.trans hz)
      show (Mem.loadInt t.dmem (rd t.dmem (t.regs.get64 .rdi + BitVec.ofInt 64 (Int64.toInt 24))
        + (t.regs.get64 .rax - 1#64) * 8#64 + BitVec.ofInt 64 (Int64.toInt 0)) 8).isSome = true
      rw [haddr h0, hk.mem]
      exact hw.data_isSome (Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hi hw.len_le))
    case vc4 => decide
    case vc5 hz _ _ _ _ hnz =>
      have h0 : i ≠ 0 := by simpa using hz0.symm.trans ((Kit.z_test _ _).symm.trans hz)
      have hne : StackSlot.ofWord (rd (s.pushRa ra).dmem (wordAt (dataOf (s.pushRa ra).dmem (rdi s)) (i - 1)))
          ≠ slot s := by
        have h := (nz_xor_shl _ _ _).symm.trans hnz
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at h
        intro hc
        apply h
        show StackSlot.ofWord (t.regs.get64 .rsi) = StackSlot.ofWord (rd t.dmem (rd t.dmem
          (t.regs.get64 .rdi + BitVec.ofInt 64 (Int64.toInt 24)) + (t.regs.get64 .rax - 1#64) * 8#64
            + BitVec.ofInt 64 (Int64.toInt 0)))
        rw [haddr h0, hk.mem, hsi, hc]
      have hax' : t.regs.get64 .rax - 1#64 = BitVec.ofNat 64 (i - 1) := by
        rw [hax]; bv_omega
      cfg_goto
      · exact stack_pushRa hk.sp
      · refine ⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hdi, hsi, i - 1, hax',
          Nat.le_trans (Nat.sub_le i 1) hi, fun j h1 h2 => ?_⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact hne
        · exact hb j (by omega) h2
      · left
        have e1 : (t.regs.get64 .rax - 1#64).toNat = i - 1 := by
          rw [hax']; simp only [BitVec.toNat_ofNat]; omega
        have e2 : (t.regs.get64 .rax).toNat = i := by
          rw [hax]; simp only [BitVec.toNat_ofNat]; omega
        simp only [↓reduceIte]
        have : i - 1 < i := by omega
        exact Nat.add_lt_add_right (Nat.lt_of_le_of_lt (Nat.le_of_eq e1) (Nat.lt_of_lt_of_eq this e2.symm)) 1
    case vc6 =>
      exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
    case vc7 hz _ _ _ _ hnz =>
      have h0 : i ≠ 0 := by simpa using hz0.symm.trans ((Kit.z_test _ _).symm.trans hz)
      have heq : StackSlot.ofWord (rd (s.pushRa ra).dmem (wordAt (dataOf (s.pushRa ra).dmem (rdi s)) (i - 1)))
          = slot s := by
        have h := (nz_xor_shl _ _ _).symm.trans hnz
        simp only [Bool.not_eq_false', beq_iff_eq] at h
        have h' : StackSlot.ofWord (t.regs.get64 .rsi) = StackSlot.ofWord (rd t.dmem (rd t.dmem
          (t.regs.get64 .rdi + BitVec.ofInt 64 (Int64.toInt 24)) + (t.regs.get64 .rax - 1#64) * 8#64
            + BitVec.ofInt 64 (Int64.toInt 0))) := h
        rw [haddr h0, hk.mem, hsi] at h'
        exact h'.symm
      refine Done.ret (R := shallowestCopyR) hpre
        (Keep.done (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) ?_)
        fun t' hm hax => ⟨hax, by rw [st', hm]; exact hst⟩
      show _ = encOpt (shallowestCopyPosition (stOf s.dmem (rdi s)) (slot s))
      rw [← hst, shallowestCopy_some (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos) hi)
        heq fun j h1 h2 => hb j (by omega) h2]
      exact (show t.regs.get64 .rax - 1#64 = BitVec.ofNat 64 (i - 1) by rw [hax]; bv_omega)
  case right.right.right.left t ht =>
    simp only [Names.shallowestCopyPosition, ↓reduceIte, String.reduceEq] at ht
    kvcgen64
    · refine Keep.done (ht.1.next rfl rfl rfl rfl rfl rfl rfl rfl) ?_
      rw [ht.2]; rfl
    · simp [Names.shallowestCopyPosition]
  case right.right.right.right t ht =>
    simp only [Names.shallowestCopyPosition, ↓reduceIte, String.reduceEq] at ht
    kvcgen64
    · simp [ht.retAddr]
    · exact Done.ret (R := shallowestCopyR) hpre ht fun t' hm hax => ⟨hax, by rw [st', hm]; exact hst⟩
end FlatShuffler
