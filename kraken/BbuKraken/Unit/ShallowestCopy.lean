import BbuKraken.Unit.Defs
import BbuKraken.Sep.Stores
import ProofKit.Cfg
import ProofKit.Idioms

/-!
# `shallowestCopyPosition`

`c/bbu/<Names.shallowestCopyPosition>.S`: no frame, no call, no store. It compares the low 6
bytes of `m_stack[i]` and of the slot, for `i` from `size - 1` down, and returns `-1` if no slot
is equal.

It reads only the slots below `m_size`, and `m_size ≤ n` (`G.Ok`), so it needs no precondition.
The callers (`produce`, `permute`, `buildBottomUp`) use `g' = g` and the result in `rax`.

The loop invariant at `.LB6` is `copyBelow (flat g) x rax = shallowestCopyPosition (flat g) x`:
at the entry `rax` is `m_size`, and each turn of the loop is one unfold of `copyBelow`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ShallowestCopy

open Bbu.Sep

/-! ## The loop of the flat model -/

-- The literals are `0#64` and `1#64`, the form of the goals after `symexec_norm`.
theorem copyBelow_zero (st : Flat.St) (x : StackSlot) : Flat.copyBelow st x 0#64 = Flat.NONE := by
  rw [Flat.copyBelow]; exact dite_eq_left rfl

theorem copyBelow_ne (st : Flat.St) (x : StackSlot) {p : Word} (h : p ≠ 0#64) :
    Flat.copyBelow st x p =
      if Flat.get st.data (p - 1#64) = x then p - 1#64 else Flat.copyBelow st x (p - 1#64) := by
  rw [Flat.copyBelow]; exact dite_eq_right h

-- Slot `i < n` of the flat data is word `i` of the ghost stack.
theorem get_flat_data {g : G} (hn : g.h.n.toNat ≤ MAX_N) {i : Word} (hi : i.toNat < g.h.n.toNat) :
    Flat.get (flat g).data i = StackSlot.ofWord g.stk[i.toNat] := by
  simp [Flat.get, flat, vec, Nat.lt_of_lt_of_le hi hn, hi]

-- `subq $1, %rax` with `rax ≠ 0` does not wrap.
theorem pred_toNat {r : Word} (h0 : r ≠ 0#64) : (r - 1#64).toNat + 1 = r.toNat := by
  bv_omega

/-! ## The flags -/

theorem ofWord_eq_iff (a b : Word) :
    StackSlot.ofWord a = StackSlot.ofWord b ↔ a.extractLsb' 0 48 = b.extractLsb' 0 48 := by
  rw [Idioms.extract48_eq_iff]
  simp only [StackSlot.ofWord, StackSlot.mk.injEq]

-- `testq %rax, %rax`: `zf` is `rax = 0`.
theorem and_self_beq (r : Word) : (r &&& r == BitVec.zero 64) = decide (r = 0#64) := by
  rw [BitVec.and_self, BitVec.zero_eq]
  exact Bool.eq_iff_iff.mpr (by simp)

-- `xorq; salq $16`: `zf` is the slot compare.
theorem shl_xor_beq (a b : Word) :
    ((a ^^^ b).shiftLeft 16 == BitVec.zero 64) =
      decide (StackSlot.ofWord a = StackSlot.ofWord b) := by
  rw [BitVec.shiftLeft_eq, BitVec.zero_eq, Idioms.slot_beq]
  exact Bool.eq_iff_iff.mpr (by simp [ofWord_eq_iff])

/-! ## The jumps -/

-- `je .LB10` taken.
theorem zf_true {r : Word} (h : (r &&& r == BitVec.zero 64) = true) : r = 0#64 := by
  rwa [and_self_beq, decide_eq_true_eq] at h

-- `je .LB10` not taken.
theorem zf_false {r : Word} (h : (r &&& r == BitVec.zero 64) = false) : r ≠ 0#64 := by
  rwa [and_self_beq, decide_eq_false_iff_not] at h

-- `jne .LB6` taken: the slots differ.
theorem jne_true {a b : Word} (h : (!((a ^^^ b).shiftLeft 16 == BitVec.zero 64)) = true) :
    StackSlot.ofWord a ≠ StackSlot.ofWord b := by
  rwa [Bool.not_eq_true', shl_xor_beq, decide_eq_false_iff_not] at h

-- `jne .LB6` not taken: the slots are equal.
theorem jne_false {a b : Word} (h : (!((a ^^^ b).shiftLeft 16 == BitVec.zero 64)) = false) :
    StackSlot.ofWord a = StackSlot.ofWord b := by
  rwa [Bool.not_eq_false', shl_xor_beq, decide_eq_true_eq] at h

/-! ## The load of a slot -/

theorem rd_stk {S : Addr} {g : G} {F : MProp 64} {m : Mem 64} (h : (View S g ∗ F).get m) {i : Nat}
    (hi : i < g.h.n.toNat) : rd m (slotAt g.h.data i) = g.stk[i] :=
  let ⟨_, h⟩ := View.arr_stk h; (Arr.rd h (by simpa using hi)).trans (by simp)

end Bbu.Unit.ShallowestCopy

namespace Bbu.Unit

open Bbu.Sep ShallowestCopy

theorem shallowestCopy_unit [Host] [FunDecls] :
    UnitThm shallowestCopyAsm shallowestCopyA 0 shallowestCopyQ := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain rfl : fr = [] := List.eq_nil_of_length_eq_zero hfr
  have hok := hpre.ok
  have hk0 : Kp S g F s ra [] (s.pushRa ra) := Kp.init hm
  have hdi : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label "_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot", t => t = s.pushRa ra
      | .label ".LB6", t => Kp S g F s ra [] t ∧ rdi t = S ∧ rsi t = rsi s
          ∧ (rax t).toNat ≤ g.h.len.toNat
          ∧ Flat.copyBelow (flat g) (StackSlot.ofWord (rsi s)) (rax t)
            = Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord (rsi s))
      | .label ".LB10", t => Kp S g F s ra [] t
          ∧ Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord (rsi s)) = Flat.NONE
      | .label ".LB7", t => Kp S g F s ra [] t
          ∧ rax t = Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord (rsi s))
      | _, _ => False)
    (fun
      | ".LB6", t => (rax t).toNat + 1
      | "_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot", _ => 2 ^ 64 + 1
      | _, _ => 0) ?_ rfl
  cfg_blocks
  case «entry» t ht =>
    subst ht; kvcgen64
  case «_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot» t ht =>
    subst ht
    have hm := hk0.mem
    -- `movq 32(%rdi), %rax` loads `m_size`.
    have hlen : BitVec.ofInt 64 (Mem.loadInt (s.pushRa ra).dmem
        ((s.pushRa ra).regs.rdi.toBitVec + 32#64) 8).get! = g.h.len := by
      rw [hdi, Fld.fold_stack_size]; exact View.rd_len hm
    kvcgen64
    all_goals try symexec_norm
    all_goals try rw [hlen]
    vc_by_shape
    | load => rw [hdi, Fld.fold_stack_size]; view_load
    -- The parts of the invariant of `.LB6` have the kind `other`. No alternative calls `omega`.
    | other =>
      first
      | exact hk0.next rfl rfl rfl rfl rfl rfl rfl rfl
      | exact hdi
      | rfl
      | exact Nat.le_refl _
      | (left; exact Nat.add_lt_add_right (BitVec.isLt _) 1)
  case «.LB6» t ht =>
    obtain ⟨hk, hrdi', hrsi', hrax', hcb'⟩ := ht
    -- The invariant in the register form of the goals.
    have hrdi : t.regs.rdi.toBitVec = S := hrdi'
    have hrsi : t.regs.rsi.toBitVec = s.regs.rsi.toBitVec := hrsi'
    have hrax : t.regs.rax.toBitVec.toNat ≤ g.h.len.toNat := hrax'
    have hcb : Flat.copyBelow (flat g) (StackSlot.ofWord s.regs.rsi.toBitVec) t.regs.rax.toBitVec
        = Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord s.regs.rsi.toBitVec) := hcb'
    clear hrdi' hrsi' hrax' hcb'
    have hm := hk.mem
    -- `movq 24(%rdi), %rdx` loads `m_stack.m_data`.
    have hd : BitVec.ofInt 64 (Mem.loadInt t.dmem (Fld.stack_data S) 8).get! = g.h.data :=
      View.rd_data hm
    -- `(%rdx,%rax,8)` after `subq $1, %rax`: slot `rax - 1`, below `m_size ≤ n`.
    have ha : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rdi.toBitVec + 24#64) 8).get!
        + (t.regs.rax.toBitVec - 1#64) * 8#64
        = slotAt g.h.data (t.regs.rax.toBitVec - 1#64).toNat := by
      rw [hrdi, Fld.fold_stack_data, hd, fold_slot]
    have hi : t.regs.rax.toBitVec ≠ 0#64 → (t.regs.rax.toBitVec - 1#64).toNat < g.h.n.toNat :=
      fun h0 => Nat.lt_of_succ_le
        (Nat.le_trans (Nat.le_trans (Nat.le_of_eq (pred_toNat h0)) hrax) hok.len)
    -- One turn of the loop is one unfold of `copyBelow`.
    have hstep : t.regs.rax.toBitVec ≠ 0#64 →
        Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord s.regs.rsi.toBitVec) =
          if StackSlot.ofWord (BitVec.ofInt 64 (Mem.loadInt t.dmem
              (BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rdi.toBitVec + 24#64) 8).get!
                + (t.regs.rax.toBitVec - 1#64) * 8#64) 8).get!)
              = StackSlot.ofWord s.regs.rsi.toBitVec
          then t.regs.rax.toBitVec - 1#64
          else Flat.copyBelow (flat g) (StackSlot.ofWord s.regs.rsi.toBitVec)
            (t.regs.rax.toBitVec - 1#64) := fun h0 => by
      have hih := hi h0
      have hx : BitVec.ofInt 64 (Mem.loadInt t.dmem
          (slotAt g.h.data (t.regs.rax.toBitVec - 1#64).toNat) 8).get!
          = g.stk[(t.regs.rax.toBitVec - 1#64).toNat] := rd_stk hm hih
      rw [← hcb, copyBelow_ne _ _ h0, get_flat_data hok.n hih, ha, hx]
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB10" =>
      have h0 := zf_true (by with_reducible assumption)
      cfg_goto
      · exact (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · exact ⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, by rw [← hcb, h0, copyBelow_zero]⟩
      · simp
    | load =>
      -- Both loads are after `je .LB10`, so `rax ≠ 0`.
      have hih := hi (zf_false (by with_reducible assumption))
      simp only [hrdi, Fld.fold_stack_data, hd, fold_slot]
      view_load
    -- `salq $16`: the shift count is not 0.
    | closed => decide
    | goto ".LB6" =>
      have h0 := zf_false (by with_reducible assumption)
      have hne := jne_true (by with_reducible assumption)
      rw [hrsi] at hne
      cfg_goto
      · exact (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
      · exact ⟨hk.next rfl rfl rfl rfl rfl rfl rfl rfl, hrdi, hrsi,
          Nat.le_of_succ_le (Nat.le_trans (Nat.le_of_eq (pred_toNat h0)) hrax),
          ((hstep h0).trans (ite_eq_right (Ne.symm hne))).symm⟩
      · left; exact Nat.succ_lt_succ (Nat.lt_of_succ_le (Nat.le_of_eq (pred_toNat h0)))
    | retAddr =>
      exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
    | ret =>
      have h0 := zf_false (by with_reducible assumption)
      have heq := jne_false (by with_reducible assumption)
      rw [hrsi] at heq
      exact Kp.ret (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl hok fun t' _ hax =>
        ⟨rfl, hax.trans ((hstep h0).trans (ite_eq_left heq.symm)).symm⟩
  case «.LB10» t ht =>
    obtain ⟨hk, hn⟩ := ht
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    -- The parts of the invariant of `.LB7`: `movq $-1, %rax` is `NONE`.
    | other =>
      first
      | exact hk.next rfl rfl rfl rfl rfl rfl rfl rfl
      | exact hn.symm
      | simp
  case «.LB7» t ht =>
    obtain ⟨hk, hr⟩ := ht
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | retAddr => exact Option.isSome_iff_exists.mpr ⟨ra, hk.retAddr⟩
    | ret => exact Kp.ret hk rfl hok fun t' _ hax => ⟨rfl, hax.trans hr⟩

end Bbu.Unit
