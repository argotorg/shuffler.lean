module

public import BbuKraken.Unit.Defs
import all BbuKraken.Unit.Defs
public import BbuKraken.Sep.Stores
import all BbuKraken.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.Idioms
import all ProofKit.Idioms
public import BbuKraken.Unit.PermuteModel
import all BbuKraken.Unit.PermuteModel

@[expose] public section

/-!
# `permute`: helper lemmas

Copies of helper lemmas of the unit proofs of `generate` (branch `zc-generate`) and `swapWith`
(branch `kraken-bbu`), in the namespace `Bbu.Unit.Permute`. The copies keep this branch
independent of the other unit branches. Also the stores of `m_blocked`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

/-! ## `notq`

`kvcgen64` has no spec for `notq %r64`. -/

theorem notq_spec [Host] [FunDecls] (asz : Width) (r : Reg64)
    {Q : PUnit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (~~~(s.regs.get64 r)) } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hpre

/-! ## Loads and stores of the struct -/

section
variable {S : Addr} {g : G} {F : MProp 64} {m : Mem 64}

theorem addr_succ (a : Addr) (i : Nat) :
    a + BitVec.ofNat 64 (8 * (i + 1)) = a + 8#64 + BitVec.ofNat 64 (8 * i) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

-- Word `i` of an array, the rest, and the array with word `i` set.
theorem arr_focus_set (a : Addr) (vs : List Word) {i : Nat} (hi : i < vs.length) :
    ∃ R, Arr a vs = Wd (a + BitVec.ofNat 64 (8 * i)) vs[i] ∗ R
      ∧ ∀ w, Arr a (vs.set i w) = Wd (a + BitVec.ofNat 64 (8 * i)) w ∗ R := by
  induction vs generalizing a i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero => exact ⟨Arr (a + 8#64) vs, by simp [Arr], fun w => by simp [Arr]⟩
    | succ i =>
      obtain ⟨R, e, e'⟩ := ih (a + 8#64) (Nat.lt_of_succ_lt_succ hi)
      refine ⟨Wd a v ∗ R, ?_, fun w => ?_⟩
      · rw [Arr, e, addr_succ, List.getElem_cons_succ, ← MProp.sep_assoc,
          MProp.sep_comm (Wd a v), MProp.sep_assoc]
      · rw [List.set_cons_succ, Arr, e' w, addr_succ, ← MProp.sep_assoc,
          MProp.sep_comm (Wd a v), MProp.sep_assoc]

theorem wd_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    ∃ R, (Wd (slotAt g.h.data i) g.stk[i] ∗ R).get m := by
  obtain ⟨R, h⟩ := View.arr_stk h
  obtain ⟨Q, e, -⟩ := arr_focus_set g.h.data g.stk.toList (i := i) (by simpa using hi)
  rw [e, Vector.getElem_toList, MProp.sep_assoc] at h
  exact ⟨_, h⟩

theorem rd_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    rd m (slotAt g.h.data i) = g.stk[i] :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.rd h

theorem B32.rd32 {a : Addr} {v : BitVec 32} (h : (B32 a v ∗ F).get m) :
    BitVec.ofInt 32 (m.loadInt a 4).get! = v := by
  unfold B32 at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.get!_some,
    BitVec.ofInt_ofBytes_toBytes 32 4 rfl]

-- `movl (slot), %r32`: the low 4 bytes.
theorem rd32_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    BitVec.ofInt 32 (m.loadInt (slotAt g.h.data i) 4).get! = g.stk[i].extractLsb' 0 32 := by
  obtain ⟨R, h⟩ := wd_slot h hi
  rw [Wd.split, MProp.sep_assoc] at h
  exact B32.rd32 h

theorem isSome32_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data i) 4).isSome = true := by
  obtain ⟨R, h⟩ := wd_slot h hi
  rw [Wd.split, MProp.sep_assoc] at h
  exact B32.isSome h

-- `movzbl 4(slot)` and `movzbl 5(slot)`.
theorem rdb4_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    rdb m (slotAt g.h.data i + 4#64) = g.stk[i].extractLsb' 32 8 :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.rdb_byte h (j := 4) (by decide)

theorem rdb5_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    rdb m (slotAt g.h.data i + 5#64) = g.stk[i].extractLsb' 40 8 :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.rdb_byte h (j := 5) (by decide)

theorem isSome4_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data i + 4#64) 1).isSome = true :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.isSome_byte h (j := 4) (by decide)

theorem isSome5_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data i + 5#64) 1).isSome = true :=
  let ⟨_, h⟩ := wd_slot h hi; Wd.isSome_byte h (j := 5) (by decide)

theorem rd_dest (h : (View S g ∗ F).get m) {i : Nat} (hi : i < MAX_N) :
    rd m (Fld.mapping_destinationOf S i) = g.h.dest[i] := by
  obtain ⟨R, h'⟩ := View.arr_dest h
  exact (Arr.rd h' (by simpa using hi)).trans (by simp)

theorem rd_stk (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    rd m (slotAt g.h.data i) = g.stk[i] :=
  let ⟨_, h⟩ := View.arr_stk h; (Arr.rd h (by simpa using hi)).trans (by simp)

-- `movl` and two `movb` to slot `i`: the low 6 bytes. Bytes 6 and 7 do not change.
theorem store411_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs)
    (x : BitVec 32) (y z : BitVec 8) :
    (View S { g with stk := g.stk.set i (g.stk[i].extractLsb' 48 16 ++ z ++ y ++ x) } ∗ F).get
      (((m.storeInt (slotAt g.h.data i) 4 x.toInt).storeInt (slotAt g.h.data i + 4#64) 1
        y.toInt).storeInt (slotAt g.h.data i + 5#64) 1 z.toInt) := by
  obtain ⟨R, e, e'⟩ := arr_focus_set g.h.data g.stk.toList (i := i) (by simpa using hi)
  refine swap_of_eq h (A := Arr g.h.data g.stk.toList)
    (A' := Arr g.h.data (g.stk.set i (g.stk[i].extractLsb' 48 16 ++ z ++ y ++ x)).toList)
    (by unfold View; ecancel) (by unfold View; ecancel) fun h => ?_
  rw [e, MProp.sep_assoc, Vector.getElem_toList] at h
  rw [Vector.toList_set, e', MProp.sep_assoc]
  exact Wd.store411 h x y z

-- The bytes `4` and `5` of slot `i` between the stores of `store411_slot`.
theorem isSome4_411 (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) (x : BitVec 32) :
    ((m.storeInt (slotAt g.h.data i) 4 x.toInt).loadInt (slotAt g.h.data i + 4#64) 1).isSome
      = true := by
  obtain ⟨R, h⟩ := wd_slot h hi
  rw [Wd.split] at h
  simp only [MProp.sep_assoc] at h
  have h1 := B32.store h x.toInt
  rw [sep_lc] at h1
  exact B8.isSome h1

theorem isSome5_411 (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) (x : BitVec 32)
    (y : BitVec 8) :
    (((m.storeInt (slotAt g.h.data i) 4 x.toInt).storeInt (slotAt g.h.data i + 4#64) 1
      y.toInt).loadInt (slotAt g.h.data i + 5#64) 1).isSome = true := by
  obtain ⟨R, h⟩ := wd_slot h hi
  rw [Wd.split] at h
  simp only [MProp.sep_assoc] at h
  have h1 := B32.store h x.toInt
  rw [sep_lc] at h1
  have h2 := B8.store h1 y.toInt
  rw [sep_lc (B8 (slotAt g.h.data i + 4#64) _), sep_lc (B8 (slotAt g.h.data i + 4#64) _),
    sep_lc (B32 (slotAt g.h.data i) _)] at h2
  exact B8.isSome h2

-- `m_blocked.offset` and `m_blocked.excess`.
theorem store_blkOff (h : (View S g ∗ F).get m) (w : Word) :
    (View S { g with h := { g.h with blkOff := w } } ∗ F).get
      (m.storeInt (Fld.blocked_offset S) 8 w.toInt) :=
  swap_of_eq h (A := Wd (Fld.blocked_offset S) g.h.blkOff) (by unfold View Em; ecancel)
    (by unfold View Em; ecancel) (Wd.store · w)

theorem store_blkExc (h : (View S g ∗ F).get m) (w : Word) :
    (View S { g with h := { g.h with blkExc := w } } ∗ F).get
      (m.storeInt (Fld.blocked_excess S) 8 w.toInt) :=
  swap_of_eq h (A := Wd (Fld.blocked_excess S) g.h.blkExc) (by unfold View Em; ecancel)
    (by unfold View Em; ecancel) (Wd.store · w)

end

/-! ## The struct at `r15`: the address forms of the asm -/

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

theorem rd_len' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 32#64) 8).get! = g.h.len := by
  rw [Fld.fold_stack_size]; exact View.rd_len h
theorem isSome_len' (h : (View S g ∗ R).get m) : (m.loadInt (S + 32#64) 8).isSome = true := by
  rw [Fld.fold_stack_size]; exact View.isSome_len h
theorem rd_data' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 24#64) 8).get! = g.h.data := by
  rw [Fld.fold_stack_data]; exact View.rd_data h
theorem isSome_data' (h : (View S g ∗ R).get m) : (m.loadInt (S + 24#64) 8).isSome = true := by
  rw [Fld.fold_stack_data]; exact View.isSome_data h

theorem rd_dest' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 56#64) 8).get! = g.h.dest[x.toNat] := by
  rw [Fld.fold_mapping_destinationOf]; exact rd_dest h hx
theorem isSome_dest' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    (m.loadInt (S + x * 8#64 + 56#64) 8).isSome = true := by
  rw [Fld.fold_mapping_destinationOf]; exact View.isSome_dest h hx
theorem isSome_pos' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    (m.loadInt (S + x * 8#64 + 8248#64) 8).isSome = true := by
  rw [Fld.fold_mapping_positionOf]; exact View.isSome_pos h hx

theorem rd_slot' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < g.h.n.toNat + g.xs) :
    BitVec.ofInt 64 (m.loadInt (g.h.data + x * 8#64) 8).get! = g.stk[x.toNat] := by
  rw [fold_slot]; exact rd_stk h hx
theorem isSome_slot' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < g.h.n.toNat + g.xs) :
    (m.loadInt (g.h.data + x * 8#64) 8).isSome = true := by
  rw [fold_slot]; exact View.isSome_slot h hx

theorem store_dest' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) (v : Word) :
    (View S { g with h := { g.h with dest := g.h.dest.set x.toNat v } } ∗ R).get
      (m.storeInt (S + x * 8#64 + 56#64) 8 v.toInt) := by
  rw [Fld.fold_mapping_destinationOf]; exact View.store_dest h hx v
theorem store_pos' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) (v : Word) :
    (View S { g with h := { g.h with pos := g.h.pos.set x.toNat v } } ∗ R).get
      (m.storeInt (S + x * 8#64 + 8248#64) 8 v.toInt) := by
  rw [Fld.fold_mapping_positionOf]; exact View.store_pos h hx v

end

/-! ## `Keep` -/

theorem Keep.refl (g : G) : Keep g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {g g1 g2 : G} (h1 : Keep g g1) (h2 : Keep g1 g2) : Keep g g2 :=
  ⟨h2.tgtp.trans h1.tgtp, h2.n.trans h1.n, h2.splp.trans h1.splp, h2.data.trans h1.data,
    h2.ops.trans h1.ops, h2.xs.trans h1.xs, h2.xo.trans h1.xo, h2.tgt.trans h1.tgt,
    h2.spl.trans h1.spl⟩

/-! ## Flags -/

-- `cmpq n, a; jnb`: the jump is not taken.
theorem lt_of_cf {a n : Word}
    (h : (!(((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))) = false) : a < n := by
  rw [Idioms.cf_sub] at h
  simpa [BitVec.lt_def] using h

-- `cmpq n, a; jnb`: the jump is taken.
theorem not_lt_of_cf {a n : Word}
    (h : (!(((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))) = true) : ¬a < n := by
  rw [Idioms.cf_sub] at h
  simpa [BitVec.lt_def] using h

-- `cmpq b, a; je`.
theorem eq_of_z {a b : Word} (h : (a - b == BitVec.zero 64) = true) : a = b := by
  simp only [beq_iff_eq] at h
  have : a - b = 0#64 := h
  bv_omega

theorem ne_of_z {a b : Word} (h : (a - b == BitVec.zero 64) = false) : a ≠ b := by
  intro e
  simp [e] at h

-- `cmpq $16, d; jbe`: the jump is taken.
theorem le_of_be {d : Word}
    (h : (((((d - 16#64).toNat : Int) != (d.toNat : Int) - 16)) || (d - 16#64 == BitVec.zero 64))
      = true) :
    d ≤ 16#64 := by
  rw [Idioms.cf_sub_imm d 16 (by decide)] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | h
  · bv_omega
  · have : d - 16#64 = 0#64 := h
    bv_omega

-- `cmpq $16, d; jbe`: the jump is not taken.
theorem not_le_of_be {d : Word}
    (h : (((((d - 16#64).toNat : Int) != (d.toNat : Int) - 16)) || (d - 16#64 == BitVec.zero 64))
      = false) :
    ¬d ≤ 16#64 := by
  rw [Idioms.cf_sub_imm d 16 (by decide)] at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  have : d - 16#64 ≠ 0#64 := h.2
  bv_omega

-- `xorq; salq $16; je`: the low 6 bytes of the two words are equal.
theorem slot_eq_iff {a b : Word} :
    (((a ^^^ b).shiftLeft 16 == BitVec.zero 64) = true)
      ↔ StackSlot.ofWord b = StackSlot.ofWord a := by
  rw [beq_iff_eq, show BitVec.zero 64 = 0#64 from rfl,
    show (a ^^^ b).shiftLeft 16 = (a ^^^ b) <<< 16 from rfl, Idioms.slot_eq_iff]
  simp only [StackSlot.ofWord, StackSlot.mk.injEq]
  constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩)

/-! ## The asm forms after `symexec_norm` -/

theorem rd_eq (m : Mem 64) (a : Addr) : BitVec.ofInt 64 (Mem.loadInt m a 8).get! = rd m a := rfl
theorem rdb_eq (m : Mem 64) (a : Addr) : BitVec.ofInt 8 (Mem.loadInt m a 1).get! = rdb m a := rfl

-- `leaq -8(%d,%size,8)`: the top slot.
theorem top_slot (d x : Word) :
    slotAt d x.toNat + BitVec.ofInt 64 (-8) = slotAt d (x - 1).toNat := by
  unfold slotAt; bv_omega

-- `leaq -1(%size)`
theorem add_neg_one (x : Word) : x + BitVec.ofInt 64 (-1) = x - 1 := by bv_omega

theorem rsi_eq (s : MachineData) : rsi s = s.regs.rsi.toBitVec := rfl

-- `movzbl` and then `movb %r8b`: the byte.
theorem byte_rt (b : BitVec 8) :
    BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) = b := by bv_decide

-- `zf` of `cmp b, a` (the VC writes the zero as `BitVec.zero`).
theorem sub_beq_zero (a b : Word) : (a - b == BitVec.zero 64) = (a == b) := by
  rw [BitVec.zero_eq]; exact Idioms.sub_beq_zero a b

-- `cmpq $-1`: the test for `NONE`.
theorem cmp_none (x : Word) :
    (x - 18446744073709551615#64 == BitVec.zero 64) = (x == Flat.NONE) := by
  rw [sub_beq_zero]; rfl

/-! ## Indexes in bounds -/

theorem put_eq_set {α : Type} (v : Vector α MAX_N) (i : Word) (x : α) (h : i.toNat < MAX_N) :
    Flat.put v i x = v.set i.toNat x h := by
  apply Vector.ext; intro j hj
  simp only [Flat.put, Vector.getElem_setIfInBounds hj, Vector.getElem_set h hj]

theorem get_eq {α : Type} [Inhabited α] (v : Vector α MAX_N) (i : Word) (h : i.toNat < MAX_N) :
    Flat.get v i = v[i.toNat] := by
  simp [Flat.get, h]

theorem vec_set {α : Type} [Inhabited α] (l : List α) (i : Nat) (x : α) (hi : i < l.length)
    (hn : i < MAX_N) : vec (l.set i x) = (vec l).set i x hn := by
  apply Vector.ext; intro j hj
  simp only [vec, Vector.getElem_ofFn, Vector.getElem_set, List.getElem?_set]
  by_cases e : i = j
  · subst e; simp [hi]
  · simp [e]

theorem get_vec {α : Type} [Inhabited α] (l : List α) (i : Word) (hi : i.toNat < l.length)
    (hn : i.toNat < MAX_N) : Flat.get (vec l) i = l[i.toNat] := by
  simp [Flat.get, hn, vec, hi]

theorem take_set_succ {α : Type} (l : List α) (i : Nat) (r : α) (hi : i < l.length) :
    (l.set i r).take (i + 1) = l.take i ++ [r] := by
  rw [List.take_add_one, List.getElem?_set_self hi, List.take_set_of_le (Nat.le_refl i)]
  rfl

theorem get_data {g : G} (hok : g.Ok) {i : Word} (hi : i.toNat < g.h.n.toNat + g.xs) :
    Flat.get (flat g).data i = StackSlot.ofWord g.stk[i.toNat] := by
  simp [Flat.get, flat, vec, Nat.lt_of_lt_of_le hi hok.xs, hi]

theorem none_toNat : Flat.NONE.toNat = 2 ^ 64 - 1 := rfl

theorem reach_iff (X : Flat.St) (t : Word) :
    Flat.isSwapReachable X t = true ↔ X.size - t - 1#64 ≤ 16#64 := by
  simp only [Flat.isSwapReachable, decide_eq_true_eq]
  simp only [Flat.depthOf, Flat.maxSwapDepth]
  constructor <;> intro h <;> bv_omega

section
variable {g1 : G} {S : Addr} {R : MProp 64} {m : Mem 64}

-- `xorq; salq $16; je`: the slots `a` and `b` of the stack.
theorem data_eq (hm : (View S g1 ∗ R).get m) (hok : g1.Ok) {a b : Word}
    (ha : a.toNat < g1.h.n.toNat + g1.xs) (hb : b.toNat < g1.h.n.toNat + g1.xs)
    (h : ((BitVec.ofInt 64 (m.loadInt (g1.h.data + b * 8#64) 8).get!
      ^^^ BitVec.ofInt 64 (m.loadInt (g1.h.data + a * 8#64) 8).get!).shiftLeft 16
      == BitVec.zero 64) = true) :
    Flat.get (flat g1).data a = Flat.get (flat g1).data b := by
  rw [rd_slot' hm ha, rd_slot' hm hb, slot_eq_iff] at h
  rw [get_data hok ha, get_data hok hb, h]

theorem data_ne (hm : (View S g1 ∗ R).get m) (hok : g1.Ok) {a b : Word}
    (ha : a.toNat < g1.h.n.toNat + g1.xs) (hb : b.toNat < g1.h.n.toNat + g1.xs)
    (h : ((BitVec.ofInt 64 (m.loadInt (g1.h.data + b * 8#64) 8).get!
      ^^^ BitVec.ofInt 64 (m.loadInt (g1.h.data + a * 8#64) 8).get!).shiftLeft 16
      == BitVec.zero 64) = false) :
    Flat.get (flat g1).data a ≠ Flat.get (flat g1).data b := by
  rw [rd_slot' hm ha, rd_slot' hm hb] at h
  rw [get_data hok ha, get_data hok hb]
  intro e
  rw [slot_eq_iff.mpr e] at h
  cases h

end

/-! ## The swap of two destinations -/

-- `m_positionOf[dest[i]] = i` if `dest[i]` is not none: one half of `swapDestinations`.
def posAt (st : Flat.St) (i : Word) : Flat.St :=
  { st with pos := if Flat.get st.dest i ≠ Flat.NONE then Flat.put st.pos (Flat.get st.dest i) i
      else st.pos }

-- The two stores of `m_destinationOf` in `swapDestinations`.
def swapD (d : Vector Word MAX_N) (a b : Word) : Vector Word MAX_N :=
  Flat.put (Flat.put d a (Flat.get d b)) b (Flat.get d a)

theorem swapDestinations_eq (st : Flat.St) (a b : Word) :
    Flat.swapDestinations st a b = posAt (posAt { st with dest := swapD st.dest a b } a) b := rfl

theorem posAt_none {st : Flat.St} {i : Word} (h : Flat.get st.dest i = Flat.NONE) :
    posAt st i = st := by
  simp [posAt, h]

theorem posAt_some {st : Flat.St} {i : Word} (h : Flat.get st.dest i ≠ Flat.NONE) :
    posAt st i = { st with pos := Flat.put st.pos (Flat.get st.dest i) i } := by
  simp [posAt, h]

-- The ghost with other destinations, or other positions.
def withDest (g : G) (d : Vector Word MAX_N) : G := { g with h := { g.h with dest := d } }
def withPos (g : G) (p : Vector Word MAX_N) : G := { g with h := { g.h with pos := p } }

section
variable {g : G}

theorem flat_withDest (d : Vector Word MAX_N) : flat (withDest g d) = { flat g with dest := d } :=
  rfl
theorem flat_withPos (p : Vector Word MAX_N) : flat (withPos g p) = { flat g with pos := p } :=
  rfl

theorem Ok.withDest (h : g.Ok) (d : Vector Word MAX_N) : (withDest g d).Ok :=
  ⟨h.len, h.n, h.xs, h.xo, h.nops, h.spl⟩
theorem Ok.withPos (h : g.Ok) (p : Vector Word MAX_N) : (withPos g p).Ok :=
  ⟨h.len, h.n, h.xs, h.xo, h.nops, h.spl⟩

theorem Keep.withDest (d : Vector Word MAX_N) : Keep g (withDest g d) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Keep.withPos (p : Vector Word MAX_N) : Keep g (withPos g p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

theorem rd_dest_get (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 56#64) 8).get! = Flat.get g.h.dest x := by
  rw [get_eq _ _ hx]; exact rd_dest' h hx

theorem store_dest_put (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) (v : Word) :
    (View S (withDest g (Flat.put g.h.dest x v)) ∗ R).get
      (m.storeInt (S + x * 8#64 + 56#64) 8 v.toInt) := by
  rw [put_eq_set _ _ _ hx]; exact store_dest' h hx v

theorem store_pos_put (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) (v : Word) :
    (View S (withPos g (Flat.put g.h.pos x v)) ∗ R).get
      (m.storeInt (S + x * 8#64 + 8248#64) 8 v.toInt) := by
  rw [put_eq_set _ _ _ hx]; exact store_pos' h hx v

end

/-! ## `Flat.stackSwap` on the ghost -/

-- The slot of the top word after the `movl` and the two `movb`.
theorem ofWord_411 (a b : Word) :
    StackSlot.ofWord (a.extractLsb' 48 16 ++ b.extractLsb' 40 8 ++ b.extractLsb' 32 8
      ++ b.extractLsb' 0 32) = StackSlot.ofWord b := by
  simp only [StackSlot.ofWord, StackSlot.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

-- The record of the asm: `movb $0`, `movb %dil` (`dil` is `size + ~pos`), `movl $0`, `movb $1`,
-- `movb $5`.
theorem op_eq (l p : Word) :
    (⟨BitVec.ofInt 8 0, BitVec.ofInt 8 ((l + ~~~p).extractLsb' 0 8).toInt,
      ⟨BitVec.ofInt 32 0, BitVec.ofInt 8 1, BitVec.ofInt 8 5⟩⟩ : Op) = Op.swapW (l - 1 - p) := by
  simp only [Op.swapW, StackSlot.junk, BitVec.ofInt_toInt, Op.mk.injEq, StackSlot.mk.injEq]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  bv_decide

/-! ## `pm_load`

A copy of `mem_load` of the unit proof of `swapWith`: it takes the memory `m` of the first load
in the goal, and tries the lemmas only on the hypotheses `h : P.get m`. If no hypothesis is on
`m`, it takes the memory under the last store of `m`, and so on. Untrusted: it only selects a
lemma. -/

open Lean in
/-- `m`, then the memories under the stores of `m`, the last store first. -/
meta partial def memChain (m : Expr) : List Expr :=
  if m.isAppOfArity ``Mem.storeInt 5 then m :: memChain (m.getArg! 1) else [m]

open Lean Meta Elab Tactic in
elab "pm_load " "[" ls:term,* "]" : tactic => withMainContext do
  let some ld := (← instantiateMVars (← getMainTarget)).find? (·.isAppOfArity ``Mem.loadInt 4)
    | throwError "pm_load: no load in the goal"
  for m in memChain (ld.getArg! 1) do
    let mut found := false
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      unless ty.isAppOfArity ``MProp.get 3 do continue
      unless ← withNewMCtxDepth <| withReducible <| isDefEq ty.appArg! m do continue
      found := true
      for l in ls.getElems do
        let s ← saveState
        try
          let hs ← Term.exprToSyntax d.toExpr
          Term.withoutErrToSorry <| evalTactic (← `(tactic|
            focus ((with_reducible apply $l $hs) <;> assumption) <;> done))
          return
        catch _ => s.restore
    if found then break
  throwError "pm_load: no lemma gives this load from the sep hyps on its memory"

end Permute
end Bbu.Unit
