module

public import FlatShuffler.Sep.Stores
import all FlatShuffler.Sep.Stores
public import ProofKit.SymExec
import all ProofKit.SymExec
public import Kraken.X64.Parser
import all Kraken.X64.Parser

@[expose] public section

/-!
Tests of the struct view: the load and store lemmas of each kind of field, the folds of the asm
addresses on real `kvcgen64` VCs, and the types of the ghost.
-/

open Kraken.X64.Parser
open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace FlatShuffler.Sep.ViewTest

open FlatShuffler.Sep

variable [Host] [FunDecls] {S : Addr} {g : G} {F : MProp 64} {m : Mem 64} {w : Word}

/-! ## Words of the struct -/

example (h : (View S g ∗ F).get m) :
    rd (m.storeInt (Fld.stack_size S) 8 w.toInt) (Fld.stack_size S) = w
    ∧ rd (m.storeInt (Fld.stack_size S) 8 w.toInt) (Fld.stack_data S) = g.h.data := by
  have h1 := View.store_len h w
  exact ⟨View.rd_len h1, (View.rd_data h1 :)⟩

example (h : (View S g ∗ F).get m) :
    rd (m.storeInt (Fld.stack_traceSize S) 8 w.toInt) (Fld.stack_traceSize S) = w
    ∧ rd (m.storeInt (Fld.stack_traceSize S) 8 w.toInt) (Fld.stack_trace S) = g.h.ops :=
  ⟨View.rd_nops (View.store_nops h w), (View.rd_ops (View.store_nops h w) :)⟩

/-! ## Arrays -/

-- A store to element 3 of `m_positionOf`, then a load of element 3 and of element 4.
example (h : (View S g ∗ F).get m) :
    rd (m.storeInt (Fld.mapping_positionOf S 3) 8 w.toInt) (Fld.mapping_positionOf S 3) = w
    ∧ rd (m.storeInt (Fld.mapping_positionOf S 3) 8 w.toInt) (Fld.mapping_positionOf S 4)
      = g.h.pos[4]'(by decide) := by
  have h1 := View.store_pos h (by decide : 3 < MAX_N) w
  refine ⟨(View.rd_pos h1 (by decide : 3 < MAX_N)).trans ?_,
    (View.rd_pos h1 (by decide : 4 < MAX_N)).trans ?_⟩ <;> simp

-- The last element of `m_destinationOf` is in the view, the next is not.
example (h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.mapping_destinationOf S (MAX_N - 1)) 8).isSome = true :=
  View.isSome_dest h (by decide)
example (_h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.mapping_destinationOf S MAX_N) 8).isSome = true ∨ True := by
  fail_if_success (left; exact View.isSome_dest _h (by decide))
  exact Or.inr trivial

-- A slot of the working stack.
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    ((m.storeInt (slotAt g.h.data i) 8 w.toInt).loadInt (slotAt g.h.data i) 8).isSome = true := by
  have h1 := View.store_stk h hi w
  exact (View.isSome_slot h1 hi :)

-- A load of a stack slot below `n` with `view_load` (`View.isSome_slot_n`), and above `n` (in
-- the slack `xs`, `View.isSome_slot`).
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) :
    (m.loadInt (slotAt g.h.data i) 8).isSome = true := by
  view_load
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data i) 8).isSome = true := by
  view_load
-- Negative: with no bound of the slot, `view_load` does not close the load.
/-- error: sep_load: no sep hyp gives this load -/
#guard_msgs in
example (h : (View S g ∗ F).get m) {i : Nat} :
    (m.loadInt (slotAt g.h.data i) 8).isSome = true := by
  view_load

-- A store to slot `i`, then a load of slot `i` and of a different slot `j`.
example (h : (View S g ∗ F).get m) {i j : Nat} (hi : i < g.h.n.toNat + g.xs) (hj : j < g.h.n.toNat + g.xs)
    (hij : i ≠ j) :
    rd (m.storeInt (slotAt g.h.data i) 8 w.toInt) (slotAt g.h.data i) = w
    ∧ rd (m.storeInt (slotAt g.h.data i) 8 w.toInt) (slotAt g.h.data j) = g.stk[j] := by
  have h1 := View.store_stk h hi w
  exact ⟨(View.rd_slot h1 hi).trans (by simp),
    (View.rd_slot h1 hj).trans (by simp [hij])⟩

-- Byte 4 of a slot (the kind) in the form of `cmpb $3, 4(%rdx,%rsi,8)` (`4#64`), after a store
-- of the slot: the byte of the stored word.
example (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat + g.xs) :
    rdb (m.storeInt (slotAt g.h.data k) 8 w.toInt) (slotAt g.h.data k + 4#64) = w.extractLsb' 32 8
    ∧ ((m.storeInt (slotAt g.h.data k) 8 w.toInt).loadInt (slotAt g.h.data k + 4#64) 1).isSome
      = true := by
  have h1 := View.store_stk h hk w
  exact ⟨(View.rdb_slot h1 hk (j := 4) (by decide)).trans (by simp),
    View.isSome_slot_byte h1 hk (j := 4) (by decide)⟩

-- Byte 0 and byte 7 of a slot.
example (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat + g.xs) :
    rdb m (slotAt g.h.data k + BitVec.ofNat 64 0) = g.stk[k].extractLsb' 0 8
    ∧ rdb m (slotAt g.h.data k + BitVec.ofNat 64 7) = g.stk[k].extractLsb' 56 8 :=
  ⟨View.rdb_slot h hk (j := 0) (by decide), View.rdb_slot h hk (j := 7) (by decide)⟩

-- Negative: byte 8 is not a byte of the slot. The same steps with byte 7 close the goal.
example (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data k + BitVec.ofNat 64 7) 1).isSome = true := by
  apply View.isSome_slot_byte h hk; decide
example (_h : (View S g ∗ F).get m) {k : Nat} (_hk : k < g.h.n.toNat + g.xs) :
    (m.loadInt (slotAt g.h.data k + BitVec.ofNat 64 8) 1).isSome = true ∨ True := by
  fail_if_success (left; apply View.isSome_slot_byte _h _hk; decide; done)
  exact Or.inr trivial

/-! ## Op records -/

-- Take record `i` out, store its kind and payload, load its depth, and put it back.
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < 6 * g.h.n.toNat + g.xo) (x y : Int) :
    ∃ r, (View S { g with ops := g.ops.set i r } ∗ F).get
      ((m.storeInt (opAt g.h.ops i) 1 x).storeInt (opAt g.h.ops i + 4#64) 4 y) := by
  have h1 := OpM.store_kind (View.focus h hi) x
  have h2 := OpM.store_payload h1 y
  have _ := OpM.isSome_depth h2
  exact ⟨_, View.unfocus h2 hi⟩

-- `view_load` finds the record hypothesis and the lemma of the byte.
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < 6 * g.h.n.toNat + g.xo) :
    (m.loadInt (opAt g.h.ops i + 9#64) 1).isSome = true := by
  have _h1 := View.focus h hi
  view_load

-- Negative: `view_load` does not close a load at a byte that no lemma gives (byte 2 is padding).
/-- error: sep_load: no sep hyp gives this load -/
#guard_msgs in
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < 6 * g.h.n.toNat + g.xo) :
    (m.loadInt (opAt g.h.ops i + 2#64) 1).isSome = true := by
  have _h1 := View.focus h hi
  view_load

/-! ## Folds of the asm addresses -/

example (n : Word) : S + n * 8#64 + 8248#64 = Fld.mapping_positionOf S n.toNat :=
  Fld.fold_mapping_positionOf S n
example (o n : Word) : o + (n + n * 2#64).shiftLeft 2 = opAt o n.toNat := fold_op o n
example (d n : Word) : d + n * 8#64 = slotAt d n.toNat := fold_slot d n

-- Real VCs: two loads and a store. After `symexec_norm`, the folds give the field names, and
-- `view_load` closes the load VCs.
example (s : MachineData) (hm : (View S g ∗ F).get s.dmem) (hS : rdi s = S) {i : Nat}
    (hi : i < MAX_N) (hx : (s.regs.get64 .rsi).toNat = i) :
    ⦃ fun t => t = s ⦄ parse("
      movq 32(%rdi), %rax
      movq 8248(%rdi,%rsi,8), %rcx
      movq %rcx, 48(%rdi)")
    ⦃ (fun _ t => rax t = g.h.len
        ∧ (View S { g with h := { g.h with nops := g.h.pos[i] } } ∗ F).get t.dmem);
      fun _ _ => False ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst ht
  kvcgen64
  all_goals symexec_norm
  case vc1 => rw [hS, Fld.fold_stack_size]; view_load
  case vc2 => rw [hS, Fld.fold_mapping_positionOf, hx]; view_load
  case vc3 => rw [hS, Fld.fold_stack_traceSize]; view_load
  case vc4 => rw [hS, Fld.fold_stack_size]; exact View.rd_len hm
  case vc5 =>
    rw [hS, Fld.fold_stack_traceSize, Fld.fold_mapping_positionOf, hx]
    change (_ ∗ F).get (Mem.storeInt _ _ 8 (rd t.dmem (Fld.mapping_positionOf S i)).toInt)
    rw [View.rd_pos hm hi]
    exact View.store_nops hm _

/-! ## Types of the ghost -/

def hdr4 : Hdr := ⟨0, 4#64, 0, 0, 0, 0, 0, Vector.replicate MAX_N 0, Vector.replicate MAX_N 0, 0, 0, 0⟩

-- A stack of `n = 4` slots and `6n = 24` records.
example : G := ⟨hdr4, 0, 0, Vector.replicate 4 (0 : Word), Vector.replicate 24 ⟨⟨0, 0, ⟨0, 0, 0⟩⟩, 0, 0⟩,
  Vector.replicate 4 (0 : Word), fun _ => 0⟩
-- With the slack `xs = 2` and `xo = 3`: a stack of 6 slots and 27 records.
example : G := ⟨hdr4, 2, 3, Vector.replicate 6 (0 : Word), Vector.replicate 27 ⟨⟨0, 0, ⟨0, 0, 0⟩⟩, 0, 0⟩,
  Vector.replicate 4 (0 : Word), fun _ => 0⟩

-- Negative: a stack of 3 slots for `n = 4` does not typecheck.
/--
error: Application type mismatch: The argument
  Vector.replicate 3 0
has type
  Vector Word 3
but is expected to have type
  Vector Word (BitVec.toNat hdr4.n + 0)
in the application
  G.mk hdr4 0 0 (Vector.replicate 3 0)
-/
#guard_msgs in
example : G := ⟨hdr4, 0, 0, Vector.replicate 3 (0 : Word), Vector.replicate 24 ⟨⟨0, 0, ⟨0, 0, 0⟩⟩, 0, 0⟩,
  Vector.replicate 4 (0 : Word), fun _ => 0⟩

-- Negative: a target of 5 words for `n = 4` does not typecheck.
/--
error: Application type mismatch: The argument
  Vector.replicate 5 0
has type
  Vector Word 5
but is expected to have type
  Vector Word (BitVec.toNat hdr4.n)
in the application
  G.mk hdr4 0 0 (Vector.replicate 4 0)
    (Vector.replicate 24
      { op := { kind := 0, depth := 0, slot := { payload := 0, kind := 0, valueOpcode := 0 } }, pad2 := 0, pad10 := 0 })
    (Vector.replicate 5 0)
-/
#guard_msgs in
example : G := ⟨hdr4, 0, 0, Vector.replicate 4 (0 : Word), Vector.replicate 24 ⟨⟨0, 0, ⟨0, 0, 0⟩⟩, 0, 0⟩,
  Vector.replicate 5 (0 : Word), fun _ => 0⟩

/-! ## The target and the spilled bytes -/

-- A variable (kind 0, opcode 1) with the id 7, a literal (opcode 0) with the payload 9, and a
-- label (kind 3) with the payload 5.
def var7 : Word := 7#64 + (1#64 <<< 40)
def lit9 : Word := 9#64
def lbl5 : Word := 5#64 + (3#64 <<< 32)

-- Each id is in the list once; a literal and a label give no id.
example : splIds [var7, lit9, var7, lbl5] = [7] := by decide
example : splIds [] = [] := by decide
example : splIds [lit9, lbl5] = [] := by decide
example : splIds [var7 + 1#64, var7] = [8, 7] := by decide
-- The bytes 6 and 7 of a word are not part of the slot.
example : splIds [var7 + (1#64 <<< 56), var7] = [7] := by decide

-- A load of a target word and of the spilled byte of an id of the target.
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) :
    rd m (slotAt g.h.tgt i) = g.tgt[i] ∧ (m.loadInt (slotAt g.h.tgt i) 8).isSome = true :=
  ⟨View.rd_tgt h hi, View.isSome_tgt h hi⟩

example (h : (View S g ∗ F).get m) (hok : g.Ok) (hv : var7 ∈ g.tgt.toList) :
    (m.loadInt (g.h.spl + BitVec.ofNat 64 7) 1).isSome = true
    ∧ rdb m (g.h.spl + BitVec.ofNat 64 7) = g.spl 7 :=
  have hi := List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨var7, hv, by decide⟩)
  ⟨View.isSome_spl h hok hi, View.rdb_spl h hok hi⟩

-- Negative: the view gives no byte for an id that is not in the target.
example (_h : (View S g ∗ F).get m) (_hok : g.Ok) (_hv : g.tgt.toList = [lit9]) :
    (m.loadInt (g.h.spl + BitVec.ofNat 64 9) 1).isSome = true ∨ True := by
  fail_if_success (left; exact View.isSome_spl _h _hok (by rw [_hv]; decide))
  exact Or.inr trivial

/-! ## A spilled byte in the target -/

-- The target of `n = 2` words at `0x1000` holds the bytes `0x1000 ..< 0x1010`. `splOut` keeps the
-- ids whose byte is not in the target.
example : splOut 0x1000#64 0x1000#64 2 [0, 15, 16, 17] = [16, 17] := by decide
example : splOut 0x1000#64 0x0ff0#64 2 [15, 16, 31, 32] = [15, 32] := by decide
example : splOut 0x1000#64 0x1000#64 2 [] = [] := by decide
-- With `n = 0` the target holds no byte.
example : splOut 0x1000#64 0x1000#64 0 [0, 1] = [0, 1] := by decide
-- The address `spilled + i` wraps to the target.
example : splOut 0#64 (-4#64) 1 [3, 4, 11, 12] = [3, 12] := by decide

-- The byte of the id 7 at `0xffc + 7` is byte 3 of the target word at `0x1000`. The atoms of the
-- target and of the spilled bytes hold on the 8 bytes of the word.
example (w : Word) (f : BitVec 32 → BitVec 8) :
    (Arr 0x1000#64 [w] ∗ Spl 0x0ffc#64 f (splOut 0x1000#64 0x0ffc#64 1 [7])).get
      ((Int.toBytes 8 w.toInt).At 0x1000#64) := by
  rw [show splOut 0x1000#64 0x0ffc#64 1 [7] = [] by decide]
  simp only [Arr, Spl, MProp.sep_emp]
  unfold Wd
  rw [List.get_AtM]

-- A byte of a target word, at the last byte.
example (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat) :
    rdb m (slotAt g.h.tgt k + BitVec.ofNat 64 7) = g.tgt[k].extractLsb' 56 8 :=
  View.rdb_tgt_byte h hk (by decide)

-- Negative: byte 8 is not a byte of the word. The same steps with byte 7 close the goal.
example (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat) :
    rdb m (slotAt g.h.tgt k + BitVec.ofNat 64 7) = g.tgt[k].extractLsb' (8 * 7) 8 := by
  apply View.rdb_tgt_byte h hk; decide
example (_h : (View S g ∗ F).get m) {k : Nat} (_hk : k < g.h.n.toNat) :
    rdb m (slotAt g.h.tgt k + BitVec.ofNat 64 8) = g.tgt[k].extractLsb' (8 * 8) 8 ∨ True := by
  fail_if_success (left; apply View.rdb_tgt_byte _h _hk; decide; done)
  exact Or.inr trivial

-- The byte of the id 7 is byte 3 of target word 0. The load gives the byte of the word, and
-- `G.Ok` gives that this byte is `g.spl 7`.
example (h : (View S g ∗ F).get m) (hok : g.Ok) (hv : var7 ∈ g.tgt.toList) (hn : 0 < g.h.n.toNat)
    (ha : g.h.spl + BitVec.ofNat 64 7 = slotAt g.h.tgt 0 + BitVec.ofNat 64 3) :
    rdb m (g.h.spl + BitVec.ofNat 64 7) = g.tgt[0].extractLsb' 24 8
    ∧ rdb m (g.h.spl + BitVec.ofNat 64 7) = g.spl 7 :=
  have hi : 7 ∈ splIds g.tgt.toList :=
    List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨var7, hv, by decide⟩)
  ⟨ha ▸ View.rdb_tgt_byte h hn (j := 3) (by decide), View.rdb_spl h hok hi⟩

end FlatShuffler.Sep.ViewTest
