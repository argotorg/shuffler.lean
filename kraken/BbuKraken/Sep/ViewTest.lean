import BbuKraken.Sep.Stores
import ProofKit.SymExec
import Kraken.X64.Parser

/-!
Tests of the struct view: the load and store lemmas of each kind of field, the folds of the asm
addresses on real `kvcgen64` VCs, and the types of the ghost.
-/

open Kraken.X64.Parser
open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu.Sep.ViewTest

open Bbu.Sep

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
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) :
    ((m.storeInt (slotAt g.h.data i) 8 w.toInt).loadInt (slotAt g.h.data i) 8).isSome = true := by
  have h1 := View.store_stk h hi w
  exact (View.isSome_slot h1 hi :)

/-! ## Op records -/

-- Take record `i` out, store its kind and payload, load its depth, and put it back.
example (h : (View S g ∗ F).get m) {i : Nat} (hi : i < 6 * g.h.n.toNat) (x y : Int) :
    ∃ r, (View S { g with ops := g.ops.set i r } ∗ F).get
      ((m.storeInt (opAt g.h.ops i) 1 x).storeInt (opAt g.h.ops i + 4#64) 4 y) := by
  have h1 := OpM.store_kind (View.focus h hi) x
  have h2 := OpM.store_payload h1 y
  have _ := OpM.isSome_depth h2
  exact ⟨_, View.unfocus h2 hi⟩

/-! ## Folds of the asm addresses -/

example (n : Word) : S + n * 8#64 + 8248#64 = Fld.mapping_positionOf S n.toNat :=
  Fld.fold_mapping_positionOf S n
example (o n : Word) : o + (n + n * 2#64).shiftLeft 2 = opAt o n.toNat := fold_op o n
example (d n : Word) : d + n * 8#64 = slotAt d n.toNat := fold_slot d n

-- Real VCs: two loads and a store. After `symexec_norm`, the folds give the field names.
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
  case vc1 => rw [hS, Fld.fold_stack_size]; exact View.isSome_len hm
  case vc2 => rw [hS, Fld.fold_mapping_positionOf, hx]; exact View.isSome_pos hm hi
  case vc3 => rw [hS, Fld.fold_stack_traceSize]; exact View.isSome_nops hm
  case vc4 => rw [hS, Fld.fold_stack_size]; exact View.rd_len hm
  case vc5 =>
    rw [hS, Fld.fold_stack_traceSize, Fld.fold_mapping_positionOf, hx]
    change (_ ∗ F).get (Mem.storeInt _ _ 8 (rd t.dmem (Fld.mapping_positionOf S i)).toInt)
    rw [View.rd_pos hm hi]
    exact View.store_nops hm _

/-! ## Types of the ghost -/

def hdr4 : Hdr := ⟨0, 4#64, 0, 0, 0, 0, 0, Vector.replicate MAX_N 0, Vector.replicate MAX_N 0, 0, 0, 0⟩

-- A stack of `n = 4` slots and `6n = 24` records.
example : G := ⟨hdr4, Vector.replicate 4 (0 : Word), Vector.replicate 24 ⟨⟨0, 0, ⟨0, 0, 0⟩⟩, 0, 0⟩⟩

-- Negative: a stack of 3 slots for `n = 4` does not typecheck.
/--
error: Application type mismatch: The argument
  Vector.replicate 3 0
has type
  Vector Word 3
but is expected to have type
  Vector Word (BitVec.toNat hdr4.n)
in the application
  G.mk hdr4 (Vector.replicate 3 0)
-/
#guard_msgs in
example : G := ⟨hdr4, Vector.replicate 3 (0 : Word), Vector.replicate 24 ⟨⟨0, 0, ⟨0, 0, 0⟩⟩, 0, 0⟩⟩

end Bbu.Sep.ViewTest
