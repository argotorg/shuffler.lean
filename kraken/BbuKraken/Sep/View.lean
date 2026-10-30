import BbuKraken.Sep.Atoms
import BbuKraken.Sep.Fields

/-!
# The struct as separation atoms

`View S g` is the memory of `struct Emission` at `S`, of its working stack `m_stack.m_data`, of
its trace buffer `m_stack.m_trace`, of its target `m_target` and of the bytes of `m_spills` that
`isSpilled` can read, with the values of the ghost `g`. The ghost has one field for
each word of the struct (`Hdr`), and `Vector`s for the arrays, so a ghost with an array of the wrong
length does not typecheck. The struct atoms use the addresses of `Fields.lean`.
-/

namespace Bbu.Sep

/-! ## Op records (`ShuffleOp`, 12 bytes) -/

-- A record: the model `Op` and the 4 padding bytes (2-3 and 10-11) that no store writes.
structure OpR where
  op : Op
  pad2 : BitVec 16
  pad10 : BitVec 16

-- Record `i` of the buffer at `o`; slot `i` of the word array at `d`.
def opAt (o : Addr) (i : Nat) : Addr := o + BitVec.ofNat 64 (12 * i)
def slotAt (d : Addr) (i : Nat) : Addr := d + BitVec.ofNat 64 (8 * i)

-- Bytes 0, 1: kind, depth; 4-7: payload; 8: slot kind; 9: valueOpcode.
def OpM (a : Addr) (r : OpR) : MProp 64 :=
  B8 a r.op.kind ∗ B8 (a + 1#64) r.op.depth ∗ B16 (a + 2#64) r.pad2
    ∗ B32 (a + 4#64) r.op.slot.payload ∗ B8 (a + 8#64) r.op.slot.kind
    ∗ B8 (a + 9#64) r.op.slot.valueOpcode ∗ B16 (a + 10#64) r.pad10

-- Records `k, k+1, ...` of the buffer at `o`. The index is part of the atom address, so the
-- address of a record is `opAt o i` with no address arithmetic.
def Ops (o : Addr) (k : Nat) : List OpR → MProp 64
  | [] => MProp.emp
  | r :: rs => OpM (opAt o k) r ∗ Ops o (k + 1) rs

theorem Ops.append (o : Addr) (k : Nat) (xs ys : List OpR) :
    Ops o k (xs ++ ys) = Ops o k xs ∗ Ops o (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [Ops, MProp.emp_sep]
  | cons x xs ih =>
    simp only [List.cons_append, Ops, ih, MProp.sep_assoc, List.length_cons]
    rw [Nat.add_assoc, Nat.add_comm 1]

-- Record `i` set to `r`, and the rest.
theorem Ops.focus (o : Addr) (rs : List OpR) {i : Nat} (hi : i < rs.length) (r : OpR) :
    Ops o 0 (rs.set i r)
      = OpM (opAt o i) r ∗ (Ops o 0 (rs.take i) ∗ Ops o (i + 1) (rs.drop (i + 1))) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left_of_eq_true _ _ (eq_true hi), Ops.append]
  simp only [Ops, List.length_take, Nat.zero_add, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [← MProp.sep_assoc, MProp.sep_comm (Ops _ _ _) (OpM _ _), MProp.sep_assoc]

theorem Ops.focus_self (o : Addr) (rs : List OpR) {i : Nat} (hi : i < rs.length) :
    Ops o 0 rs = OpM (opAt o i) rs[i] ∗ (Ops o 0 (rs.take i) ∗ Ops o (i + 1) (rs.drop (i + 1))) := by
  conv => lhs; rw [← List.set_getElem_self hi]
  exact Ops.focus o rs hi _

/-! ## The spilled bytes -/

-- The byte `f i` of `m_spills` at `a + i`, for each id `i` in `is`.
def Spl (a : Addr) (f : BitVec 32 → BitVec 8) : List Nat → MProp 64
  | [] => MProp.emp
  | i :: is => B8 (a + BitVec.ofNat 64 i) (f (BitVec.ofNat 32 i)) ∗ Spl a f is

-- The ids of the spilled bytes that `isSpilled` can read: the variables of the target words.
-- An id is in the list once, because two atoms at one address do not hold together.
def splIds (tgt : List Word) : List Nat :=
  (tgt.filterMap fun w => spillId (StackSlot.ofWord w)).eraseDups

-- The atom of the id `i`, and the rest.
theorem Spl.focus (a : Addr) (f : BitVec 32 → BitVec 8) {is : List Nat} {i : Nat} (hi : i ∈ is) :
    ∃ R, Spl a f is = B8 (a + BitVec.ofNat 64 i) (f (BitVec.ofNat 32 i)) ∗ R := by
  induction is with
  | nil => cases hi
  | cons j js ih =>
    rcases List.mem_cons.mp hi with rfl | h
    · exact ⟨_, rfl⟩
    · obtain ⟨R, e⟩ := ih h
      refine ⟨B8 (a + BitVec.ofNat 64 j) (f (BitVec.ofNat 32 j)) ∗ R, ?_⟩
      rw [Spl, e, ← MProp.sep_assoc, MProp.sep_comm (B8 _ _) (B8 _ _), MProp.sep_assoc]

/-! ## The struct -/

-- The words of `struct Emission`, in the order of the members.
structure Hdr where
  tgt : Word
  n : Word
  spl : Word
  data : Word
  len : Word
  ops : Word
  nops : Word
  dest : Vector Word MAX_N
  pos : Vector Word MAX_N
  pend : Word
  blkOff : Word
  blkExc : Word

-- The struct at `S`. `Fld.mapping_destinationOf S i` and `Fld.mapping_positionOf S i` are the
-- addresses of element `i` of the two arrays (`Arr.rd`).
def Em (S : Addr) (h : Hdr) : MProp 64 :=
  Wd (Fld.target S) h.tgt ∗ Wd (Fld.targetSize S) h.n ∗ Wd (Fld.spills S) h.spl
    ∗ Wd (Fld.stack_data S) h.data ∗ Wd (Fld.stack_size S) h.len ∗ Wd (Fld.stack_trace S) h.ops
    ∗ Wd (Fld.stack_traceSize S) h.nops
    ∗ Arr (S + BitVec.ofNat 64 56) h.dest.toList ∗ Arr (S + BitVec.ofNat 64 8248) h.pos.toList
    ∗ Wd (Fld.pendingGenerations S) h.pend ∗ Wd (Fld.blocked_offset S) h.blkOff
    ∗ Wd (Fld.blocked_excess S) h.blkExc

-- The ghost: the struct, the working stack (`n` slots), the trace buffer (`6n` records), the
-- target (`n` words) and the spilled bytes (`m_spills[i]` is `spl i`).
structure G where
  h : Hdr
  stk : Vector Word h.n.toNat
  ops : Vector OpR (6 * h.n.toNat)
  tgt : Vector Word h.n.toNat
  spl : BitVec 32 → BitVec 8

-- The struct at `S`, the working stack, the trace buffer, the target, and the spilled bytes of
-- the variables of the target.
def View (S : Addr) (g : G) : MProp 64 :=
  Em S g.h ∗ Arr g.h.data g.stk.toList ∗ Ops g.h.ops 0 g.ops.toList
    ∗ Arr g.h.tgt g.tgt.toList ∗ Spl g.h.spl g.spl (splIds g.tgt.toList)

-- The ghost invariant that the contracts keep.
structure G.Ok (g : G) : Prop where
  len : g.h.len.toNat ≤ g.h.n.toNat
  n : g.h.n.toNat ≤ MAX_N
  nops : g.h.nops.toNat ≤ 6 * g.h.n.toNat

end Bbu.Sep
