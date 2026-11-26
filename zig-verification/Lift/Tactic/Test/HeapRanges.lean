module

public import Lift.Tactic.HeapSlice
public import Lift.Sem.HeapDec
meta import Lift.Sem.HeapBytes
meta import Lift.Sem.HeapWF
meta import Lift.Sem.HeapDec

@[expose] public section

namespace Lift.Tactic.Test.HeapRanges

open Lift.P2.Total Lift.Sem

set_option maxHeartbeats 20000

-- A byte range can cross typed cells inside one held object.
theorem object_range {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h) {offset : Nat}
    (hk : offset + 2 ≤ o.size) :
    h.loadB (o.addr + BitVec.ofNat 64 offset) .W16 =
      .ok (BitVec.ofInt 16 (Int.ofBytes ((o.bytes.drop offset).take 2))) := by
  heap_slice

-- An unknown prefix and suffix do not need an enumeration of the frame.
theorem framed_range {policy : CpuPolicy} {m : DataMem} {pre post : Heap} {o : Obj}
    (hh : Heap.Holds policy (pre ++ o :: post) m) {offset : Nat}
    (hk : offset + 4 ≤ o.size) :
    Heap.loadB (pre ++ o :: post) (o.addr + BitVec.ofNat 64 offset) .W32 =
      .ok (BitVec.ofInt 32 (Int.ofBytes ((o.bytes.drop offset).take 4))) := by
  heap_slice

-- This W16 range includes the last byte of one array word and the next byte.
theorem array_cross_cell {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {base : BitVec 64} {xs : List (BitVec 64)}
    (ho : Obj.words base false .W64 xs ∈ h) {index : Nat} (hi : index + 1 < xs.length) :
    h.loadB (base + BitVec.ofNat 64 (index * 8 + 7)) .W16 =
      .ok (BitVec.ofInt 16 (Int.ofBytes
        (((Obj.words base false .W64 xs).bytes.drop (index * 8 + 7)).take 2))) := by
  heap_slice

theorem array_cross_cell_bv {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {base index : BitVec 64} {xs : List (BitVec 64)}
    (ho : Obj.words base false .W64 xs ∈ h) (hi : index.toNat + 1 < xs.length) :
    h.loadB (base + index * 8 + 7) .W16 =
      .ok (BitVec.ofInt 16 (Int.ofBytes
        (((Obj.words base false .W64 xs).bytes.drop (index.toNat * 8 + 7)).take 2))) := by
  heap_slice

-- An array encoder can contain fields of different widths.
theorem encoded_record_range {α : Type} {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {base : BitVec 64} {xs : List α} {encode : α → List Cell}
    (ho : Obj.mk base false (xs.flatMap encode) ∈ h)
    (hs : ∀ x, cellsSize (encode x) = 12) {index : Nat} (hi : index < xs.length) :
    h.loadB (base + BitVec.ofNat 64 (index * 12 + 2)) .W32 =
      .ok (BitVec.ofInt 32 (Int.ofBytes
        ((((encode xs[index]).flatMap Cell.bytes).drop 2).take 4))) := by
  heap_slice

-- A wrong array membership must not stop the search for the matching one.
theorem encoded_record_range_bv {α : Type} {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {base otherBase index : BitVec 64} {xs ys : List α}
    {encode : α → List Cell}
    (_other : Obj.mk otherBase false (ys.flatMap encode) ∈ h)
    (ho : Obj.mk base false (xs.flatMap encode) ∈ h)
    (hs : ∀ x, cellsSize (encode x) = 12) (hi : index.toNat < xs.length) :
    h.loadB (base + index * 12 + 2) .W32 =
      .ok (BitVec.ofInt 32 (Int.ofBytes
        ((((encode xs[index.toNat]).flatMap Cell.bytes).drop 2).take 4))) := by
  heap_slice

-- An unknown encoder needs a fixed-size hypothesis.
example {α : Type} {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (_hh : h.Holds policy m) {base : BitVec 64} {xs : List α} {encode : α → List Cell}
    (_ho : Obj.mk base false (xs.flatMap encode) ∈ h)
    {index : Nat} (_hi : index < xs.length) : True := by
  fail_if_success
    have : h.loadB (base + BitVec.ofNat 64 (index * 12 + 2)) .W32 =
        .ok (BitVec.ofInt 32 (Int.ofBytes
          ((((encode xs[index]).flatMap Cell.bytes).drop 2).take 4))) := by
      heap_slice
  fail_if_success
    have : h.loadB (base + BitVec.ofNat 64 (index * 12)) .W32 =
        .ok (BitVec.ofInt 32 (Int.ofBytes
          ((((encode xs[index]).flatMap Cell.bytes).drop 0).take 4))) := by
      heap_slice
  trivial

def recordCells (x : BitVec 8 × BitVec 8 × BitVec 16) : List Cell :=
  [⟨.W8, x.1⟩, ⟨.W8, x.2.1⟩, ⟨.W16, x.2.2⟩]

theorem typed_record_range {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {base : BitVec 64}
    {xs : List (BitVec 8 × BitVec 8 × BitVec 16)}
    (ho : Obj.mk base true (xs.flatMap recordCells) ∈ h) {index : Nat} (hi : index < xs.length) :
    h.loadB (base + BitVec.ofNat 64 (index * 4)) .W32 =
      .ok (BitVec.ofInt 32 (Int.ofBytes
        ((((recordCells xs[index]).flatMap Cell.bytes).drop 0).take 4))) := by
  heap_slice

-- A slice of one selected record cannot stand for bytes from the next record.
example {policy : CpuPolicy} {h : Heap} {m : DataMem} (_hh : h.Holds policy m)
    {base : BitVec 64} {xs : List (BitVec 8 × BitVec 8 × BitVec 16)}
    (_ho : Obj.mk base true (xs.flatMap recordCells) ∈ h) {index : Nat}
    (_hi : index + 1 < xs.length) : True := by
  fail_if_success
    have : h.loadB (base + BitVec.ofNat 64 (index * 4 + 3)) .W32 =
        .ok (BitVec.ofInt 32 (Int.ofBytes
          ((((recordCells xs[index]).flatMap Cell.bytes).drop 3).take 4))) := by
      heap_slice
  trivial

-- The byte offset can be in a different association from the object's base.
theorem normalized_address {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h) {offset : Nat}
    (hk : offset + 2 + 4 ≤ o.size) :
    h.loadB (o.addr + BitVec.ofNat 64 offset + 2) .W32 =
      .ok (BitVec.ofInt 32 (Int.ofBytes ((o.bytes.drop (offset + 2)).take 4))) := by
  heap_slice

-- A held read-only alias does not need a first-object search proof.
theorem read_only_alias {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {o other : Obj} (ho : o ∈ h) (_ha : other ∈ h)
    (_ro : o.writable = false) (_rao : other.writable = false) (_same : o.addr = other.addr)
    {offset : Nat} (hk : offset + 2 ≤ o.size) :
    h.loadB (o.addr + BitVec.ofNat 64 offset) .W16 =
      .ok (BitVec.ofInt 16 (Int.ofBytes ((o.bytes.drop offset).take 2))) := by
  heap_slice

-- Missing bounds, missing heap membership, and missing Holds must be refused.
example {policy : CpuPolicy} {h : Heap} {m : DataMem} (_hh : h.Holds policy m)
    {o : Obj} (_ho : o ∈ h) {_offset : Nat} : True := by
  fail_if_success
    have : h.loadB (o.addr + BitVec.ofNat 64 _offset) .W16 =
        .ok (BitVec.ofInt 16 (Int.ofBytes ((o.bytes.drop _offset).take 2))) := by
      heap_slice
  trivial

example {policy : CpuPolicy} {h : Heap} {m : DataMem} (_hh : h.Holds policy m)
    {o : Obj} {offset : Nat} (_hk : offset + 2 ≤ o.size) : True := by
  fail_if_success
    have : h.loadB (o.addr + BitVec.ofNat 64 offset) .W16 =
        .ok (BitVec.ofInt 16 (Int.ofBytes ((o.bytes.drop offset).take 2))) := by
      heap_slice
  trivial

example {h : Heap} {o : Obj} (_ho : o ∈ h) {offset : Nat}
    (_hk : offset + 2 ≤ o.size) : True := by
  fail_if_success
    have : h.loadB (o.addr + BitVec.ofNat 64 offset) .W16 =
        .ok (BitVec.ofInt 16 (Int.ofBytes ((o.bytes.drop offset).take 2))) := by
      heap_slice
  trivial

-- Equal addresses do not give ownership or agreement for another object.
example {policy : CpuPolicy} {h : Heap} {m : DataMem} (_hh : h.Holds policy m)
    {o ghost : Obj} (_ho : o ∈ h) (_addr : o.addr = ghost.addr) {offset : Nat}
    (_hk : offset + 2 ≤ ghost.size) : True := by
  fail_if_success
    have : h.loadB (o.addr + BitVec.ofNat 64 offset) .W16 =
        .ok (BitVec.ofInt 16 (Int.ofBytes ((ghost.bytes.drop offset).take 2))) := by
      heap_slice
  trivial

-- The sample admission check rejects wrap and writable aliases.
example : True := by
  fail_if_success
    have : ∃ policy m,
        Heap.Holds policy [Obj.words 0xFFFFFFFFFFFFFFFF false .W16 [0]] m := by
      heap_admit
  fail_if_success
    have : ∃ policy m, Heap.Holds policy
        [Obj.words 0x1000 true .W64 [0], Obj.words 0x1004 false .W32 [0]] m := by
      heap_admit
  trivial

#print axioms object_range
#print axioms framed_range
#print axioms array_cross_cell
#print axioms array_cross_cell_bv
#print axioms normalized_address
#print axioms encoded_record_range
#print axioms encoded_record_range_bv
#print axioms typed_record_range

end Lift.Tactic.Test.HeapRanges
