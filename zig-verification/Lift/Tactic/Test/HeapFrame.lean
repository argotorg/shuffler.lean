module

public import Lift.Tactic.LoopClose

@[expose] public section

namespace Lift.Tactic.Test.HeapFrame
open Lift.P2.Total Lift.Sem

set_option maxHeartbeats 20000

-- An already reduced field goal must reach the cell rules.
example (x : BitVec 16) : cellGet [⟨.W16, x⟩] 0 .W16 = some x := by
  field_eval

-- The selected object is after an unknown prefix, with an unknown suffix.
example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p : BitVec 64) (x y : BitVec 16)
    (hh : (pre ++ ⟨p, true, [⟨.W16, x⟩, ⟨.W16, y⟩]⟩ :: post).Holds pol m) :
    (pre ++ ⟨p, true, [⟨.W16, x⟩, ⟨.W16, y⟩]⟩ :: post).load (p + 2) .W16 = .ok y := by
  heap_frame

-- A typed store keeps both frames and the untouched field.
example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p : BitVec 64) (x y v : BitVec 16)
    (hh : (pre ++ ⟨p, true, [⟨.W16, x⟩, ⟨.W16, y⟩]⟩ :: post).Holds pol m) :
    (pre ++ ⟨p, true, [⟨.W16, x⟩, ⟨.W16, y⟩]⟩ :: post).storeB (p + 2) .W16 v =
      .ok (pre ++ ⟨p, true, [⟨.W16, x⟩, ⟨.W16, v⟩]⟩ :: post) := by
  heap_frame

-- A byte store spans two fields without changing either frame.
example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p : BitVec 64) (x y : BitVec 8) (v : BitVec 16)
    (hh : (pre ++ ⟨p, true, [⟨.W8, x⟩, ⟨.W8, y⟩]⟩ :: post).Holds pol m) :
    (pre ++ ⟨p, true, [⟨.W8, x⟩, ⟨.W8, y⟩]⟩ :: post).storeB p .W16 v =
      .ok (pre ++ ⟨p, true,
        [⟨.W8, v.extractLsb' 0 8⟩, ⟨.W8, v.extractLsb' 8 8⟩]⟩ :: post) := by
  heap_frame

end Lift.Tactic.Test.HeapFrame

namespace Lift.Tactic.Test.HeapFrame
open Lift.P2.Total Lift.Sem

set_option maxHeartbeats 20000

example (pol : CpuPolicy) (m : DataMem) (pre post : Heap) (o : Obj)
    (hh : (pre ++ o :: post).Holds pol m) : (pre ++ post).Holds pol m := by
  heap_frame

-- A byte write inside a wider cell keeps the typed cell layout and both frames.
example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p : BitVec 64) (x : BitVec 32) (v : BitVec 8)
    (hh : (pre ++ ⟨p, true, [⟨.W32, x⟩]⟩ :: post).Holds pol m) :
    (pre ++ ⟨p, true, [⟨.W32, x⟩]⟩ :: post).storeB (p + 1) .W8 v =
      .ok (pre ++ (Obj.setBytes (p + 1) .W8 v ⟨p, true, [⟨.W32, x⟩]⟩) :: post) := by
  heap_frame

-- Duplicate read-only objects remain separate list occurrences.
example (pol : CpuPolicy) (m : DataMem) (o : Obj) (F : Heap)
    (hh : Heap.Holds pol (o :: o :: F) m) : Heap.Holds pol [o, o] m := by
  heap_frame

example (pol : CpuPolicy) (m m' : DataMem) (h h' F : Heap)
    (hh : (h ++ F).Holds pol m) (hout : h'.Holds pol m')
    (shape : h.SameShape h')
    (frame : ∀ b, ¬ h.Owned b → m'.get? b = m.get? b) :
    (h' ++ F).Holds pol m' := by
  heap_call Heap.Holds.reassemble

-- Layout alone must not transfer the contents of a frame to another memory.
example : True := by
  fail_if_success
    have bad : ∀ (pol : CpuPolicy) (m m' : DataMem) (h h' F : Heap),
        (h ++ F).Holds pol m → h'.Holds pol m' → h.SameShape h' →
        (h' ++ F).Holds pol m' := by
      intros
      heap_frame
  trivial

-- A read-only object cannot be used as the target of a store.
example : True := by
  fail_if_success
    have bad : ∀ (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
        (p : BitVec 64) (x v : BitVec 16),
        (pre ++ ⟨p, false, [⟨.W16, x⟩]⟩ :: post).Holds pol m →
        (pre ++ ⟨p, false, [⟨.W16, x⟩]⟩ :: post).storeB p .W16 v =
          .ok (pre ++ ⟨p, false, [⟨.W16, v⟩]⟩ :: post) := by
      intros
      heap_frame
  trivial

-- The rule must not invent a second occurrence during selection.
example : True := by
  fail_if_success
    have bad : ∀ (pol : CpuPolicy) (m : DataMem) (o : Obj),
        Heap.Holds pol [o] m → Heap.Holds pol [o, o] m := by
      intros
      heap_frame
  trivial

-- A supplied call rule leaves missing preconditions open.
example (P : Prop) (_rule : P → True) : True := by
  fail_if_success (heap_call _rule; done)
  trivial

example (P : Prop) (rule : P → True) (hp : True → P) : True := by
  heap_call rule
  guard_target = P
  exact hp True.intro

-- An operation on the first goal must not consume the second goal.
example (pol : CpuPolicy) (m : DataMem) (p : BitVec 64) (x : BitVec 16)
    (hh : Heap.Holds pol [⟨p, true, [⟨.W16, x⟩]⟩] m) :
    Heap.load [⟨p, true, [⟨.W16, x⟩]⟩] p .W16 = .ok x ∧ True := by
  constructor
  heap_frame
  trivial

example (pol : CpuPolicy) (m : DataMem) (p : BitVec 64) (x : BitVec 16)
    (hh : Heap.Holds pol [⟨p, true, [⟨.W16, x⟩]⟩] m) :
    Heap.load [⟨p, true, [⟨.W16, x⟩]⟩] p .W16 = .ok x ∧ True := by
  constructor
  · heap_frame
  · trivial

-- Selection crosses append boundaries without inspecting the frame.
example (pol : CpuPolicy) (m : DataMem) (a b : Obj) (F : Heap)
    (hh : Heap.Holds pol ([a] ++ F ++ [b]) m) : Heap.Holds pol [a, b] m := by
  heap_frame

-- Backtrack after the first object does not match the store address.
example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p q : BitVec 64) (x y v : BitVec 16)
    (hh : (pre ++ ⟨p, true, [⟨.W16, x⟩]⟩ :: ⟨q, true, [⟨.W16, y⟩]⟩ :: post).Holds pol m) :
    (pre ++ ⟨p, true, [⟨.W16, x⟩]⟩ :: ⟨q, true, [⟨.W16, y⟩]⟩ :: post).storeB q .W16 v =
      .ok (pre ++ ⟨p, true, [⟨.W16, x⟩]⟩ :: ⟨q, true, [⟨.W16, v⟩]⟩ :: post) := by
  heap_frame

example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p : BitVec 64) (x v : BitVec 16)
    (hh : Heap.Holds pol ((pre ++ [⟨p, true, [⟨.W16, x⟩]⟩]) ++ post) m) :
    Heap.storeB ((pre ++ [⟨p, true, [⟨.W16, x⟩]⟩]) ++ post) p .W16 v =
      .ok ((pre ++ [⟨p, true, [⟨.W16, v⟩]⟩]) ++ post) := by
  heap_frame

-- A symbolic array store keeps both unknown frames.
example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p : BitVec 64) (xs : List (BitVec 16)) (i : Nat) (v : BitVec 16)
    (hi : i < xs.length)
    (hh : (pre ++ Obj.words p true .W16 xs :: post).Holds pol m) :
    (pre ++ Obj.words p true .W16 xs :: post).storeB (p + BitVec.ofNat 64 (i * 2)) .W16 v =
      .ok (pre ++ Obj.words p true .W16 (xs.set i v) :: post) := by
  heap_frame

-- loop_close uses the common tactic for a selected framed load.
example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p : BitVec 64) (x : BitVec 16)
    (hh : (pre ++ ⟨p, true, [⟨.W16, x⟩]⟩ :: post).Holds pol m) :
    (pre ++ ⟨p, true, [⟨.W16, x⟩]⟩ :: post).load p .W16 = .ok x := by
  loop_close

-- A local permission proof can establish a symbolic write flag.
example (pol : CpuPolicy) (m : DataMem) (pre post : Heap)
    (p : BitVec 64) (x v : BitVec 16) (wr : Bool) (hw : wr = true)
    (hh : (pre ++ ⟨p, wr, [⟨.W16, x⟩]⟩ :: post).Holds pol m) :
    (pre ++ ⟨p, wr, [⟨.W16, x⟩]⟩ :: post).store p .W16 v =
      .ok (pre ++ ⟨p, wr, [⟨.W16, v⟩]⟩ :: post) := by
  heap_frame

-- An opaque heap can supply an object through a checked membership fact.
example (pol : CpuPolicy) (m : DataMem) (h : Heap) (o : Obj)
    (a : BitVec 64) (w : Width) (v : w.type)
    (hh : h.Holds pol m) (ho : o ∈ h)
    (hc : cellGet o.cells (a - o.addr).toNat w = some v) :
    h.load a w = .ok v := by
  heap_frame

-- Selection must not change an object in the frame.
example : True := by
  fail_if_success
    have bad : ∀ (pol : CpuPolicy) (m : DataMem) (p q : BitVec 64) (x y v : BitVec 16),
        Heap.Holds pol [⟨p, true, [⟨.W16, x⟩]⟩, ⟨q, false, [⟨.W16, y⟩]⟩] m →
        Heap.storeB [⟨p, true, [⟨.W16, x⟩]⟩, ⟨q, false, [⟨.W16, y⟩]⟩] p .W16 v =
          .ok [⟨p, true, [⟨.W16, v⟩]⟩, ⟨q, false, [⟨.W16, x⟩]⟩] := by
      intros
      heap_frame
  trivial

example : True := by
  fail_if_success
    have bad : ∀ (pol : CpuPolicy) (m : DataMem) (p : BitVec 64) (x v : BitVec 16),
        Heap.Holds pol [⟨p, true, [⟨.W16, x⟩]⟩] m →
        Heap.storeB [⟨p, true, [⟨.W16, x⟩]⟩] p .W16 v =
          .ok [⟨p + 1, false, [⟨.W16, v⟩]⟩] := by
      intros
      heap_frame
  trivial

end Lift.Tactic.Test.HeapFrame
