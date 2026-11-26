import Skel.Lean.Sample
import Lift.Sem.HeapDec

/-! The tests of `Skel/Lean/Sample.lean` (suite `leansample`): `lake exe skel-test --only leansample`.
Each test name starts with `leansample.`. The property tests run over `cases` seeds from `seed`. The distribution and
boundary tests run over the fixed seeds `0 .. 999`. A test that fails gives one line. -/

namespace SampleTests

open Skel.Sample Lift.Sem Coordinator.Dst

/-- The seeds of the property tests: `cases` seeds from `seed`. -/
private def seedsOf (seed cases : Nat) : List Nat := (List.range cases).map (seed + ·)

/-- The fixed seeds of the distribution and boundary tests. -/
private def fixed : List Nat := List.range 1000

/-- The generator of seed `s`. -/
private def gen (s : Nat) : Rng := Rng.ofSeed s

/-- The value of the 64-bit word at `a`, if the load is `.ok`. -/
private def valueAt (h : Heap) (a : BitVec 64) : Option (BitVec 64) :=
  match h.load a .W64 with
  | .ok v => some v
  | _ => none

/-- The 64-bit words of an object. -/
private def wordsOf (o : Obj) : List (BitVec 64) := o.cells.filterMap (·.get .W64)

/-- An admitted array of stream `s`, is well formed and has the array and the frame. -/
private def arrayOk (s : Nat) (writable : Bool) : Bool :=
  match arraySample (gen s) writable with
  | some (p, xs, h) => holdsArray h.1 p xs && h.1.WF && xs.length ≤ maxLen
  | none => false

/-- The toy `Find` of seed `s`: the array, and the key is a word of the array or the other value. -/
private def toyFind (s : Nat) : Bool :=
  arrayOk s false && (match arraySample (gen s) false with
    | some (_, xs, _) => decide (memberOr ((gen s).stream 5) xs (5 : BitVec 64) ∈ xs ++ [5])
    | none => false)

/-- The toy `Walk` of seed `s`: the chain of the sample is the list of its node addresses. -/
private def toyWalk (s : Nat) : Bool :=
  match chainSample (gen s) with
  | some (_, ps, h) => h.1.WF && Heap.chain h.1 8 (ps.headD 0) == ps
  | none => false

/-- The tests: each name and whether it holds, for `seed` and `cases`. -/
private def tests (seed cases : Nat) : List (String × Bool) :=
  let seeds := seedsOf seed cases
  [ -- The sample instances: lists of 0 to 6 words, and a product by fields.
    ("leansample.list.size", seeds.all fun s => (Sample.draw (gen s) : List (BitVec 64)).length ≤ maxLen),
    ("leansample.list.lengths", (List.range (maxLen + 1)).all fun n =>
      fixed.any fun s => (Sample.draw (gen s) : List (BitVec 64)).length == n),
    ("leansample.product.fields", seeds.all fun s =>
      let x : BitVec 64 × List (BitVec 64) := Sample.draw (gen s)
      x.1 == (Sample.draw ((gen s).stream 0) : BitVec 64) &&
        x.2 == (Sample.draw ((gen s).stream 1) : List (BitVec 64))),
    -- Binders: addresses are 8-aligned and nonzero, below 2^43; the slots are a permutation.
    ("leansample.addr.bounds", fixed.all fun s =>
      let p := addrOf (gen s)
      p != 0 && p.toNat % 8 == 0 && p.toNat < 2 ^ 43),
    ("leansample.addr.distinct", (fixed.map fun s => (addrOf (gen s)).toNat).eraseDups.length == fixed.length),
    ("leansample.slots.permutation", (List.range (maxLen + 1)).all fun n =>
      seeds.all fun s => (slots (gen s) n).mergeSort (· ≤ ·) == List.range n),
    ("leansample.slots.empty-and-one", slots (gen 1) 0 == [] && slots (gen 1) 1 == [0]),
    ("leansample.slots.range", seeds.all fun s =>
      match slotAddrs (gen s) 0x1000 16 6 with
      | some ps => ps.length == 6 && ps.all fun p => 0x1000 ≤ p.toNat && p.toNat < 0x1000 + 96
      | none => false),
    ("leansample.counter.range", seeds.all fun s =>
      (List.range (maxLen + 1)).all fun n => counter ((gen s).stream n) n ≤ n + 3),
    -- Arrays (`Sum`, `Find`, `Fill`): the heap is well formed and holds the array; the frame is two words.
    ("leansample.array.wf", [true, false].all fun w => seeds.all fun s =>
      match arraySample (gen s) w with
      | some (_, _, h) => h.1.WF
      | none => false),
    ("leansample.array.simArr", [true, false].all fun w => seeds.all fun s => arrayOk s w),
    ("leansample.array.writable", [true, false].all fun w => seeds.all fun s =>
      match arraySample (gen s) w with
      | some (_, _, h) => h.1.head?.map (·.writable) == some w
      | none => false),
    ("leansample.array.frame", seeds.all fun s =>
      match arraySample (gen s) true with
      | some (p, _, h) =>
        let fr := h.1.tail
        fr.length == 1 && fr.all (fun o => o.writable && o.cells.length == 1) && fr.map (·.addr) == [p - 8]
      | none => false),
    -- No word is readable at the end of the array: a read of the word after the last one is a fault.
    ("leansample.array.nothingAfter", [true, false].all fun w => seeds.all fun s =>
      match arraySample (gen s) w with
      | some (p, xs, h) =>
        let hi := p + 8 * BitVec.ofNat 64 xs.length
        (valueAt h.1 hi).isNone && h.1.tail.all (fun o => o.addr != hi)
      | none => false),
    ("leansample.array.lastWord", seeds.all fun s =>
      match arraySample (gen s) false with
      | some (p, xs, h) => xs.isEmpty || valueAt h.1 (p + 8 * BitVec.ofNat 64 (xs.length - 1)) == xs.getLast?
      | none => false),
    -- Chains (`Walk`): the node addresses are the chain; the values are in the nodes; the heap is well formed.
    ("leansample.chain.total", seeds.all fun s => (chainSample (gen s)).isSome),
    ("leansample.chain.wf", seeds.all fun s =>
      match chainSample (gen s) with
      | some (_, _, h) => h.1.WF
      | none => false),
    ("leansample.chain.addresses", seeds.all fun s =>
      match chainSample (gen s) with
      | some (_, ps, h) => Heap.chain h.1 8 (ps.headD 0) == ps
      | none => false),
    ("leansample.chain.values", seeds.all fun s =>
      match chainSample (gen s) with
      | some (vs, ps, h) => (vs.zip ps).all fun (v, p) => valueAt h.1 p == some v
      | none => false),
    ("leansample.chain.nothingAfter", seeds.all fun s =>
      match chainSample (gen s) with
      | some (_, ps, h) => ps.isEmpty || (valueAt h.1 (ps.foldl (fun m p => if m < p then p else m) 0 + 16)).isNone
      | none => false),
    ("leansample.chain.distinct", seeds.all fun s =>
      match chainSample (gen s) with
      | some (_, ps, _) => ps.eraseDups.length == ps.length && ps.all (· != 0)
      | none => false),
    ("leansample.chain.boundaries", [0, 1, maxLen].all fun n => fixed.any fun s =>
      match chainSample (gen s) with
      | some (vs, _, _) => vs.length == n
      | none => false),
    ("leansample.chain.empty", fixed.all fun s =>
      match chainSample (gen s) with
      | some (_, [], h) => Heap.chain h.1 8 0 == []
      | some _ => true
      | none => false),
    -- The four toys of seeds 1 to 3.
    ("leansample.toys.sum", [1, 2, 3].all fun s => arrayOk s false),
    ("leansample.toys.find", [1, 2, 3].all fun s => toyFind s),
    ("leansample.toys.fill", [1, 2, 3].all fun s => arrayOk s true),
    ("leansample.toys.walk", [1, 2, 3].all fun s => toyWalk s),
    -- Free states: a pointer is a visit's pointer, the counter and the kinds, the frame bump, and the one-in-two member.
    ("leansample.visit.other-differs", (List.range 9).all fun m =>
      (List.range (m + 2)).all fun j => fixed.all fun s =>
        match otherVisit (gen s) (m + 2) j with
        | some k => k < m + 2 && k != j
        | none => false),
    ("leansample.visit.other-covers", fixed.any (fun s => otherVisit (gen s) 3 1 == some 0) &&
      fixed.any (fun s => otherVisit (gen s) 3 1 == some 2)),
    ("leansample.pointer.walk-states", fixed.all fun s =>
      match chainSample (gen s) with
      | some (_, ps, _) => match pointer ((gen s).stream 1) (ps ++ [0]) with
        | some p => p == 0 || ps.contains p
        | none => false
      | none => false),
    ("leansample.freeKind.all", [FreeKind.counter, .fromVisit, .word, .frame].all fun k =>
      fixed.any fun s => freeKind (gen s) == k),
    ("leansample.bump.one-word", seeds.all fun s =>
      match arraySample (gen s) true with
      | some (_, _, h) =>
        let fr := h.1.tail
        match bumpFrame (gen s) fr with
        | some fr' =>
          let d := (fr'.zip fr).filter fun (a, b) => wordsOf a != wordsOf b
          fr'.length == fr.length && d.length == 1 &&
            d.all fun (a, b) => wordsOf a == (wordsOf b).map (· + 1)
        | none => false
      | none => false),
    ("leansample.memberOr.empty", seeds.all fun s => memberOr (gen s) ([] : List (BitVec 64)) 5 == 5),
    ("leansample.memberOr.half", 400 ≤ (fixed.filter fun s =>
      memberOr (gen s) [(7 : BitVec 64), 8, 9] 5 != 5).length &&
      (fixed.filter fun s => memberOr (gen s) [(7 : BitVec 64), 8, 9] 5 != 5).length ≤ 600),
    ("leansample.shown.index",
      shownAt toString (fun _ => some 1) (fun _ => 2) 7 0 == "1" &&
      shownAt toString (fun _ => some 1) (fun _ => 2) 7 1 == "2" &&
      shownAt toString (fun (_ : Rng) => (none : Option Nat)) (fun _ => 2) 7 0 == "skipped"),
    ("leansample.determinism", seeds.all fun s =>
      (arraySample (gen s) true).map (fun (p, xs, h) => (p, xs, h.1)) ==
        (arraySample (gen s) true).map (fun (p, xs, h) => (p, xs, h.1))),
    ("leansample.determinism.seeds-differ",
      (fixed.map fun s => (arraySample (gen s) true).map (fun (_, xs, _) => xs)).eraseDups.length > 100),
    -- Negative cases: a request that cannot be met gives `none`, and a heap that is not well formed is refused.
    ("leansample.neg.overlap",
      (WFHeap.of? [Obj.words 0x1000 true .W64 [1, 2], Obj.words 0x1008 false .W64 [3]]).isNone),
    ("leansample.neg.wrap", (WFHeap.of? [Obj.words 0xFFFFFFFFFFFFFFF8 false .W64 [1, 2]]).isNone),
    ("leansample.neg.adjacent-ok",
      (WFHeap.of? [Obj.words 0x1000 true .W64 [1], Obj.words 0x1008 false .W64 [2]]).isSome),
    ("leansample.neg.slots-base-zero", (slotAddrs (gen 1) 0 16 2).isNone),
    ("leansample.neg.slots-size-zero", (slotAddrs (gen 1) 0x1000 0 2).isNone),
    ("leansample.neg.slots-wrap", (slotAddrs (gen 1) 0xFFFFFFFFFFFFFF00 16 17).isNone),
    ("leansample.slots.top-edge", (slotAddrs (gen 1) 0xFFFFFFFFFFFFFF00 16 16).isSome),
    ("leansample.neg.nodes-length", (nodes? [1, 2] [0x1000]).isNone),
    ("leansample.neg.admit-none", (admit (fun (_ : Rng) => (none : Option Nat)) (gen 1)).isNone),
    ("leansample.neg.admit-redraw-last",
      admit (fun r => if r == (gen 1).stream 8 then some 1 else none) (gen 1) == some 1),
    ("leansample.neg.admit-redraw-past",
      (admit (fun r => if r == (gen 1).stream 9 then some 1 else none) (gen 1)).isNone),
    ("leansample.neg.visit-none", (otherVisit (gen 1) 0 0).isNone && (otherVisit (gen 1) 1 0).isNone),
    ("leansample.neg.pointer-empty", (pointer (gen 1) []).isNone),
    ("leansample.neg.bump-empty", (bumpFrame (gen 1) []).isNone) ]

/-- Runs the tests whose name starts with `only` (all when `only` is `none`); one line for each failed test. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  let mut failed := 0
  for (name, ok) in tests seed cases do
    if only.all (fun p => name.startsWith p) && !ok then
      IO.println s!"FAIL {name}"
      failed := failed + 1
  return failed

end SampleTests
