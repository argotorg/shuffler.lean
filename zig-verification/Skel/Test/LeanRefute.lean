import Skel.Lean.Refute

/-! Tests of `Skel.Refute` (`Skel/Lean/Refute.lean`) on a counter loop from 0 to `n`.
At `head`, a state `i` goes to `body` when `i < n`, else to `done`. `body` goes to `head` with `i + 1`.
`done` returns `i`. The tests are `#guard` commands, so they run when the module is built. -/

namespace Skel.Test.LeanRefute

open Lift.Sem Coordinator.Dst Skel.Refute

inductive Lbl where
  | head | body | done
  deriving DecidableEq

def counter (n : Nat) : Leaf Lbl Nat Nat :=
  { step := fun l i => match l with
      | .head => .ok (if i < n then .goto .body i else .goto .done i)
      | .body => .ok (.goto .head (i + 1))
      | .done => .ok (.ret i) }

/-- The loop refuted with the given invariant, measure and result; the admitted state is `(0, n)`. -/
def triple (n : Nat) (inv : Nat → Bool) (μ : Nat → Nat) (out : Nat → Nat) (samples : Nat) : Found :=
  refuteLoop (counter n) Lbl.head (2 * n + 8) inv μ out (fun _ => (0, n))
    (fun g => (g.natIn 0 (n + 3)).1) 1 samples

/-- The true triple: `i ≤ n`, measure `n - i`, result `n`. -/
def trueTriple (n samples : Nat) : Found :=
  triple n (fun i => decide (i ≤ n)) (fun i => n - i) (fun _ => n) samples

-- The true triple gives `pass`, for n above 0, for n = 0, and with zero samples.
#guard trueTriple 5 200 == Found.pass 200
#guard trueTriple 0 200 == Found.pass 200
#guard trueTriple 5 0 == Found.pass 0

-- The invariant `true` with free states above `n` gives `cti` (not `real`: the free state is not admitted).
#guard (match triple 5 (fun _ => true) (fun i => 5 - i) (fun _ => 5) 200 with
  | .cti _ _ => true | _ => false)

-- A wrong result gives `real`, at the admitted sample 0.
#guard triple 5 (fun i => decide (i ≤ 5)) (fun i => 5 - i) (fun _ => 6) 200
  == Found.real 0 "entry: result differs from expected"

-- `stepTo`: fuel counts blocks; fuel 0 fails.
#guard (match stepTo (counter 5) Lbl.head 0 Lbl.head 0 with | .fail _ => true | _ => false)
#guard (match stepTo (counter 5) Lbl.head 1 Lbl.head 0 with | .fail _ => true | _ => false)
#guard (match stepTo (counter 5) Lbl.head 2 Lbl.head 0 with | .head 1 => true | _ => false)
#guard (match stepTo (counter 5) Lbl.head 2 Lbl.head 5 with | .ret 5 => true | _ => false)

-- `stepFails`: none when the invariant is false at the state, and for a correct step.
#guard (stepFails (counter 5) Lbl.head 18 (fun i => decide (i ≤ 5)) (fun i => 5 - i) (fun _ => 5) 7).isNone
#guard (stepFails (counter 5) Lbl.head 18 (fun i => decide (i ≤ 5)) (fun i => 5 - i) (fun _ => 5) 3).isNone
#guard (stepFails (counter 5) Lbl.head 18 (fun _ => true) (fun _ => 0) (fun _ => 5) 2).isSome

-- `sampleAt`: even index admitted, odd index free.
#guard (match sampleAt (fun _ => (0, 1)) (fun _ => 2) 1 0 with | .admitted 0 1 => true | _ => false)
#guard (match sampleAt (fun _ => (0, 1)) (fun _ => 2) 1 1 with | .free 2 => true | _ => false)

-- `refuteClaim`: equal sides pass; differing sides give `real` at sample 0; zero samples pass.
#guard refuteClaim (fun g => (g.natIn 0 100).1) (fun x => some x) (fun x => some x) 1 200
  == Found.pass 200
#guard refuteClaim (fun g => (g.natIn 0 100).1) (fun x => some x) (fun x => some (x + 1)) 1 200
  == Found.real 0 "lhs and rhs differ"
#guard refuteClaim (fun g => (g.natIn 0 100).1) (fun x => some x) (fun x => some (x + 1)) 1 0
  == Found.pass 0

-- `Found.line`: one JSON line; strings are escaped.
#guard Found.line (.cti 3 "stuck") (fun _ => "s")
  == "{\"verdict\":\"cti\",\"index\":3,\"why\":\"stuck\",\"shown\":\"s\"}"
#guard Found.line (.pass 200) (fun _ => "") == "{\"verdict\":\"pass\",\"samples\":200}"
#guard Found.line (.real 1 "a\"b") (fun _ => "x")
  == "{\"verdict\":\"real\",\"index\":1,\"why\":\"a\\\"b\",\"shown\":\"x\"}"

/-! Ghost values: `refuteLoopG`, `runFailsG` and `stepFailsG`. The ghost is carried with the state. -/

/-- The triple of seed `k`: the invariant, the measure and the result of the counter loop with `n = k % 6`. -/
def variantTriple (k : Nat) : (Nat → Bool) × (Nat → Nat) × (Nat → Nat) :=
  let n := k % 6
  let inv : Nat → Bool := match k % 3 with
    | 0 => fun i => decide (i ≤ n)
    | 1 => fun _ => true
    | _ => fun i => decide (i < n + 2)
  let out : Nat → Nat := if k % 4 = 0 then fun _ => n + 1 else fun _ => n
  (inv, fun i => n - i, out)

-- With a unit ghost, `refuteLoopG` gives the verdict of `refuteLoop` for seeds 0 to 39.
#guard (List.range 40).all fun k =>
  let n := k % 6
  let (inv, μ, out) := variantTriple k
  let adm : Rng → Nat × Nat := fun _ => (0, n)
  let free : Rng → Nat := fun g => (g.natIn 0 (n + 3)).1
  refuteLoop (counter n) Lbl.head (2 * n + 8) inv μ out adm free k 30
    == refuteLoopG (counter n) Lbl.head (2 * n + 8) (fun (_ : Unit) => inv) (fun _ => μ) (fun _ => out)
      (fun g => ((), (adm g).1, (adm g).2)) (fun g => ((), free g)) k 30

-- With a unit ghost, `stepFailsG` and `runFailsG` give the verdicts of `stepFails` and `runFails` on states 0 to 7.
#guard (List.range 40).all fun k =>
  let n := k % 6
  let (inv, μ, out) := variantTriple k
  (List.range 8).all fun i =>
    stepFails (counter n) Lbl.head (2 * n + 8) inv μ out i
      == stepFailsG (counter n) Lbl.head (2 * n + 8) (fun (_ : Unit) => inv) (fun _ => μ) (fun _ => out) () i
    && runFails (counter n) Lbl.head (2 * n + 8) inv μ out i n
      == runFailsG (counter n) Lbl.head (2 * n + 8) (fun (_ : Unit) => inv) (fun _ => μ) (fun _ => out) () i n

/-! The Walk form: a list walk. The heap is a list of next pointers and is in the state. The ghost `n` is the number of
nodes from the entry. It is not in the state: it is carried with the state, and the invariant and the result read it. -/

inductive WLbl where
  | head | body | done
  deriving DecidableEq

structure WSt where
  heap : List Nat
  p : Nat
  c : Nat

def walkLeaf : Leaf WLbl WSt Nat :=
  { step := fun l x => match l with
      | .head => .ok (if x.p = 0 then .goto .done x else .goto .body x)
      | .body => .ok (.goto .head { x with p := x.heap.getD x.p 0, c := x.c + 1 })
      | .done => .ok (.ret x.c) }

/-- The heap of a chain of `n` nodes: node `i` points to `i + 1`, node `n` to `0`. -/
def chainHeap (n : Nat) : List Nat := (List.range (n + 1)).map fun i => if i < n then i + 1 else 0

/-- The number of nodes from `p` on, at most `k` of them. -/
def remain (heap : List Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, p => if p = 0 then 0 else 1 + remain heap k (heap.getD p 0)

/-- The entry pointer of the chain of `n` nodes. -/
def entryOf (n : Nat) : Nat := if n = 0 then 0 else 1

/-- An admitted sample: the ghost `n`, the state at the entry of a chain of `n` nodes, and the result `n`. -/
def walkAdmitted (g : Rng) : Nat × WSt × Nat :=
  let (n, _) := g.natIn 0 5
  (n, ⟨chainHeap n, entryOf n, 0⟩, n)

/-- A free sample: the ghost `n`, the chain of `n` nodes, and a pointer and a count below `n + 4`. -/
def walkFree (g : Rng) : Nat × WSt :=
  let (n, g) := g.natIn 0 5
  let (p, g) := g.natIn 0 (n + 3)
  let (c, _) := g.natIn 0 (n + 3)
  (n, ⟨chainHeap n, p, c⟩)

/-- The invariant: the count and the nodes left give `n`. -/
def walkInv (n : Nat) (x : WSt) : Bool := decide (x.c + remain x.heap (x.heap.length + 1) x.p = n)
def walkMeasure (n : Nat) (x : WSt) : Nat := n - x.c
def walkOut (n : Nat) (_ : WSt) : Nat := n

-- The true triple with the ghost gives `pass`, for seeds 0 to 4 and 200 samples.
#guard (List.range 5).all fun s => refuteLoopG walkLeaf WLbl.head 8 walkInv walkMeasure walkOut walkAdmitted walkFree s 200
  == Found.pass 200

-- Negative: an invariant that reads the ghost but is too weak (`c ≤ n`) gives `cti` at a free sample.
#guard (match refuteLoopG walkLeaf WLbl.head 8 (fun n x => decide (x.c ≤ n)) walkMeasure walkOut walkAdmitted
    walkFree 1 200 with
  | .cti _ _ => true | _ => false)

-- Negative: an invariant that reads the ghost wrongly (`n + 1`) fails at the entry: `real` at sample 0.
#guard refuteLoopG walkLeaf WLbl.head 8 (fun n x => decide (x.c + remain x.heap (x.heap.length + 1) x.p = n + 1))
    walkMeasure walkOut walkAdmitted walkFree 1 200
  == Found.real 0 "entry: invariant fails"

-- Negative: a result that reads the ghost wrongly (`n + 1`) fails at the entry: `real` at sample 0.
#guard refuteLoopG walkLeaf WLbl.head 8 walkInv walkMeasure (fun n _ => n + 1) walkAdmitted walkFree 1 200
  == Found.real 0 "entry: result differs from expected"

-- Boundary: zero samples give `pass 0`; a chain of zero nodes (the loop is not entered) gives `pass`.
#guard refuteLoopG walkLeaf WLbl.head 8 walkInv walkMeasure walkOut walkAdmitted walkFree 1 0 == Found.pass 0
#guard refuteLoopG walkLeaf WLbl.head 8 walkInv walkMeasure walkOut
    ((fun _ => (0, ⟨chainHeap 0, 0, 0⟩, 0)) : Rng → Nat × WSt × Nat)
    ((fun _ => (0, ⟨chainHeap 0, 0, 0⟩)) : Rng → Nat × WSt) 1 50 == Found.pass 50

-- Boundary: fuel 0 cannot take a step. The first sample is admitted, so the result is `real`.
#guard refuteLoopG walkLeaf WLbl.head 0 walkInv walkMeasure walkOut walkAdmitted walkFree 1 5
  == Found.real 0 "no fuel"
#guard stepFailsG walkLeaf WLbl.head 0 walkInv walkMeasure walkOut 0 ⟨chainHeap 0, 0, 0⟩ == some "no fuel"

/-! Optional draws must skip all checks. A run with no draws has no test coverage. -/

def noAdmitted : Rng → Option (Unit × Nat × Nat) := fun _ => none
def noFree : Rng → Option (Unit × Nat) := fun _ => none
def noInput : Rng → Option Nat := fun _ => none

#guard (sampleAtG? noAdmitted noFree 1 0).isNone
#guard (sampleAtG? noAdmitted noFree 1 1).isNone
#guard (admittedState? noAdmitted noFree (Rng.ofSeed 1)).isNone
#guard refuteLoopG (counter 0) Lbl.head 0 (fun (_ : Unit) _ => false) (fun _ _ => 0)
    (fun _ _ => 1) noAdmitted noFree 1 8 == Found.unknown "no admitted samples"
#guard refuteLoopG (counter 0) Lbl.head 0 (fun (_ : Unit) _ => false) (fun _ _ => 0)
    (fun _ _ => 1) noAdmitted noFree 1 0 == Found.pass 0
#guard refuteLoopG (counter 0) Lbl.head 8 (fun (_ : Unit) _ => true) (fun _ _ => 0)
    (fun _ _ => 0) noAdmitted ((fun _ => some ((), 0)) : Rng → Option (Unit × Nat)) 1 8 == Found.pass 8
#guard refuteLoopG (counter 0) Lbl.head 8 (fun (_ : Unit) _ => true) (fun _ _ => 0)
    (fun _ _ => 0) ((fun _ => some ((), 0, 1)) : Rng → Option (Unit × Nat × Nat)) noFree 1 8
      == Found.real 0 "entry: result differs from expected"
#guard refuteLoopG (counter 0) Lbl.head 8 (fun (_ : Unit) _ => true) (fun _ _ => 0)
    (fun _ _ => 0) ((fun _ => some ((), 0, 0)) : Rng → Option (Unit × Nat × Nat)) noFree 1 8
      == Found.pass 4

#guard refuteClaim noInput (fun x => some x) (fun x => some (x + 1)) 1 8
  == Found.unknown "no admitted samples"
#guard refuteClaim noInput (fun x => some x) (fun x => some (x + 1)) 1 0 == Found.pass 0
#guard refuteClaim ((fun _ => some 7) : Rng → Option Nat) (fun x => some x) (fun x => some (x + 1)) 1 8
  == Found.real 0 "lhs and rhs differ"
#guard Found.line (.unknown "no admitted samples") (fun _ => "unused")
  == "{\"verdict\":\"unknown\",\"why\":\"no admitted samples\"}"

end Skel.Test.LeanRefute
