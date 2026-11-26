import Lean

/-! The fueled L3 toys of the suite `discoverl3` (`Skel/Test/DiscoverL3.lean`, task DISC-FUEL). It is a module of its own,
so that the generated files of the tests (the traces, the searches, the checks) import it without the tests.

Each toy is a loop `f (fuel : Nat) (st : S) : R` that recurs on the fuel, with one caller in this module:
- `sumLoop` checks its exit before it uses fuel; at the fuel `0` with the exit true it gives `.done`. Its caller `sumAll`
  gives the fuel `xs.size` and the entry state `⟨xs, 0, 0⟩`.
- `walkLoop` checks the fuel first and calls the helper `advance`, which calls the nested helper `bumpLo`; its test is the
  helper `active`.
- `gapWalk` is called from `gapFrom`, which has a precondition `lo ≤ hi` and an `if` on the path to the call. With no entry
  fact the loop does not end (from `lo > hi`).
- `shortLoop` is `sumLoop` with a caller that gives one fuel too few: the negative control.
- `wideLoop` reads 8 fields with 28 comparisons: more than `maxPool` items before the cut.
- `deepLoop` calls `d1`, which calls `d2`, which calls `d3`: the pool reads `d2` (depth 2), not `d3` (depth 3).

The `example`s are the ground truth, checked by the kernel when this module is built. -/

namespace DiscoverL3Toys

/-- A result with an out-of-fuel value. -/
inductive Res where
  | done (v : Nat)
  | stuck
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The state of the sum: the array, the index, the sum so far. -/
structure Acc where
  xs : Array Nat
  i : Nat
  s : Nat
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The sum of the elements from `i`: the exit test comes before the fuel test. -/
def sumLoop (fuel : Nat) (st : Acc) : Res :=
  if st.i < st.xs.size then
    match fuel with
    | 0 => .stuck
    | n + 1 => sumLoop n { st with i := st.i + 1, s := st.s + st.xs[st.i]! }
  else .done st.s

/-- A use of `sumLoop` with no argument: no call site (the reader meets it before `sumAll`, by the order of the names). -/
def asFn : Nat → Acc → Res := sumLoop

/-- The caller of `sumLoop`: the fuel is the size of the array. -/
def sumAll (xs : Array Nat) : Res := sumLoop xs.size ⟨xs, 0, 0⟩

/-- `sumLoop` again, with a caller that gives one fuel too few. -/
def shortLoop (fuel : Nat) (st : Acc) : Res :=
  if st.i < st.xs.size then
    match fuel with
    | 0 => .stuck
    | n + 1 => shortLoop n { st with i := st.i + 1, s := st.s + st.xs[st.i]! }
  else .done st.s

/-- The caller of `shortLoop`: the fuel `xs.size - 1` is too small for each array that is not empty. -/
def shortAll (xs : Array Nat) : Res := shortLoop (xs.size - 1) ⟨xs, 0, 0⟩

/-- The state of the walk: a counter `lo` that goes up to `hi`, and a weight. -/
structure Pos where
  lo : Nat
  hi : Nat
  w : Nat
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The test of the walk. -/
def active (p : Pos) : Bool := p.lo < p.hi

/-- The nested helper: one more for the counter. -/
def bumpLo (p : Pos) : Pos := { p with lo := p.lo + 1 }

/-- The helper step: add the counter to the weight, then `bumpLo`. -/
def advance (p : Pos) : Pos := bumpLo { p with w := p.w + p.lo }

/-- The walk: the fuel test comes first; the step and the test are helpers. -/
def walkLoop : Nat → Pos → Option Nat
  | 0, _ => none
  | n + 1, p => if active p then walkLoop n (advance p) else some p.w

/-- The caller of `walkLoop`. -/
def walkAll (hi : Nat) : Option Nat := walkLoop (hi + 1) ⟨0, hi, 0⟩

/-- The state of the gap walk. -/
structure Win where
  lo : Nat
  hi : Nat
  acc : Nat
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- The gap walk: it ends at `lo = hi`, so only from `lo ≤ hi`. -/
def gapWalk : Nat → Win → Option Nat
  | 0, _ => none
  | n + 1, s => if s.lo = s.hi then some s.acc else gapWalk n { s with lo := s.lo + 1, acc := s.acc + 1 }

/-- The caller of `gapWalk`: a precondition, and an `if` on the path to the call. -/
def gapFrom (lo hi : Nat) (_h : lo ≤ hi) : Option Nat :=
  if hi < 50 then gapWalk (hi - lo + 1) ⟨lo, hi, 0⟩ else none

/-- The state of the wide loop: eight counters. -/
structure Wide where
  f0 : Nat
  f1 : Nat
  f2 : Nat
  f3 : Nat
  f4 : Nat
  f5 : Nat
  f6 : Nat
  f7 : Nat
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A loop whose test compares each pair of the eight fields. -/
def wideLoop : Nat → Wide → Option Nat
  | 0, _ => none
  | n + 1, s =>
    if s.f0 < s.f1 && s.f0 < s.f2 && s.f0 < s.f3 && s.f0 < s.f4 && s.f0 < s.f5 && s.f0 < s.f6 && s.f0 < s.f7 &&
        s.f1 < s.f2 && s.f1 < s.f3 && s.f1 < s.f4 && s.f1 < s.f5 && s.f1 < s.f6 && s.f1 < s.f7 &&
        s.f2 < s.f3 && s.f2 < s.f4 && s.f2 < s.f5 && s.f2 < s.f6 && s.f2 < s.f7 &&
        s.f3 < s.f4 && s.f3 < s.f5 && s.f3 < s.f6 && s.f3 < s.f7 &&
        s.f4 < s.f5 && s.f4 < s.f6 && s.f4 < s.f7 &&
        s.f5 < s.f6 && s.f5 < s.f7 &&
        s.f6 < s.f7 then wideLoop n { s with f0 := s.f0 + 1 }
    else some s.f0

/-- The helpers of the deep loop: `d1` calls `d2`, `d2` calls `d3`. -/
def d3 (p : Pos) : Bool := p.w < p.hi
def d2 (p : Pos) : Bool := p.lo < p.w && d3 p
def d1 (p : Pos) : Bool := d2 p

/-- A loop whose test is three calls deep. -/
def deepLoop : Nat → Pos → Option Nat
  | 0, _ => none
  | n + 1, p => if d1 p then deepLoop n (bumpLo p) else some p.w

/-! ## The ground truth -/

example : sumAll #[1, 2, 3] = .done 6 := by decide
example : sumLoop 0 ⟨#[1], 1, 4⟩ = .done 4 := by decide
example : walkAll 3 = some 3 := by decide
example : gapFrom 2 5 (by decide) = some 3 := by decide
/-- From `lo > hi` the gap walk gives out of fuel at each fuel. -/
example : gapWalk 9 ⟨3, 1, 0⟩ = none := by decide
/-- The fuel of `shortAll` is too small. -/
example : shortAll #[5] = .stuck := by decide
example : shortLoop 1 ⟨#[5], 0, 0⟩ = .done 5 := by decide

end DiscoverL3Toys
