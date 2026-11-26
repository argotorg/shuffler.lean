import Std.Data.HashSet
import Skel.Discover.Trace

/-! The dynamic passes of the invariant discovery (`docs/research/invariant-discovery-design-20261119.md`, section 3.3 (a)
and section 5, task D5). Each pass is a pure function of a feature pool and a trace.

The feature pool is a list of features. The visit `v` gives the value of a feature of the pool at its position in
`v.features`. A constant, a sum, a truncated difference and a scaling have their value from their parts. Any other
feature has no value on a trace.

- The Daikon pass (`daikon`) keeps the candidate atoms that have the truth `true` at every visit. The trace must have a
  visit. The caller gives the atom pool of the trace: the visit `v` has the truth of the atom at a position of the pool at
  the same position of `v.atoms` (the trace runner evaluates every atom on the state and on the entry state). An atom of
  the pool has that truth, quantified and frame atoms included. An atom that is not in the pool, or a visit with no truth
  at its position (a trace of the old form), has the truth of the feature values for `le`, `lt` and `eq`, and no truth
  for any other atom. A candidate with no truth at some visit is dropped.
- The DIG pass (`dig`) keeps the candidate measures that fall at every step. A step is a pair of consecutive visits of one
  run. A measure falls at a step when its tuple of values, in lexicographic order, is smaller at the second visit. Each
  kept measure gets the number of distinct steps that it explains: the steps where its first component falls strictly.
  The result is sorted by that number, most first; equal numbers keep the order of the candidates.
- The bound pass (`bounds`) keeps the bounds that hold at the first visit of every run: `μ ≤ fuel` for the fuel of each
  run, and `μ ≤ k` for each constant `k`. `μ` is the first component of the measure. The caller gives the fuel of each
  run, because a trace does not carry it.

The candidates come from the caller. A trace has the features as naturals, so every value is non-negative. -/

namespace Skel.Discover

open Std

/-- The value of a feature at a visit. A feature of the pool has the entry of `v.features` at its position in the pool.
A constant, a sum, a truncated difference and a scaling have the values of their parts; other features have none. -/
def valueAt (pool : List Feature) (v : Visit) (f : Feature) : Option Nat :=
  match pool.idxOf? f with
  | some i => v.features[i]?
  | none =>
    match f with
    | .const n => some n
    | .add a b => (· + ·) <$> valueAt pool v a <*> valueAt pool v b
    | .sub a b => (· - ·) <$> valueAt pool v a <*> valueAt pool v b
    | .scale k a => (k * ·) <$> valueAt pool v a
    | _ => none

/-- The truth of an atom at a visit from the feature values: the relations `≤`, `<` and `=` of two values have one. Any
other atom needs the state, so it has none. -/
def relTruth (pool : List Feature) (v : Visit) : Atom → Option Bool
  | .le a b => (fun x y => decide (x ≤ y)) <$> valueAt pool v a <*> valueAt pool v b
  | .lt a b => (fun x y => decide (x < y)) <$> valueAt pool v a <*> valueAt pool v b
  | .eq a b => (fun x y => decide (x = y)) <$> valueAt pool v a <*> valueAt pool v b
  | _ => none

/-- The truth of an atom at a visit, when the trace gives one: the truth that the visit records for an atom of the atom
pool `apool`, else the truth of the feature values (see `relTruth`). -/
def truthAt (pool : List Feature) (apool : List Atom) (v : Visit) (a : Atom) : Option Bool :=
  match apool.idxOf? a with
  | some i => (v.atoms[i]?).orElse fun _ => relTruth pool v a
  | none => relTruth pool v a

/-- The atoms of `cands` that are true at every visit of the trace `t`, with the atom pool `apool` of the trace. A trace
with no visit keeps none. -/
def daikon (pool : List Feature) (apool : List Atom) (cands : List Atom) (t : Trace) : List Atom :=
  cands.filter fun a => !t.isEmpty && t.all fun v => truthAt pool apool v a == some true

/-- The components of a measure, as features. -/
def Measure.components : Measure → List Feature
  | .one a => [a]
  | .two a b => [a, b]
  | .three a b c => [a, b, c]

/-- The lexicographic order of two tuples of values. -/
def lexLt : List Nat → List Nat → Bool
  | [], _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x < y) || (x == y && lexLt xs ys)

/-- The consecutive visits of the trace: the pairs of visits `j` and `j + 1` of one run. -/
def steps (t : Trace) : List (Visit × Visit) :=
  (t.zip t.tail).filter fun (x, y) => x.seed == y.seed && x.index == y.index && y.visit == x.visit + 1

/-- The tuple of the values of a measure at a visit, when each component has a value. -/
def measureAt (pool : List Feature) (v : Visit) (m : Measure) : Option (List Nat) :=
  m.components.mapM (valueAt pool v)

/-- Whether the measure falls at the step: its tuple at the second visit is less than at the first. -/
def falls (pool : List Feature) (m : Measure) (xy : Visit × Visit) : Option Bool :=
  (fun vx vy => lexLt vy vx) <$> measureAt pool xy.1 m <*> measureAt pool xy.2 m

/-- The number of distinct steps where the first component of the measure falls strictly. Two steps are the same when
their two feature vectors are equal. -/
def explained (pool : List Feature) (m : Measure) (t : Trace) : Nat :=
  let keys : HashSet (List Nat × List Nat) :=
    (steps t).foldl (init := ∅) fun s xy =>
      match valueAt pool xy.1 m.first, valueAt pool xy.2 m.first with
      | some x, some y => if y < x then s.insert (xy.1.features, xy.2.features) else s
      | _, _ => s
  keys.size

/-- The measures of `cands` that fall at every step of the trace, with the number of steps that each explains. A trace
with no step keeps none. The result is sorted by the number of steps, most first; equal numbers keep the order of
`cands`. -/
def dig (pool : List Feature) (cands : List Measure) (t : Trace) : List (Measure × Nat) :=
  let ss := steps t
  let kept := cands.filter fun m => !ss.isEmpty && ss.all fun xy => falls pool m xy == some true
  (kept.map fun m => (m, explained pool m t)).mergeSort fun a b => decide (a.2 ≥ b.2)

/-- The most features that the linear measures use. -/
def maxLinFeatures : Nat := 8

/-- The most linear measures of any pool. -/
def maxLinearMeasures : Nat := 9 * (maxLinFeatures * (maxLinFeatures - 1) / 2)

/-- The coefficients of a linear measure. -/
def linCoefs : List Int := [-2, -1, 1, 2]

/-- The linear measures of a pool: for each pair of the first `maxLinFeatures` distinct features, the combinations `c * f + d * g`
with `c` and `d` in `linCoefs`, a positive one of them (else the value is zero), and not both of size 2 (a multiple of a smaller
one). The constant is 1: the zero case of the goals of a fueled loop needs a measure of at least 1 at each state of the
invariant (the steps that are left, with the exit), and a measure that falls still falls with 1 added. That is 9 for a pair, so
at most `maxLinearMeasures`. The value of a measure is the sum over `Int`, cut at zero. -/
def linearMeasures (pool : List Feature) : List Measure :=
  let fs := pool.eraseDups.take maxLinFeatures
  (fs.zipIdx.flatMap fun (f, i) => (fs.drop (i + 1)).map fun g => (f, g)).flatMap fun (f, g) =>
    linCoefs.flatMap fun c => linCoefs.filterMap fun d =>
      if (0 < c || 0 < d) && !(c.natAbs == 2 && d.natAbs == 2) then
        some (Measure.one ({ terms := [(c, f), (d, g)], const := 1 } : Lin).toFeature)
      else none

/-- The bounds that hold at the first visit of every run. `fuelOf` gives the fuel of the run of a visit. The bound `fuel`
is kept when the first component of `m` is at most that fuel at every first visit; the bound `const k` is kept when it
is at most `k` at every first visit. A trace with no first visit keeps none. -/
def bounds (pool : List Feature) (fuelOf : Visit → Nat) (consts : List Nat) (m : Measure) (t : Trace) : List Bound :=
  let firsts := t.filter (·.visit == 0)
  let holds (limit : Visit → Nat) : Bool :=
    !firsts.isEmpty && firsts.all fun v => (valueAt pool v m.first).any (· ≤ limit v)
  (if holds fuelOf then [Bound.fuel] else []) ++ (consts.filter fun k => holds fun _ => k).map Bound.const

end Skel.Discover
