import Skel.Types
import Skel.Discover.Lang
import Std.Data.HashMap

/-! Houdini over a list of atoms, by index set (`docs/research/invariant-discovery-design-20261119.md`, section 3.4, filter 3).
A conjunction is a set of atom indexes: a `Mask`, a natural number in which bit `i` says that atom `i` is in. The refuter gives one
verdict for a whole conjunction, and a `cti` names no atom, so a culprit is found by leaving out one atom at a time (the drop loop
of `Skel/Houdini.lean`). The atoms are not enumerated as sublists: a run asks for the conjunctions that the loop reaches, at most
`n * (n + 1) + 1` for `n` atoms. A run takes at most `maxAtoms` atoms. Pure. -/

namespace Skel.Discover.Houdini

open Skel (Verdict Cex)

/-- A set of atom indexes: bit `i` is set when atom `i` is in the set. -/
abbrev Mask := Nat

/-- The most atoms of a run. -/
def maxAtoms : Nat := 24

/-- The set of the indexes below `n`. -/
def Mask.full (n : Nat) : Mask := 2 ^ n - 1

/-- The indexes of `m` below `n`, in order. -/
def Mask.members (m : Mask) (n : Nat) : List Nat := (List.range n).filter m.testBit

/-- `m` without the index `i`. -/
def Mask.erase (m : Mask) (i : Nat) : Mask := if m.testBit i then m - 2 ^ i else m

/-- The indexes of `a` that are not in `b`. -/
def Mask.diff (a b : Mask) : Mask := a ^^^ (a &&& b)

/-- The elements of `xs` whose index is in `m`, in order. -/
def pick {α : Type} (xs : List α) (m : Mask) : List α :=
  (((List.range xs.length).zip xs).filter fun p => m.testBit p.1).map Prod.snd

/-- Whether the verdict `w` of the conjunction without an atom fixes the counterexample `c` of the conjunction: it passes, or its
first failure is at a later sample. -/
def fixes (c : Cex) : Verdict → Bool
  | .pass _ => true
  | .real d | .cti d => c.index < d.index
  | .unknown _ => false

/-- Whether a verdict is `unknown`. -/
def isUnknown : Verdict → Bool
  | .unknown _ => true
  | _ => false

/-- What the loop asks for next, given the verdicts known so far. -/
inductive Step where
  /-- the verdict of this conjunction is needed -/
  | ask (m : Mask)
  /-- this conjunction passes -/
  | pass (m : Mask)
  /-- the loop ends with no pass; the conjunction that is left -/
  | stop (m : Mask)
  /-- the loop ends with no answer: the verdict of the conjunction `s` is `unknown`; `m` is the conjunction that is left -/
  | unknown (m s : Mask)
  deriving DecidableEq, Repr

/-- The next step of the drop loop from the conjunction `m` of the `n` atoms, given the verdicts known so far (`v`). `fuel` bounds
the rounds: a round drops at least one atom. The loop gives:
* `ask m` when `v` has no verdict for `m`;
* `ask s` for the first leave-one-out set `s` of `m` with no verdict, when `v` has a `real` or `cti` for `m`;
* when `v` has a verdict for each leave-one-out set, the loop goes on with `m` minus its culprits (`fixes`);
* `pass m` for a pass of `m`;
* `stop 0` for a lone atom that fails (all atoms are dropped), and for the empty set;
* `unknown m s` for an `unknown` verdict of `m` (then `s = m`), or when `m` has a `real` or `cti`, no leave-one-out set shows a
  culprit, and the verdict of a leave-one-out set `s` is `unknown`: an `unknown` is no counterexample, so no atom is dropped for it;
* `stop m` for no culprit with no `unknown` verdict, or no fuel. -/
def step (v : Mask → Option Verdict) (n : Nat) : Nat → Mask → Step
  | 0, m => .stop m
  | fuel + 1, m =>
    if m == 0 then .stop 0 else
    match v m with
    | none => .ask m
    | some (.pass _) => .pass m
    | some (.unknown _) => .unknown m m
    | some (.real c) | some (.cti c) =>
      let ms := m.members n
      if ms.length ≤ 1 then .stop 0 else
      let without := ms.map fun i => (i, m.erase i)
      match without.find? fun (_, s) => (v s).isNone with
      | some (_, s) => .ask s
      | none =>
        match (without.filter fun (_, s) => (v s).any (fixes c)).map (·.1) with
        | [] =>
          match without.find? fun (_, s) => (v s).any isUnknown with
          | some (_, s) => .unknown m s
          | none => .stop m
        | culprits => step v n fuel (culprits.foldl Mask.erase m)

/-- The result of a run. `kept` is the conjunction that passes, and the empty set when no conjunction was shown to pass. `weak` is
the set of atoms that the loop dropped as culprits: each has a counterexample. `unknown` is the conjunction whose verdict is
`unknown` when the loop ended for it; then `kept` is empty, and the atoms that are not in `weak` are not decided. -/
structure Result where
  kept : Mask
  weak : Mask
  unknown : Option Mask := none
  deriving DecidableEq, Repr

/-- A run: its result, and the conjunctions that it asked the refuter, in order. -/
structure Run where
  result : Result
  asked : List Mask
  deriving DecidableEq, Repr

/-- At most `maxAtoms` atoms. -/
structure Pool where
  atoms : List Atom
  small : atoms.length ≤ maxAtoms

/-- The pool of the atoms, or none when there are more than `maxAtoms`. -/
def Pool.make? (ats : List Atom) : Option Pool :=
  if h : ats.length ≤ maxAtoms then some ⟨ats, h⟩ else none

/-- The most refutes of a run of `n` atoms: a round asks the set and its `n` leave-one-out sets, and there are at most `n` rounds. -/
def askBound (n : Nat) : Nat := n * (n + 1) + 1

/-- The loop: it asks the refuter for the sets that `step` names, and keeps the verdicts. `asked` is newest first. -/
private def walk (n : Nat) (refute : Mask → Verdict) : Nat → Std.HashMap Mask Verdict → List Mask → Run
  | 0, _, asked => { result := ⟨0, 0, none⟩, asked := asked.reverse }
  | fuel + 1, h, asked =>
    match step (fun m => h[m]?) n n (Mask.full n) with
    | .ask m => walk n refute fuel (h.insert m (refute m)) (m :: asked)
    | .pass m => { result := ⟨m, Mask.diff (Mask.full n) m, none⟩, asked := asked.reverse }
    | .stop m => { result := ⟨0, Mask.diff (Mask.full n) m, none⟩, asked := asked.reverse }
    | .unknown m s => { result := ⟨0, Mask.diff (Mask.full n) m, some s⟩, asked := asked.reverse }

/-- The run against the refuter `refute`, which gives the verdict of the conjunction of a list of atoms. The run asks at most
`askBound` sets. -/
def Pool.run (p : Pool) (refute : List Atom → Verdict) : Run :=
  walk p.atoms.length (fun m => refute (pick p.atoms m)) (askBound p.atoms.length) {} []

/-- The atoms that a run keeps. -/
def Pool.kept (p : Pool) (r : Result) : List Atom := pick p.atoms r.kept

/-- The atoms that a run dropped as culprits. -/
def Pool.weak (p : Pool) (r : Result) : List Atom := pick p.atoms r.weak

end Skel.Discover.Houdini
