import Skel.Discover.Houdini
import Skel.Test.Houdini

/-! The tests of `Skel/Discover/Houdini.lean` (suite `discoverhoudini`): `lake exe skel-test --only discoverhoudini`.
Each check is a value that must hold. A check that does not hold prints one `FAIL` line. The refuter of the tests is a model:
each atom has a position `p` in the pool, and a bad atom fails at the sample `2 * p + 1`; a conjunction with no bad atom passes,
and one with bad atoms is a `cti` at the least sample of its bad atoms. The property draws `max cases 200` cases: the case `i` is
drawn by the generator of seed `seed + i`. The suite gives the number of failed checks. -/

namespace DiscoverHoudiniTests

open Skel Skel.Discover Skel.Discover.Houdini

/-- The atom `i` of a test pool: distinct for distinct `i`. -/
def atomN (i : Nat) : Atom := .frameEq [s!"f{i}"]

/-- The pool atoms `0` to `n - 1`. -/
def atomsN (n : Nat) : List Atom := (List.range n).map atomN

/-- The verdict of the model for the conjunction `s` of the atoms of `all`, when the atoms `bad` are bad. -/
def oracle (all bad s : List Atom) : Verdict :=
  match (s.filter (bad.contains ·)).map (fun a => 2 * ((all.findIdx? (· == a)).getD 0) + 1) with
  | [] => .pass 200
  | i :: is => .cti (HoudiniTests.cexAt (is.foldl min i))

/-- The run of the pool of `n` atoms against the model whose bad atoms have the indexes `badIdx`. -/
def runBad (n : Nat) (badIdx : List Nat) : Option (Pool × Run) :=
  (Pool.make? (atomsN n)).map fun p =>
    (p, p.run (oracle p.atoms (badIdx.filterMap (p.atoms[·]?))))

/-- Whether a verdict is a pass. -/
def isPass : Verdict → Bool
  | .pass _ => true
  | _ => false

/-- The case of the property: the size `n` of the pool (0 to 24), and the bad indexes (each index is bad with chance 1/3). -/
def caseOf (seed i : Nat) : Nat × List Nat :=
  let g := mkStdGen (seed + i)
  let (n, g) := randNat g 0 24
  let (picked, _) := HoudiniTests.draws (fun g => randNat g 0 2) n g
  (n, (List.range n).filter fun j => picked.getD j 1 == 0)

/-- Whether a run of the case ends as the model says. The kept atoms are a sublist of the pool, they pass the model, they are the
good atoms; the weak atoms are the bad atoms; no conjunction is asked twice, none is empty, each is inside the pool, and the number
of asks is within the bound. -/
def caseOk (seed i : Nat) : Bool :=
  let (n, badIdx) := caseOf seed i
  match runBad n badIdx with
  | none => false
  | some (p, r) =>
    let all := p.atoms
    let bad := badIdx.filterMap (all[·]?)
    let kept := p.kept r.result
    kept.isSublist all && isPass (oracle all bad kept) &&
      kept == all.filter (!bad.contains ·) && p.weak r.result == bad &&
      r.asked.eraseDups.length == r.asked.length && r.asked.all (fun m => m != 0 && m ≤ Mask.full n) &&
      r.asked.length ≤ askBound n && (n == 0 || r.asked.length ≥ 1)

/-- The number of cases of the property that fail. -/
def propertyFailures (seed cases : Nat) : Nat :=
  ((List.range (max cases 200)).filter fun i => !caseOk seed i).length

/-- The refute count of the run of 24 atoms with the one culprit `c`, or none. -/
def oneCulprit (c : Nat) : Option Nat := (runBad 24 [c]).map (·.2.asked.length)

/-- Whether the run of 24 atoms with the one culprit `c` keeps all atoms but `c` and drops `c`. -/
def oneCulpritKept (c : Nat) : Bool :=
  match runBad 24 [c] with
  | none => false
  | some (p, r) =>
    p.kept r.result == (atomsN 24).eraseIdx c && p.weak r.result == [atomN c]

/-- The model for a pool in which each non-empty conjunction fails at the sample 5. -/
def refuteAll (s : List Atom) : Verdict := if s.isEmpty then .pass 1 else .cti (HoudiniTests.cexAt 5)

/-- The run of 24 atoms against a refuter `f`. -/
def runWith (n : Nat) (f : List Atom → Verdict) : Option (Pool × Run) :=
  (Pool.make? (atomsN n)).map fun p => (p, p.run f)

/-- The first step of the loop for 4 atoms with no verdict known. -/
def nothing : Mask → Option Verdict := fun _ => none

def fixedChecks : List (String × Bool) :=
  [ ("full of 4 is 15", Mask.full 4 == 15),
    ("full of 0 is the empty set", Mask.full 0 == 0),
    ("members of 10 below 4 are 1 and 3", Mask.members 10 4 == [1, 3]),
    ("members ignores the indexes from n on", Mask.members 26 4 == [1, 3]),
    ("erase removes a member", Mask.erase 15 1 == 13),
    ("erase of a non-member changes nothing", Mask.erase 13 1 == 13),
    ("diff gives the indexes of a that are not in b", Mask.diff 15 5 == 10),
    ("diff of a set and itself is empty", Mask.diff 21 21 == 0),
    ("pick takes the elements at the members", pick ["a", "b", "c", "d"] 10 == ["b", "d"]),
    ("pick ignores a member out of range", pick ["a", "b"] 12 == []),
    ("pick of the full set is the list", pick ["a", "b", "c"] 7 == ["a", "b", "c"]),
    ("pick of the empty set is empty", pick ["a", "b", "c"] 0 == []),
    ("a pool of 24 atoms is made", (Pool.make? (atomsN 24)).isSome),
    ("a pool of 25 atoms is refused", (Pool.make? (atomsN 25)).isNone),
    ("a pool of no atom is made", (Pool.make? []).isSome),
    ("step with no verdict asks the full set", step nothing 4 4 15 == .ask 15),
    ("step with the verdict of the full set asks the first leave-one-out",
      step (fun m => if m == 15 then some (.cti (HoudiniTests.cexAt 1)) else none) 4 4 15 == .ask 14),
    ("step of a pass is a pass", step (fun _ => some (.pass 1)) 4 4 15 == .pass 15),
    ("step of an unknown verdict ends with the unknown set (REFUTE-COV: no atom is dropped for it)",
      step (fun _ => some (.unknown "timeout")) 4 4 15 == .unknown 15 15),
    ("step of the empty set stops with the empty set", step nothing 4 4 0 == .stop 0),
    ("step with no fuel stops", step nothing 4 0 15 == .stop 15),
    ("step of a lone atom that fails drops it", step (fun _ => some (.cti (HoudiniTests.cexAt 3))) 4 1 1 == .stop 0),
    ("step of a lone atom with no verdict asks it", step nothing 4 1 4 == .ask 4),
    ("step with no culprit stops", step (fun _ => some (.cti (HoudiniTests.cexAt 5))) 2 2 3 == .stop 3),
    ("step of a real verdict is read as a cti",
      step (fun m => if m == 3 then some (.real (HoudiniTests.cexAt 1)) else none) 2 2 3 == .ask 2),
    ("24 atoms, no culprit: one refute and all atoms kept",
      (runBad 24 []).map (fun (p, r) => (r.asked.length, p.kept r.result == atomsN 24)) == some (1, true)),
    ("24 atoms, one culprit at each position: at most 25 refutes",
      (List.range 24).all fun c => (oneCulprit c).any (· ≤ 25)),
    ("24 atoms, one culprit at each position: the kept atoms are the others", (List.range 24).all oneCulpritKept),
    ("24 atoms, the culprit at the end: exactly 25 refutes", oneCulprit 23 == some 25),
    ("24 atoms, all bad: no atom is kept, no error",
      (runBad 24 (List.range 24)).map (fun (p, r) => (p.kept r.result, (p.weak r.result).length)) == some ([], 24)),
    ("24 atoms, two culprits: the others are kept",
      (runBad 24 [3, 17]).map (fun (p, r) => p.kept r.result == (atomsN 24).filter (fun a => a != atomN 3 && a != atomN 17)) ==
        some true),
    ("a refuter that refutes every candidate gives the empty set",
      (runWith 24 refuteAll).map (fun (p, r) => (p.kept r.result, r.result.kept)) == some ([], 0)),
    ("a refuter that refutes every candidate: at most 25 refutes",
      (runWith 24 refuteAll).any fun (_, r) => r.asked.length ≤ 25),
    ("a refuter of `real` verdicts for every candidate gives the empty set",
      (runWith 24 fun s => if s.isEmpty then .pass 1 else .real (HoudiniTests.cexAt 5)).map
        (fun (p, r) => p.kept r.result) == some []),
    ("a refuter of `unknown` verdicts gives the empty set after one refute",
      (runWith 24 fun _ => .unknown "timeout").map (fun (p, r) => (p.kept r.result, r.asked.length)) == some ([], 1)),
    ("a pool of no atom: the empty set and no refute",
      (runWith 0 refuteAll).map (fun (p, r) => (p.kept r.result, r.asked.length)) == some ([], 0)),
    ("a pool of one bad atom: the empty set",
      (runBad 1 [0]).map (fun (p, r) => (p.kept r.result, (p.weak r.result))) == some ([], [atomN 0])) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverhoudini`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverhoudini" then return 0
  let mut failed := 0
  for (name, ok) in fixedChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverhoudini: {name}"
  let bad := propertyFailures seed cases
  if bad > 0 then
    failed := failed + 1
    IO.println s!"FAIL  discoverhoudini: the run on a random model ({bad} of {max cases 200} cases fail)"
  return failed

end DiscoverHoudiniTests
