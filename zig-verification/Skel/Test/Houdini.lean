import Skel.Houdini
import Skel.Rungs
import Skel.Toy.Sum
import Skel.Test.Loop

/-! The tests of `Skel/Houdini.lean` (suite `houdini`): `lake exe skel-test --only houdini`. Each check is a value that
must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed checks. The property
draws `max cases 200` cases: the case `i` is drawn by the generator of seed `seed + i`. -/

namespace HoudiniTests

open Skel Skel.Houdini

/-- The texts of the atoms of the fields `f`, or `[]` when the boundary parser refuses `f`. -/
def texts (f : Option Fields) : List String :=
  (f.map fun f => (atoms f).map Atom.text).getD []

/-- The fields of `toySum`: the state fields `rcx` and `rax` of words, and the L3 input `xs` a list. -/
def toySumFields : Option Fields :=
  Fields.parse? [("rcx", "word"), ("rax", "word")] [("xs", "list")]

/-- The fields with `n` word state fields `w0`, `w1`, ... and `m` list inputs `l0`, `l1`, ... -/
def gridFields (n m : Nat) : Option Fields :=
  Fields.parse? ((List.range n).map fun k => (s!"w{k}", "word"))
    ((List.range m).map fun k => (s!"l{k}", "list"))

/-- The number of atoms of the grammar for `n` word fields and `m` list inputs: one bound below `2^64` for each word,
and one length bound for each word with each list. -/
def expectedCount (n m : Nat) : Nat := n * (m + 1)

/-- Four distinct atoms for the checks of `drop`. -/
def a0 : Atom := .wordBelow ⟨"a"⟩
def a1 : Atom := .countBound ⟨"a"⟩ ⟨"xs"⟩
def a2 : Atom := .wordBelow ⟨"b"⟩
def a3 : Atom := .countBound ⟨"b"⟩ ⟨"ys"⟩

/-- The atoms of the grid of `n` words and `m` lists: no repeated text, and the count of `expectedCount`. -/
def gridHolds : Bool :=
  (List.range 4).all fun n => (List.range 4).all fun m =>
    let ts := texts (gridFields n m)
    ts.length == expectedCount n m && ts.eraseDups.length == ts.length

/-- The property of `drop`: the result is a sublist of the input, and its length is the input length minus the number
of distinct in-range indexes. -/
def dropHolds (ats : List Atom) (idx : List Nat) : Bool :=
  (drop ats idx).isSublist ats &&
    (drop ats idx).length == ats.length - (idx.filter (· < ats.length)).eraseDups.length

/-- The atoms of the pool that the generator draws from. -/
def pool : List Atom := [a0, a1, a2, a3]

/-- Draws `k` values with `f`, threading the generator. -/
def draws {α : Type} (f : StdGen → α × StdGen) : Nat → StdGen → List α × StdGen
  | 0, g => ([], g)
  | k + 1, g =>
    let (x, g) := f g
    let (xs, g) := draws f k g
    (x :: xs, g)

/-- The atom list and the index list of case `i`, drawn by the generator of seed `seed + i`. The atom list has 0 to 8
atoms; the indexes are 0 to 11, so some are out of range. -/
def caseOf (seed i : Nat) : List Atom × List Nat :=
  let g := mkStdGen (seed + i)
  let (la, g) := randNat g 0 8
  let (ats, g) := draws (fun g => let (j, g) := randNat g 0 (pool.length - 1); (pool.getD j a0, g)) la g
  let (li, g) := randNat g 0 8
  let (idx, _) := draws (fun g => randNat g 0 11) li g
  (ats, idx)

/-- The number of cases of the property that fail. -/
def propertyFailures (seed cases : Nat) : Nat :=
  ((List.range (max cases 200)).filter fun i => let (ats, idx) := caseOf seed i; !dropHolds ats idx).length

/-- The checks that hold on fixed values. -/
def fixedChecks : List (String × Bool) :=
  [ ("toySum atoms include the invariant of template T2", (texts toySumFields).contains Skel.Toy.Sum.template2.inv),
    ("toySum atoms are in the fixed order",
      texts toySumFields == ["x.rcx.toNat < 2^64", "x.rax.toNat < 2^64", "x.rcx.toNat ≤ xs.length", "x.rax.toNat ≤ xs.length"]),
    ("toySum atoms are the same in two calls", texts toySumFields == texts toySumFields),
    ("toySum atoms have no duplicates", (texts toySumFields).eraseDups.length == (texts toySumFields).length),
    ("the grid of n words and m lists has n*(m+1) atoms and no duplicates", gridHolds),
    ("empty fields give no atoms (boundary)", texts (Fields.parse? [] []) == []),
    ("conj of no atoms is True (boundary)", conj [] == "True"),
    ("conj of one atom is its text", conj [a0] == "x.a.toNat < 2^64"),
    ("conj joins two atoms with and", conj [a0, a1] == "x.a.toNat < 2^64 ∧ x.a.toNat ≤ xs.length"),
    ("a word with no list gives one atom", texts (Fields.parse? [("i", "word")] []) == ["x.i.toNat < 2^64"]),
    ("a list with no word gives no atom", texts (Fields.parse? [] [("xs", "list")]) == []),
    ("drop removes the atoms at indexes 1 and 3", drop [a0, a1, a2, a3] [1, 3] == [a0, a2]),
    ("drop with no index changes nothing", drop [a0, a1, a2, a3] [] == [a0, a1, a2, a3]),
    ("drop with one out-of-range index changes nothing", drop [a0, a1, a2, a3] [4] == [a0, a1, a2, a3]),
    ("drop with out-of-range indexes changes nothing", drop [a0, a1, a2, a3] [9, 100] == [a0, a1, a2, a3]),
    ("drop ignores the out-of-range index and removes the other", drop [a0, a1, a2, a3] [1, 9] == [a0, a2, a3]),
    ("drop with a repeated index is the same as one index",
      drop [a0, a1, a2, a3] [2, 2] == drop [a0, a1, a2, a3] [2] && drop [a0, a1, a2, a3] [2] == [a0, a1, a3]),
    ("drop does not depend on the order of the indexes", drop [a0, a1, a2, a3] [3, 1] == drop [a0, a1, a2, a3] [1, 3]),
    ("drop of all indexes gives the empty list", drop [a0, a1, a2, a3] [0, 1, 2, 3] == []),
    ("drop of an empty list gives the empty list", drop [] [0] == []),
    ("an empty name is refused", (Fields.parse? [("", "word")] []).isNone),
    ("a state name with a space is refused", (Fields.parse? [("a b", "word")] []).isNone),
    ("an input name with a space is refused", (Fields.parse? [] [("x s", "list")]).isNone),
    ("a name that starts with a digit is refused", (Fields.parse? [("1x", "word")] []).isNone),
    ("an unknown kind is refused", (Fields.parse? [("i", "int")] []).isNone),
    ("a repeated state name is refused", (Fields.parse? [("i", "word"), ("i", "word")] []).isNone),
    ("a name with a letter, a digit and an underscore is accepted", (Fields.parse? [("a_1", "word")] []).isSome) ]

/-! ## The drop loop and the rung (R-C)

The refuter is a function of the atoms of a triple. Its model of a loop: each atom has a position `p` in the atom list, and a
bad atom fails at the sample `2 * p + 1`; a conjunction with no bad atom passes, one with bad atoms is a `cti` at the least sample
of its bad atoms. So the culprit of a failing conjunction is its bad atom with the least position, and dropping it moves the
failure to a later sample. -/

/-- The spec of the fields `f` with the one tail of the tests. -/
def specOf (f : Option Fields) : Option Spec :=
  f.bind fun f => Spec.make? f [("xs.length - x.rcx.toNat", "x.rax")]

/-- The spec of `toySum`. -/
def sumSpec : Option Spec := specOf toySumFields

/-- A dummy obligation for the proposer: the proposer reads the history only. -/
def dummyOb : Obligation :=
  { id := { function := "f", name := "loop" }, cls := .refine, origin := .loop "L", statement := "", deps := [], claim := .loop }

/-- The atoms of the invariant text of a triple of the spec: the atoms of the spec whose text is a conjunct. -/
def atomsOf (spec : Spec) (t : Triple) : List Atom :=
  spec.atoms.filter fun a => (t.inv.splitOn " ∧ ").contains a.text

/-- The counterexample of a failure at the sample `index`. -/
def cexAt (index : Nat) : Cex :=
  { ob := dummyOb.id, subject := .claim, seed := 1, index := index, shown := "s", why := "leaves the invariant" }

/-- The verdict of the model above for the conjunction `s` of the atoms of `all`, when the atoms `bad` are bad. -/
def oracle (all bad s : List Atom) : Verdict :=
  match (s.filter (bad.contains ·)).map (fun a => 2 * ((all.findIdx? (· == a)).getD 0) + 1) with
  | [] => .pass 200
  | i :: is => .cti (cexAt (is.foldl min i))

/-- The history of the run of the rung against the refuter `refute`, newest first: the rung gives a triple, the refuter gives
its verdict, until the rung gives none, a triple passes (the loop checks it then), or the fuel ends. -/
def simulate (spec : Spec) (refute : Triple → Verdict) : Nat → List Attempt → List Attempt
  | 0, atts => atts
  | n + 1, atts =>
    if atts.any (fun a => match a.result with | .refuted (.pass _) => true | _ => false) then atts
    else
      match houdiniRung spec dummyOb ⟨atts, []⟩ with
      | none => atts
      | some t => simulate spec refute n ({ candidate := .triple .houdini t, result := .refuted (refute t), ms := 0 } :: atts)

/-- The run of the rung against the model with the bad atoms `bad`. -/
def runBad (spec : Spec) (bad : List Atom) : List Attempt :=
  simulate spec (fun t => oracle spec.atoms bad (atomsOf spec t)) 200 []

/-- The triples of the attempts, oldest first. -/
def triplesOf (atts : List Attempt) : List Triple :=
  atts.reverse.filterMap fun a => match a.candidate with | .triple _ t => some t | _ => none

/-- The triple of the pass of the attempts, if there is one. -/
def passOf (atts : List Attempt) : Option Triple :=
  atts.findSome? fun a => match a.candidate, a.result with | .triple _ t, .refuted (.pass _) => some t | _, _ => none

/-- The case of the property of the rung: the atoms of a grid of at most 8 atoms, and a subset of them as bad. The case `i` is
drawn from the seed `seed + i`. -/
def rungCase (seed i : Nat) : Option (Spec × List Atom) :=
  let g := mkStdGen (seed + i)
  let (n, g) := randNat g 1 4
  let (m, g) := randNat g 0 1
  (specOf (gridFields n m)).map fun sp =>
    let (picked, _) := draws (fun g => randNat g 0 1) sp.atoms.length g
    (sp, (sp.atoms.zip picked).filterMap fun (a, b) => if b == 1 then some a else none)

/-- Whether the run of a case ends as the model says: with bad atoms and a good rest, the first pass is the conjunction of the
good atoms; with no good atom, no pass. No triple repeats, no triple has the empty conjunction, and the number of probes is at
most `n * (n + 1) + 1`. -/
def rungCaseOk (seed i : Nat) : Bool :=
  match rungCase seed i with
  | none => false
  | some (sp, bad) =>
    let atts := runBad sp bad
    let ts := triplesOf atts
    let good := sp.atoms.filter (!bad.contains ·)
    let n := sp.atoms.length
    let passOk :=
      if good.isEmpty then (passOf atts).isNone
      else (passOf atts).map (·.inv) == some (conj good)
    passOk && ts.eraseDups.length == ts.length && ts.all (·.inv != "True") && ts.length ≤ n * (n + 1) + 1

/-- The number of cases of the property of the rung that fail. -/
def rungFailures (seed cases : Nat) : Nat :=
  ((List.range (max cases 200)).filter fun i => !rungCaseOk seed i).length

/-- The bad atom of `toySum`: the count of the sum is not below the length of the list. -/
def sumBad : List Atom := [.countBound ⟨"rax"⟩ ⟨"xs"⟩]

/-- The triple that the loop row closes with in the run of `lad` against the fake `fk`: `none` when the row is not closed,
else the triple of its closure (`some none` for a closure with no triple). -/
def closedTriple (lad : Ladders) (fk : LoopTests.Fake) : Option (Option (InvRung × Triple)) :=
  (LoopTests.runOn lad fk LoopTests.tableObs).bind fun r =>
    match LoopTests.statusOf r.final "loop" with
    | some (.closed c) => some c.triple
    | _ => none

/-- The fake that accepts each check and gives the refute verdict of the model above, with the bad atoms `bad`; a triple of
`early` (a template) is a `cti` at the sample 0. -/
def fakeBad (spec : Spec) (bad : List Atom) (early : List Triple := []) : LoopTests.Fake :=
  { LoopTests.allAccepted with
    refute := fun p =>
      match p.candidate with
      | .triple _ t =>
        if early.contains t then .cti (LoopTests.cexOf p) else
          match oracle spec.atoms bad (atomsOf spec t) with
          | .cti c => .cti { c with ob := p.ob, subject := .triple t }
          | v => v
      | _ => .pass 200 }

/-- The ladders of the tests: the templates `ts` and the Houdini rung of `spec` (`LoopTests.lad` has no Houdini rung). -/
def ladWith (ts : List Triple) (spec : Spec) : Ladders :=
  ladders ts LoopTests.noTexts [] [] [] LoopTests.handTriple (some spec)

/-- The triples of the refute actions of the loop row of the run. -/
def refutedIn (lad : Ladders) (fk : LoopTests.Fake) : List Triple :=
  ((LoopTests.runOn lad fk LoopTests.tableObs).map LoopTests.loopRefuted).getD []

/-- Whether the loop row of the run is open. -/
def loopOpen (lad : Ladders) (fk : LoopTests.Fake) : Bool :=
  match (LoopTests.runOn lad fk LoopTests.tableObs).bind fun r => LoopTests.statusOf r.final "loop" with
  | some (.«open» _) => true
  | _ => false

/-- The number of asks of the loop row of the run. -/
def loopAskCount (lad : Ladders) (fk : LoopTests.Fake) : Option Nat :=
  (LoopTests.runOn lad fk LoopTests.tableObs).map fun r => (LoopTests.loopAsks r).length

/-- The checks of the drop loop and of the rung, with the fields of `toySum`. -/
def rungChecks : List (String × Bool) :=
  match sumSpec with
  | none => [("the spec of toySum is made", false)]
  | some sp =>
    let all := sp.atoms
    let a3 := Atom.countBound ⟨"rcx"⟩ ⟨"xs"⟩
    let tripleOf (s : List Atom) : Triple := { inv := conj s, measure := "xs.length - x.rcx.toNat", result := "x.rax" }
    -- the recorded verdicts: the full conjunction and the four leave-one-out conjunctions
    let recorded : List (List Atom × Verdict) :=
      (all :: (List.range all.length).map fun i => drop all [i]).map fun s => (s, oracle all sumBad s)
    let lookup (s : List Atom) : Option Verdict := (recorded.find? (·.1 == s)).map (·.2)
    let nothing : List Atom → Option Verdict := fun _ => none
    let tpl := Skel.Toy.Sum.templateTriples
    [ ("the loop on no verdict asks the full conjunction", next nothing all.length all == some all),
      ("the loop on the verdict of the full conjunction asks the first leave-one-out",
        next (fun s => if s == all then lookup s else none) all.length all == some (drop all [0])),
      ("the loop on the recorded verdicts ends: the culprit is dropped and the rest passes",
        next lookup all.length all == none && lookup (drop all [3]) == some (.pass 200)),
      ("a pass ends the loop", next (fun _ => some (.pass 200)) all.length all == none),
      ("an unknown verdict ends the loop", next (fun _ => some (.unknown "timeout")) all.length all == none),
      ("no atoms: the loop ends", next nothing 3 [] == none),
      ("no fuel: the loop ends", next nothing 0 all == none),
      ("a lone atom that fails: all atoms are dropped, no triple", next (fun _ => some (.cti (cexAt 3))) 1 [a3] == none),
      ("a lone atom with no verdict is asked", next nothing 1 [a3] == some [a3]),
      ("two atoms that fail at one sample: no culprit, the loop ends",
        next (fun _ => some (.cti (cexAt 5))) 2 [a3, .wordBelow ⟨"rcx"⟩] == none),
      ("only the atom whose removal moves the failure to a later sample is a culprit: the loop goes on without it",
        let abcd := [Atom.wordBelow ⟨"a"⟩, .wordBelow ⟨"b"⟩, .wordBelow ⟨"c"⟩, .wordBelow ⟨"d"⟩]
        let v (s : List Atom) : Option Verdict :=
          if s == drop abcd [1] then some (.cti (cexAt 9))
          else if (List.range 4).any (fun i => s == drop abcd [i]) || s == abcd then some (.cti (cexAt 5)) else none
        next v 4 abcd == some (drop (drop abcd [1]) [0])),
      ("an atom whose removal fails at an earlier sample is not a culprit",
        let abc := [Atom.wordBelow ⟨"a"⟩, .wordBelow ⟨"b"⟩, .wordBelow ⟨"c"⟩]
        next (fun s => if s == abc then some (.cti (cexAt 5)) else some (.cti (cexAt 2))) 3 abc == none),
      ("toySum: the rung asks the full conjunction first", houdiniRung sp dummyOb ⟨[], []⟩ == some (tripleOf all)),
      ("toySum: the first pass is the conjunction without the bad atom",
        (passOf (runBad sp sumBad)).map (·.inv) == some (conj (drop all [3]))),
      ("toySum: five probes, the full conjunction and the four leave-one-out", (triplesOf (runBad sp sumBad)).length == 5),
      ("toySum with no bad atom: the first probe passes and is the last", (triplesOf (runBad sp [])).length == 1),
      ("toySum with all atoms bad: no pass, and the rung ends with no triple",
        (passOf (runBad sp all)).isNone && (houdiniRung sp dummyOb ⟨runBad sp all, []⟩).isNone),
      ("a spec with no tail: the rung gives nothing",
        ((Fields.parse? [("rcx", "word")] [("xs", "list")]).bind fun f => Spec.make? f []).all fun s =>
          (houdiniRung s dummyOb ⟨[], []⟩).isNone),
      ("the rung goes to the next tail when the first tail ends",
        match (Fields.parse? [("rcx", "word")] [("xs", "list")]).bind fun f => Spec.make? f [("m1", "r1"), ("m2", "r2")] with
        | some s2 =>
          let atts := simulate s2 (fun t => if t.measure == "m1" then .cti (cexAt 1) else .pass 200) 50 []
          (triplesOf atts).map (·.measure) == ["m1", "m1", "m1", "m2"] && (passOf atts).map (·.measure) == some "m2"
        | none => false),
      ("a spec of more than maxAtoms atoms is refused", (specOf (gridFields 3 3)).isNone),
      ("a spec of maxAtoms atoms is made", (specOf (gridFields 4 1)).isSome),
      ("the candidates of toySum are the 15 non-empty conjunctions", sp.candidates.length == 15),
      ("the candidates have no repeat and no empty conjunction",
        sp.candidates.eraseDups.length == sp.candidates.length && sp.candidates.all (·.inv != "True")),
      ("the candidates hold each triple of the run of the model", (triplesOf (runBad sp sumBad)).all sp.candidates.contains),
      ("the ladder with a spec has the rungs template, houdini, model, replay",
        (ladWith [] sp).triple.map (·.1) == ([.template, .houdini, .model, .replay] : List InvRung)),
      ("the ladder with no spec has no Houdini rung",
        (ladders [] LoopTests.noTexts [] [] [] LoopTests.handTriple).triple.map (·.1) ==
          ([.template, .model, .replay] : List InvRung)),
      ("templates off: the loop row closes with the Houdini triple without the bad atom",
        closedTriple (ladWith [] sp) (fakeBad sp sumBad) == some (some (.houdini, tripleOf (drop all [3])))),
      ("templates on, T2 passes: the loop row closes on the template rung and no Houdini triple is refuted",
        closedTriple (ladWith tpl sp) (fakeBad sp sumBad (tpl.take 1)) == some (some (.template, Skel.Toy.Sum.template2)) &&
          (refutedIn (ladWith tpl sp) (fakeBad sp sumBad (tpl.take 1))).length == 2),
      ("templates off, all atoms bad: the loop row is open, with no closing triple",
        loopOpen (ladWith [] sp) (fakeBad sp all) && closedTriple (ladWith [] sp) (fakeBad sp all) == none),
      ("templates off, all atoms bad: the model rung asks 4 times after the Houdini rung",
        loopAskCount (ladWith [] sp) (fakeBad sp all) == some 4),
      ("templates off, all atoms bad: no refuted triple has an empty conjunction",
        !(refutedIn (ladWith [] sp) (fakeBad sp all)).any (·.inv == "True")) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `houdini`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "houdini" then return 0
  let mut failed := 0
  for (name, ok) in fixedChecks ++ rungChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  houdini: {name}"
  let bad := propertyFailures seed cases
  if bad > 0 then
    failed := failed + 1
    IO.println s!"FAIL  houdini: drop is a sublist with the right length ({bad} of {max cases 200} cases fail)"
  let badRung := rungFailures seed cases
  if badRung > 0 then
    failed := failed + 1
    IO.println s!"FAIL  houdini: the rung on a random model ({badRung} of {max cases 200} cases fail)"
  return failed

end HoudiniTests
