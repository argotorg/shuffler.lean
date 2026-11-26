import Skel.Test.GenMultiCallee

/-! The tests of the proof of `decompiles_l2` with one lemma for each case (task MULTI-CALLEE3 (e), suite `cases`):
`lake exe skel-test --only cases`.

In the memory form with a guard, the `det` text of `decompiles_l2` has helpers (`Skel.Proof`): the invariant
`decompiles_l2_inv` and a lemma `decompiles_l2_<block>` for each block. The theorem applies `Decompiles.ofBlocks` and gives
each case its lemma. So each case has its own heartbeats.

Pure checks, on the toys `two`, `putCall` and `twice` (`Skel/Test/CallMem/Code.lean`): one lemma for each
block, and the theorem names each lemma once; the lemma of a block with a row takes the block lemma as a hypothesis; the
lines of each lemma after its block start are the lines of the case in `decompilesProof` (the text of the case is the text
of before). Negative: a function in another form (`inc`, `l2zArith`) keeps the one proof `by …` with no helpers.

Lean checks, on the toy `two` (with `put` and `inc`): the file with the case lemmas is accepted with the standard axioms,
and a case lemma is a declaration with them. With `maxHeartbeats` lowered to `low` (below the total of the cases, above each
case), the file with the case lemmas is accepted, and the file with the one proof of `decompilesProof` fails at the
heartbeat limit. (The suites `callmem` and `multicallee` check `putCall`, `two` and `twice` with the case lemmas too.) -/

namespace GenCasesTests

open Skel Skel.Gen GenMultiCalleeTests

/-- The summary, the frame text and the generated function of the toy `fn` (`Skel/Test/CallMem/Code.lean`). -/
def toyParts (fn : String) : Except GenError (Target × Summary × FrameText × Generated) := do
  let t := target fn (← callees fn)
  let (s, fr) ← summaryOf t .storeChain code .table fn
  pure (t, s, fr, ← gen fn)

/-- The lines of the case `name` in a proof of `decompilesProof`: the lines after `  | name =>` up to the next case. -/
def armLines (proof name : String) : List String :=
  let ls := proof.splitOn "\n"
  let rest := (ls.dropWhile (· != s!"  | {name} =>")).drop 1
  rest.takeWhile fun l => !l.startsWith "  | "

/-- The text of the lemma of the case `name` in the helpers `hs`: from its `theorem` line to the next blank line. -/
def lemmaText (hs name : String) : String :=
  match hs.splitOn s!"theorem {caseLemma name}" with
  | [_, rest] => (rest.splitOn "\n\n").headD ""
  | _ => ""

/-- The checks of the split of `fn`. -/
def splitChecks (fn : String) (p : Except GenError (Target × Summary × FrameText × Generated)) : List (String × Bool) :=
  match p with
  | .error _ => [(s!"{fn}: generates", false)]
  | .ok (t, s, fr, g) =>
    let d := Proof.ofText (detOf g)
    let one := decompilesProof t s fr
    let names := s.blocks.map (·.name.s)
    let rowOf (n : String) : Option Obligation := g.obligations.find? (·.origin == .block n)
    [ (s!"{fn}: one case lemma for each block ({names.length}), and the theorem names each once",
        !d.helpers.isEmpty && names.length > 0 && has d.helpers "abbrev decompiles_l2_inv" &&
          names.all fun n => (d.helpers.splitOn s!"theorem {caseLemma n} ").length == 2 &&
            (d.proof.splitOn s!"| {n} => have H := {caseLemma n} ").length == 2),
      (s!"{fn}: the lemma of a block with a row takes the block lemma; a block with no row does not",
        names.all fun n =>
          let lt := lemmaText d.helpers n
          match rowOf n with
          | some o => lt.startsWith s!" ({n} : {o.statement}) :" && has d.proof s!"H := {caseLemma n} {n} policy"
          | none => lt.startsWith " : " && has d.proof s!"H := {caseLemma n} policy"),
      (s!"{fn}: the lines of each case lemma end with the lines of its case in decompilesProof",
        names.all fun n =>
          let arm := armLines one n
          let tail := "\n".intercalate (arm.map fun l => String.ofList (l.toList.drop 2))
          !arm.isEmpty && (lemmaText d.helpers n).endsWith tail) ]

/-- The function `fn` in another form keeps one proof with no helpers. -/
def oneChecks (fn : String) (g : Except GenError Generated) : List (String × Bool) :=
  [ (s!"negative: {fn} (not the memory form with a guard) has one proof `by` with no helpers",
      match g with
      | .ok g => let d := detOf g; d.startsWith "by\n" && (Proof.ofText d).helpers.isEmpty && !has d "decompiles_l2_inv"
      | .error _ => false) ]

def pureChecks : List (String × Bool) :=
  splitChecks "two" (toyParts "two") ++
    ["putCall", "twice"].flatMap (fun fn => splitChecks fn (toyParts fn)) ++
    oneChecks "inc" (gen "inc") ++ oneChecks "l2zArith" (l2gen "l2zArith")

/-- The heartbeats of the check with the lowered limit: below the total of the cases of `two`, above each case. -/
def low : Nat := 9000

/-- The text `text` with `maxHeartbeats` lowered to `n` after the imports. -/
def lowered (n : Nat) (text : String) : String :=
  match text.splitOn "\nopen " with
  | [a, b] => a ++ s!"\n\nset_option maxHeartbeats {n}\n\nopen " ++ b
  | _ => text

/-- `g` with the `det` text of `decompiles_l2` set to `det`. -/
def withDet (g : Generated) (det : String) : Generated :=
  { g with det := g.det.map fun (i, d) => if i.name == "decompiles_l2" then (i, det) else (i, d) }

def heartbeatError : Outcome → Bool
  | .failed es => es.any fun e => has e "heartbeats"
  | _ => false

def leanChecks : IO (List (String × Bool × String)) := do
  match gen "put", gen "inc", toyParts "two" with
  | .ok p, .ok i, .ok (t, s, fr, g) =>
    let one := withDet g s!"by\n{decompilesProof t s fr}"
    let text := toyFile p i g g.modelText
    let ok ← runFile "cases-two" "MultiCall.decompiles_l2" text
    let lo ← runFile "cases-two-low" "MultiCall.decompiles_l2" (lowered low text)
    let lone ← runFile "cases-two-low-one" "MultiCall.decompiles_l2" (lowered low (toyFile p i one one.modelText))
    let caseAxioms ← runFile "cases-two-lemma" "MultiCall.decompiles_l2_entry" (text ++ "\n#print axioms MultiCall.decompiles_l2_entry\n")
    pure [ ("two: Lean accepts decompiles_l2 with the case lemmas, standard axioms", accepted ok, s!"{repr ok}"),
      ("two: the case lemma of the entry is a declaration with the standard axioms", accepted caseAxioms, s!"{repr caseAxioms}"),
      (s!"two: with maxHeartbeats {low}, Lean accepts the case lemmas", accepted lo, s!"{repr lo}"),
      (s!"two: with maxHeartbeats {low}, the one proof of decompilesProof fails at the heartbeat limit", heartbeatError lone,
        s!"{repr lone}")]
  | _, _, _ => pure [("two: generates (Lean)", false, "")]

/-- Gives the number of failed checks. The suite runs when `only` is none or `cases`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "cases" then return 0
  let mut n := 0
  for (name, ok) in pureChecks do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  cases: {name}"
  for (name, ok, msg) in ← leanChecks do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  cases: {name}\n{msg}"
  return n

end GenCasesTests
