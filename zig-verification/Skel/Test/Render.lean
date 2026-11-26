import Skel.Render

/-! The tests of `Skel/Render.lean` (suite `render`): `lake exe skel-test --only render`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed checks. -/

namespace RenderTests

open Skel

/-- The obligation `name : 1 + 1 = 2` of the unit `Sum`, with no deps and no claim. -/
def oneTwo (name : String) : Obligation :=
  { id := { function := "Sum", name := name }, cls := .total, origin := .unit,
    statement := "1 + 1 = 2", deps := [], claim := .none }

/-- A header with the namespace `Skel.Gen.Sum` and the open `Lift.Sem`. -/
def header (imports : List String) : Header :=
  { imports := imports, namespace_ := "Skel.Gen.Sum", opens := ["Lift.Sem"] }

/-- The text of the check file of `oneTwo name` with `by rfl`, the given imports, model and answers. -/
def fileOf (imports : List String) (model : String) (answers : List String) (name : String) : String :=
  checkFile (header imports) model answers (oneTwo name) "by rfl"

/-- The lines of a text. -/
def lines (s : String) : List String := s.splitOn "\n"

/-- The lines of a text that start with `#print axioms`. -/
def printAxiomLines (s : String) : List String :=
  (lines s).filter (·.startsWith "#print axioms")

/-- The loop statement of `toySum`, as text. -/
def loopSt : String :=
  "∀ (xs : List (BitVec 64)) (a : In2p), SimArr xs a → blocksP.Returns noCall .LBB1_1 (init a) (UInt64.ofBitVec xs.sum)"

/-- Whether `s` has `sub` as a substring. -/
def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The number of the non-overlapping occurrences of `sub` in `s`. -/
def count (s sub : String) : Nat := (s.splitOn sub).length - 1

/-- The length of the text before the first occurrence of `sub` in `s`; `none` when there is none. -/
def posOf (s sub : String) : Option Nat :=
  match s.splitOn sub with
  | a :: _ :: _ => some a.length
  | _ => none

/-- The triple of the slots `i0`, `m0`, `r0`. -/
def tri : Triple := { inv := "i0", measure := "m0", result := "r0" }

/-- The checks of the render functions, each with its name. -/
def checks : List (String × Bool) :=
  [ ("resource options apply to the theorem command",
      theoremText "t" "True" "set_option maxHeartbeats 400000 in\nby trivial" ==
        "set_option maxHeartbeats 400000 in\ntheorem t : True := by trivial"),
    ("resource options stay inside a dotted theorem namespace",
      theoremText "F.t" "True" "set_option maxHeartbeats 300000 in\nset_option maxRecDepth 2000 in\nby trivial" ==
        "namespace F\nset_option maxHeartbeats 300000 in\nset_option maxRecDepth 2000 in\ntheorem t : True := by trivial\nend F"),
    ("resource options apply to the helper implementation, with the statement fixed outside",
      let proof := Proof.text { helpers := "theorem helper : True := trivial", proof := "set_option maxHeartbeats 400000 in\nby exact helper" }
      let text := theoremText "F.t" "True" proof
      has text "def t.skel_statement : Prop := True" &&
        has text "set_option maxHeartbeats 400000 in\ntheorem t : True := by exact helper"),
    ("invalid and unrelated options are not moved to command scope",
      ["maxHeartbeats 0", "maxHeartbeats 400001", "maxRecDepth 0", "debug.skipKernelTC true"].all fun option =>
        let proof := s!"set_option {option} in\nby trivial"
        theoremText "t" "True" proof == s!"theorem t : True := {proof}"),
    ("helper names include namespaces and ignore comments and strings",
      Source.declarationNames "namespace A\nsection\ntheorem saved : True := trivial\nend\nend A\n-- theorem wrong : True\ndef msg := \"theorem ignored\"\n" == ["A.saved", "msg"]),
    ("check file has the import line of each module",
      (lines (fileOf ["Lift.Sem.Sim", "Lift.Spike.Sites"] "" [] "t")).contains "import Lift.Sem.Sim"
        && (lines (fileOf ["Lift.Sem.Sim", "Lift.Spike.Sites"] "" [] "t")).contains "import Lift.Spike.Sites"),
    ("check file has one #print axioms line",
      (printAxiomLines (fileOf ["Lift.Sem.Sim"] "" [] "t")).length == 1),
    ("the #print axioms line has the theorem name",
      printAxiomLines (fileOf ["Lift.Sem.Sim"] "" [] "t") == ["#print axioms t"]),
    ("a dotted name is written in its namespace",
      let out := fileOf [] "" [] "Sites.Sum.entry"
      (lines out).contains "namespace Sites.Sum" && (lines out).contains "theorem entry : 1 + 1 = 2 := by rfl"
        && (lines out).contains "end Sites.Sum"),
    ("a dotted name has its full name in #print axioms",
      printAxiomLines (fileOf [] "" [] "Sites.Sum.entry") == ["#print axioms Sites.Sum.entry"]),
    ("no imports and no answers: no import line",
      (lines (fileOf [] "" [] "t")).all (!·.startsWith "import")),
    ("no imports and no answers: still one #print axioms line",
      printAxiomLines (fileOf [] "" [] "t") == ["#print axioms t"]),
    ("the whole check file text",
      checkFile (header ["X.Y"]) "def m := 1" ["theorem a : True := trivial"] (oneTwo "t") "by rfl" ==
        "import X.Y\nnamespace Skel.Gen.Sum\nopen Lift.Sem\ndef m := 1\ntheorem a : True := trivial\n" ++
        "theorem t : 1 + 1 = 2 := by rfl\n#print axioms t\nend Skel.Gen.Sum\n"),
    -- the introduction of the binders of a statement
    ("introNames of a statement with two binders", introNames loopSt == ["xs", "a"]),
    ("introNames of a statement without a binder is empty", introNames "P → Q" == []),
    ("introNames of a statement with a comma inside a binder",
      introNames "∀ (f : ∀ x, P x) {a : A} [Foo A], Q" == ["f", "a", "_"]),
    ("introNames of an unbracketed binder is empty (not supported)", introNames "∀ x, P x" == []),
    -- the proof text of a loop row
    ("loopProof is the whole text",
      loopProof loopSt tri ==
        "by\n  intro xs a\n  intros\n  split_hyps\n  lift_loop! (fun x => x.input = a ∧ (i0)) (fun x => (m0)) (fun x => (r0))"),
    ("loopProof of a statement without binders has no intro line",
      loopProof "P" tri ==
        "by\n  intros\n  split_hyps\n  lift_loop! (fun x => x.input = a ∧ (i0)) (fun x => (m0)) (fun x => (r0))"),
    ("loopProof of an empty invariant (boundary)", has (loopProof loopSt { tri with inv := "" }) "x.input = a ∧ ())"),
    ("loopProof keeps a term with a newline once and whole (boundary)",
      count (loopProof loopSt { tri with measure := "m\n  0" }) "(m\n  0)" == 1),
    ("loopProof has no slot name", !has (loopProof loopSt tri) "INV" && !has (loopProof loopSt tri) "STEP")
  ]

/-- A text of 0 to 5 characters of a small alphabet (with spaces), after the tag `tag`; the tag makes the texts of the
three terms of a triple different. -/
def genText (tag : String) (seed i : Nat) : String :=
  let cs := "xy 01+".toList
  tag ++ String.ofList ((List.range ((seed * 7 + i * 5 + tag.length) % 6)).map fun j =>
    cs.getD ((seed * 13 + i * 11 + tag.length * 3 + j * 17) % cs.length) 'x')

/-- The property: for a triple of three short texts, the proof holds each term once, in parentheses, in the order
invariant, measure, result. -/
def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  (List.range (max 100 cases)).map fun i =>
    let t : Triple :=
      { inv := genText "I_" seed i, measure := genText "M_" seed i, result := genText "R_" seed i }
    let p := loopProof loopSt t
    let inv := s!"({t.inv})"
    let measure := s!"({t.measure})"
    let result := s!"({t.result})"
    (s!"loopProof of the generated triple {i}: each term once, in order",
      count p inv == 1 && count p measure == 1 && count p result == 1 &&
      (match posOf p inv, posOf p measure, posOf p result with
       | some a, some b, some c => decide (a < b) && decide (b < c)
       | _, _, _ => false))

/-- Gives the number of failed checks. The suite runs when `only` is none or `render`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "render" then return 0
  let mut failed := 0
  for (name, ok) in checks ++ propertyChecks seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  render: {name}"
  return failed

end RenderTests
