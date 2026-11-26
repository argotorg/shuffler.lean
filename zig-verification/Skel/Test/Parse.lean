import Skel.Parse

/-! The tests of `Skel/Parse.lean` (suite `parse`): `lake exe skel-test --only parse`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line. The verdict line fixtures copy the text form of `Found.line`
(`Skel/Lean/Refute.lean`); this file does not import that module. The property checks draw `cases` values of the
index and of the samples. The suite gives the number of failed checks. -/

namespace ParseTests

open Skel

private def info (text : String) : NxLift.Message :=
  { severity := .info, file := "Skel/Gen.lean", line := 1, col := 0, text := text }

private def err (text : String) : NxLift.Message :=
  { severity := .error, file := "Skel/Gen.lean", line := 1, col := 0, text := text }

private def warn (text : String) : NxLift.Message :=
  { severity := .warning, file := "Skel/Gen.lean", line := 2, col := 8, text := text }

/-- Whether an outcome is `failed`, with any errors. -/
private def isFailed : Outcome → Bool
  | .failed _ => true
  | _ => false

/-- The theorem that the checks of an outcome name. -/
def thm : String := "Skel.Gen.Sum.x"

/-- The obligation of the verdict checks. -/
def ob : ObId := { function := "Sum", name := "entry" }

/-- A `bv_decide` axiom of `thm`, named as this toolchain names it. -/
def bvAxiom : String := "Skel.Gen.Sum.x._native.bv_decide.ax_1_5"

/-- The line that `#print axioms` gives for a theorem with the axioms `axs` (text form). -/
def axiomsLine (name axs : String) : String := "'" ++ name ++ "' depends on axioms: [" ++ axs ++ "]"

/-- The verdict line of `Found.line` for a pass with `n` samples. -/
def passLine (n : Nat) : String := "{\"verdict\":\"pass\",\"samples\":" ++ toString n ++ "}"

/-- The verdict line of `Found.line` for a real counterexample at `index`. -/
def realLine (index : Nat) : String :=
  "{\"verdict\":\"real\",\"index\":" ++ toString index ++ ",\"why\":\"lhs and rhs differ\",\"shown\":\"[1, 2]\"}"

/-- The verdict line of `Found.line` for a cti at index 3. -/
def ctiLine : String := "{\"verdict\":\"cti\",\"index\":3,\"why\":\"stuck\",\"shown\":\"x\"}"

/-- The counterexample that `Verdict.parse` gives for `realLine index`, with the seed 7 and the subject `claim`. -/
def realCex (index : Nat) : Cex :=
  { ob := ob, subject := .claim, seed := 7, index := index, shown := "[1, 2]", why := "lhs and rhs differ" }

/-- Whether `r` is a parse that gives the verdict `v`. -/
def parsesTo (r : Except String Verdict) (v : Verdict) : Bool :=
  match r with
  | .ok x => x == v
  | .error _ => false

/-- Whether `r` is a failed parse. -/
def isError (r : Except String Verdict) : Bool :=
  match r with
  | .error _ => true
  | .ok _ => false

/-- The checks of the outcomes and of the verdict lines, each with its name. -/
def fixedChecks : List (String × Bool) :=
  [ ("a time-out gives timedOut",
      Outcome.ofRun .strict thm (.timedOut 5000) #[] == .timedOut 5000),
    ("an error gives failed with its text",
      Outcome.ofRun .strict thm (.exited 1) #[err "bad"] == .failed ["bad"]),
    ("an error and a time-out give timedOut",
      Outcome.ofRun .strict thm (.timedOut 5000) #[err "bad"] == .timedOut 5000),
    ("an error wins over an axioms line",
      Outcome.ofRun .strict thm (.exited 1) #[err "bad", info (axiomsLine thm "propext")] == .failed ["bad"]),
    ("propext gives accepted",
      Outcome.ofRun .strict thm (.exited 0) #[info (axiomsLine thm "propext")] == .accepted ["propext"]),
    ("a bv_decide axiom with strict gives gateRefused",
      Outcome.ofRun .strict thm (.exited 0)
        #[info (axiomsLine thm ("propext, Classical.choice, Quot.sound, " ++ bvAxiom))]
        == .gateRefused ["propext", "Classical.choice", "Quot.sound", bvAxiom]),
    ("a bv_decide axiom with bvDecide gives accepted",
      Outcome.ofRun .bvDecide thm (.exited 0)
        #[info (axiomsLine thm ("propext, Classical.choice, Quot.sound, " ++ bvAxiom))]
        == .accepted ["propext", "Classical.choice", "Quot.sound", bvAxiom]),
    ("no axioms line gives failed",
      Outcome.ofRun .strict thm (.exited 0) #[] == .failed ["no axioms line"]),
    ("an axioms line of another theorem is not used",
      Outcome.ofRun .strict thm (.exited 0) #[info (axiomsLine "Skel.Gen.Sum.y" "propext")]
        == .failed ["no axioms line"]),
    ("does not depend on any axioms gives accepted with an empty list",
      Outcome.ofRun .strict thm (.exited 0) #[info ("'" ++ thm ++ "' does not depend on any axioms")]
        == .accepted []),
    ("a sorry warning beside a clean axioms line gives failed",
      isFailed (Outcome.ofRun .strict thm (.exited 0)
        #[warn "declaration uses `sorry`", info (axiomsLine thm "propext")])),
    ("a sorry warning with single quotes beside a clean axioms line gives failed",
      isFailed (Outcome.ofRun .strict thm (.exited 0)
        #[warn "declaration uses 'sorry'", info (axiomsLine thm "propext")])),
    ("a sorry warning with the bvDecide gate beside a clean axioms line gives failed",
      isFailed (Outcome.ofRun .bvDecide thm (.exited 0)
        #[warn "declaration uses `sorry`", info (axiomsLine thm (bvAxiom))])),
    ("a warning that is not about sorry is accepted",
      Outcome.ofRun .strict thm (.exited 0) #[warn "unused variable `x`", info (axiomsLine thm "propext")]
        == .accepted ["propext"]),
    ("sorryAx with the sorry warning gives gateRefused",
      Outcome.ofRun .strict thm (.exited 0) #[warn "declaration uses `sorry`", info (axiomsLine thm "sorryAx")]
        == .gateRefused ["sorryAx"]),
    ("sorryAx with no warning and no error (an error dropped by guard_msgs) gives gateRefused",
      Outcome.ofRun .strict thm (.exited 0) #[info (axiomsLine thm "propext, sorryAx")]
        == .gateRefused ["propext", "sorryAx"]),
    ("a nonzero exit with no error message and a clean axioms line gives failed",
      isFailed (Outcome.ofRun .strict thm (.exited 1) #[info (axiomsLine thm "propext")])),
    ("ofPrinted: the axioms of all the printed theorems decide",
      Outcome.ofPrinted .strict (.exited 0)
        #[info (axiomsLine "a" "propext"), info (axiomsLine "b" "propext, Quot.sound")] == .accepted ["propext", "Quot.sound"]),
    ("ofPrinted: one printed theorem with sorryAx gives gateRefused",
      Outcome.ofPrinted .strict (.exited 0)
        #[info (axiomsLine "a" "propext"), info (axiomsLine "b" "sorryAx")] == .gateRefused ["propext", "sorryAx"]),
    ("ofPrinted: native_decide gives gateRefused",
      Outcome.ofPrinted .strict (.exited 0) #[info (axiomsLine "a" "Lean.ofReduceBool")] == .gateRefused ["Lean.ofReduceBool"]),
    ("ofPrinted: a new axiom gives gateRefused",
      Outcome.ofPrinted .bvDecide (.exited 0) #[info (axiomsLine "a" "ax")] == .gateRefused ["ax"]),
    ("ofPrinted: no printed line gives failed",
      Outcome.ofPrinted .strict (.exited 0) #[] == .failed ["no axioms line"]),
    ("ofPrinted: no axioms at all gives accepted",
      Outcome.ofPrinted .strict (.exited 0) #[info ("'a' does not depend on any axioms")] == .accepted []),
    ("ofPrinted: a sorry warning gives failed",
      isFailed (Outcome.ofPrinted .strict (.exited 0) #[warn "declaration uses `sorry`", info (axiomsLine "a" "propext")])),
    ("ofPrinted: an error gives failed",
      Outcome.ofPrinted .strict (.exited 1) #[err "bad", info (axiomsLine "a" "propext")] == .failed ["bad"]),
    ("a pass line gives pass 200",
      parsesTo (Verdict.parse ob .claim 7 #[info (passLine 200)]) (.pass 200)),
    ("a real line gives real",
      parsesTo (Verdict.parse ob .claim 7 #[info (realLine 3)]) (.real (realCex 3))),
    ("a cti line gives cti",
      parsesTo (Verdict.parse ob .claim 7 #[info ctiLine])
        (.cti { ob := ob, subject := .claim, seed := 7, index := 3, shown := "x", why := "stuck" })),
    ("no verdict line gives error",
      isError (Verdict.parse ob .claim 7 #[])),
    ("no verdict line among other lines gives error",
      isError (Verdict.parse ob .claim 7 #[info (axiomsLine thm "propext")])),
    ("two verdict lines give error",
      isError (Verdict.parse ob .claim 7 #[info (passLine 1), info (passLine 2)])),
    ("a verdict line with severity error is not a verdict line",
      isError (Verdict.parse ob .claim 7 #[err (passLine 1)])),
    ("a verdict line with broken JSON gives error",
      isError (Verdict.parse ob .claim 7 #[info "{\"verdict\":\"pass\""])),
    ("an unknown verdict word gives error",
      isError (Verdict.parse ob .claim 7 #[info "{\"verdict\":\"maybe\",\"index\":1}"])),
    ("a verdict line beside an axioms line is read",
      parsesTo (Verdict.parse ob .claim 7 #[info (axiomsLine thm "propext"), info (passLine 200)]) (.pass 200)),
    ("ofOutput: a verdict line gives the verdict, with an error message beside it",
      Verdict.ofOutput ob .claim 7 #[err "Unknown identifier `y`", info (passLine 200)] == .pass 200),
    ("ofOutput: no verdict line and no error gives the reason of the parse",
      Verdict.ofOutput ob .claim 7 #[] == .unknown "no verdict line"),
    ("ofOutput: no verdict line and a Lean error gives unknown with the error text",
      Verdict.ofOutput ob .claim 7 #[err "Unknown identifier `y`"]
        == .unknown "no verdict line: Lean error: Unknown identifier `y`"),
    ("ofOutput: the first two errors are shown, the others are not",
      Verdict.ofOutput ob .claim 7 #[err "E1", err "E2", err "E3"]
        == .unknown "no verdict line: Lean error: E1 | E2"),
    ("ofOutput: a warning is not shown",
      Verdict.ofOutput ob .claim 7 #[{ info "unused variable" with severity := .warning }, err "E1"]
        == .unknown "no verdict line: Lean error: E1"),
    ("ofOutput: a long error is cut to 300 characters with a mark",
      match Verdict.ofOutput ob .claim 7 #[err (String.ofList (List.replicate 1000 'e'))] with
      | .unknown w => w.length ≤ 300 + "no verdict line: Lean error: ".length + 3 && w.endsWith "..."
          && w.startsWith "no verdict line: Lean error: eee"
      | _ => false),
    ("ofOutput: an error of 3 lines is shown on one line",
      Verdict.ofOutput ob .claim 7 #[err "a\nb\nc"] == .unknown "no verdict line: Lean error: a b c")
  ]

/-- The checks that hold for each value of `cases`: a pass line with `i` samples and a real line at index `i`. -/
def propertyChecks (seed cases : Nat) : List (String × Bool) :=
  (List.range cases).flatMap fun i =>
    [ (s!"a pass line with {i} samples gives pass {i}",
        parsesTo (Verdict.parse ob .claim seed #[info (passLine i)]) (.pass i)),
      (s!"a real line at index {i} gives real {i}",
        parsesTo (Verdict.parse ob .claim seed #[info (realLine i)]) (.real { realCex i with seed := seed })) ]

/-- A triple for the reply checks. -/
def tripleA : Triple := { inv := "i <= n", measure := "n - i", result := "acc" }

/-- A second triple for the reply checks. -/
def tripleB : Triple := { inv := "j < m", measure := "m - j", result := "out" }

/-- Triples 3 to 5 for the reply checks. -/
def tripleC : Triple := { inv := "k < p", measure := "p - k", result := "res" }
def tripleD : Triple := { inv := "u <= v", measure := "v - u", result := "w" }
def tripleE : Triple := { inv := "a < b", measure := "b - a", result := "c" }

/-- A fenced block with the info string `info` and the lines `lines`, each followed by a newline. -/
def fenced (info : String) (lines : List String) : String :=
  "```" ++ info ++ "\n" ++ String.join (lines.map (· ++ "\n")) ++ "```\n"

/-- The fenced `triple` block of `t`: the keys `inv`, `measure` and `result`, one line each. -/
def tripleBlock (t : Triple) : String :=
  fenced "triple" ["inv: " ++ t.inv, "measure: " ++ t.measure, "result: " ++ t.result]

/-- The checks of `parseTriples`, each with its name. -/
def tripleChecks : List (String × Bool) :=
  [ ("a good reply with 2 blocks gives both triples",
      parseTriples (tripleBlock tripleA ++ tripleBlock tripleB) == [tripleA, tripleB]),
    ("a block without a key is dropped",
      parseTriples (fenced "triple" ["inv: x", "measure: m"]) == []),
    ("a block without a key does not drop the block after it",
      parseTriples (fenced "triple" ["inv: x", "measure: m"] ++ tripleBlock tripleA) == [tripleA]),
    ("a block with an extra key is dropped",
      parseTriples (fenced "triple" ["inv: x", "measure: m", "result: r", "extra: e"]) == []),
    ("a block with an extra key does not drop the block after it",
      parseTriples (fenced "triple" ["inv: x", "measure: m", "result: r", "extra: e"] ++ tripleBlock tripleA)
        == [tripleA]),
    ("a block with a duplicate key is dropped",
      parseTriples (fenced "triple" ["inv: x", "inv: y", "result: r"]) == []),
    ("a block with a duplicate key does not drop the block after it",
      parseTriples (fenced "triple" ["inv: x", "inv: y", "result: r"] ++ tripleBlock tripleA) == [tripleA]),
    ("a block with a duplicate key and four lines is dropped",
      parseTriples (fenced "triple" ["inv: x", "measure: m", "result: r", "result: s"]) == []),
    ("5 valid blocks give the first 4",
      parseTriples (String.join ([tripleA, tripleB, tripleC, tripleD, tripleE].map tripleBlock))
        == [tripleA, tripleB, tripleC, tripleD]),
    ("no block gives an empty list",
      parseTriples "just text\nno fence here\n" == []),
    ("an empty string gives an empty list",
      parseTriples "" == []),
    ("text before, between and after the blocks is ignored",
      parseTriples ("before\n" ++ tripleBlock tripleA ++ "between\n" ++ tripleBlock tripleB ++ "after\n")
        == [tripleA, tripleB]),
    ("a block with info string lean is ignored",
      parseTriples (fenced "lean" ["inv: x", "measure: m", "result: r"]) == []),
    ("a lean block beside a triple block leaves the triple",
      parseTriples (fenced "lean" ["inv: x", "measure: m", "result: r"] ++ tripleBlock tripleA) == [tripleA]),
    ("an unclosed block is dropped",
      parseTriples "```triple\ninv: x\nmeasure: m\nresult: r\n" == []),
    ("an unclosed block does not drop the block after it",
      parseTriples ("```triple\ninv: x\nmeasure: m\n" ++ tripleBlock tripleA) == [tripleA]),
    ("values with spaces at both ends are trimmed",
      parseTriples (fenced "triple" ["inv:   i <= n  ", "measure:  n - i ", "result:  acc   "]) == [tripleA]),
    ("a value keeps its later colons",
      parseTriples (fenced "triple" ["inv: fun x : Nat => x", "measure: m", "result: r"])
        == [{ inv := "fun x : Nat => x", measure := "m", result := "r" }]),
    ("the info string is read with its spaces trimmed",
      parseTriples (fenced " triple " ["inv: i <= n", "measure: n - i", "result: acc"]) == [tripleA]),
    ("Windows line ends give the same result as \\n",
      let lf := tripleBlock tripleA ++ tripleBlock tripleB
      parseTriples (lf.replace "\n" "\r\n") == parseTriples lf && parseTriples lf == [tripleA, tripleB])
  ]

/-- A linear congruential generator: the state after `s`. -/
def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

/-- `n` draws from the states of the generator, starting at `s`. -/
def draws (s : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => (s / 65536) :: draws (lcg s) n

/-- The next draw below `n`, and the draws that are left. -/
def pick (n : Nat) : List Nat → Nat × List Nat
  | [] => (0, [])
  | d :: ds => (d % n, ds)

/-- The strings that the generated fields take. None has a backtick or a space at an end. -/
def fieldPool : List String :=
  ["i <= n", "xs.length - i", "acc + 1", "fun x : Nat => x", "a:b", "(i + 1) * 2", "x.1", "s.toNat"]

/-- The lines that the generated filler takes. None has a backtick. -/
def fillerPool : List String :=
  ["", "some text", "inv: not a block", "measure: stray", "result", ":", "a : b", "  indented  "]

/-- A string of `pool`, and the draws that are left. -/
def pickFrom (pool : List String) (ds : List Nat) : String × List Nat :=
  let (i, ds) := pick pool.length ds
  (pool.getD i "", ds)

/-- A triple of pool strings. The `inv` field has a number, so that triples differ. -/
def genTriple (ds : List Nat) : Triple × List Nat :=
  let (i, ds) := pickFrom fieldPool ds
  let (m, ds) := pickFrom fieldPool ds
  let (r, ds) := pickFrom fieldPool ds
  let (k, ds) := pick 1000 ds
  ({ inv := s!"{i} {k}", measure := m, result := r }, ds)

/-- `n` filler lines, each followed by a newline. -/
def genFiller : Nat → List Nat → String × List Nat
  | 0, ds => ("", ds)
  | n + 1, ds =>
    let (line, ds) := pickFrom fillerPool ds
    let (rest, ds) := genFiller n ds
    (line ++ "\n" ++ rest, ds)

/-- A reply with `n` triples: 0 to 2 filler lines before each block and after the last one.
It gives the triples, the text and the draws that are left. -/
def genReply : Nat → List Nat → List Triple × String × List Nat
  | 0, ds =>
    let (k, ds) := pick 3 ds
    let (f, ds) := genFiller k ds
    ([], f, ds)
  | n + 1, ds =>
    let (k, ds) := pick 3 ds
    let (f, ds) := genFiller k ds
    let (t, ds) := genTriple ds
    let (ts, rest, ds) := genReply n ds
    (t :: ts, f ++ tripleBlock t ++ rest, ds)

/-- The checks that hold for each generated reply, for at least 200 cases: `parseTriples` gives the first 4 of the
triples of the reply, in order. -/
def tripleProperty (seed cases : Nat) : List (String × Bool) :=
  (List.range (max 200 cases)).map fun k =>
    let (n, ds) := pick 7 (draws (seed + k * 7919) 400)
    let (expected, text, _) := genReply n ds
    (s!"a generated reply of {n} triples (case {k}) gives the first 4",
      parseTriples text == expected.take 4)

/-- Gives the number of failed checks. The suite runs when `only` is none or `parse`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "parse" then return 0
  let mut failed := 0
  for (name, ok) in fixedChecks ++ tripleChecks ++ propertyChecks seed cases ++ tripleProperty seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  parse: {name}"
  return failed

end ParseTests
