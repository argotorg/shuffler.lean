import Skel.Prompt

/-! The tests of `Skel/Prompt.lean` (suite `prompt`): `lake exe skel-test --only prompt`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line. The generated inputs are built from their index only, so a run
gives the same checks each time. The suite gives the number of failed checks. -/

namespace PromptTests

open Skel

/-- The obligation of the counterexamples of the fixtures. -/
def ob : ObId := { function := "Sum", name := "entry" }

/-- The triple with the texts `inv-i`, `measure-i` and `result-i`. -/
def triOf (i : String) : Triple :=
  { inv := "inv-" ++ i, measure := "measure-" ++ i, result := "result-" ++ i }

/-- A counterexample of the triple `t`, with the shown and why texts. -/
def cexOf (t : Triple) (shown why : String) : Cex :=
  { ob := ob, subject := .triple t, seed := 1, index := 4, shown := shown, why := why }

/-- The golden input: one history triple with a real counterexample, and one error. -/
def goldenInput : TriplePromptInput :=
  { l2PlusText := "L2 text", l3Text := "L3 text", slot := "slot text", loopRule := "rule text",
    history := [(triOf "1", .real (cexOf (triOf "1") "s1" "w1"))], errors := ["err1"] }

/-- The intro lines of the golden text: the task, the meaning of `result`, one worked example, the names in scope, the verdicts. -/
def introText : List String :=
    [ "You propose loop triples for a proof of a loop in a Lean 4 model of x86-64 code.",
      "A triple is three Lean terms over xs, a and x: an invariant inv (type Prop), a measure (type Nat) and a result (the result type).",
      "x is the state at the loop head. result is a function of x: the value that the loop returns when it starts from the state x. It is not the value of the whole run from the entry state, except at the entry state. The step of the loop must give the same result for the next state.",
      "Example, for a loop that is not in this task. The loop counts the words of xs that are zero. Its state x has an index x.rcx and a count x.rax, and it starts at x.rcx = 0 and x.rax = 0. A triple:",
      "inv: x.rcx.toNat ≤ xs.length",
      "measure: xs.length - x.rcx.toNat",
      "result: x.rax + UInt64.ofNat ((xs.drop x.rcx.toNat).countP (· == 0))",
      "In the example, result is the count so far (x.rax) plus the count of the words that the loop has not read yet (xs.drop x.rcx.toNat). At the start state it is the count of all of xs. A constant, such as the count of all of xs, is not the value that the loop returns from each x.",
      "The refuter binds a, xs and y (the L3 result). A term with another free name can have the verdict unknown; the reason is then the Lean error of the refuter.",
      "The refuter evaluates decide (inv), so inv must have a Decidable instance: use =, ≤ and < on numbers, words and lists of words, ∧, ∨, ¬, → and a bounded ∀ i < n. Do not write a conjunct that the loop rule already has (such as x.input = a): In2p and Heap have no decidable equality, and the term does not elaborate.",
      "A refuter has tested each earlier triple. The verdict real means: wrong at the admitted entry state shown. The verdict cti means: shown satisfies inv, but why.",
      "Use only the text of this prompt. Do not use tools. Do not use the triple of any other loop.",
      "Propose triples that differ from the triples already tried." ]

/-- The golden text of `goldenInput`, written out line by line. -/
def goldenText : String :=
  "\n".intercalate
    (introText ++
    [
      "",
      "## L2+ model text",
      "L2 text",
      "",
      "## L3 text",
      "L3 text",
      "",
      "## Slot statement",
      "slot text",
      "",
      "## Loop rule",
      "rule text",
      "",
      "## Triples already tried",
      "Triple 1:",
      "inv: inv-1",
      "measure: measure-1",
      "result: result-1",
      "verdict: real",
      "shown: s1",
      "why: w1",
      "",
      "## Lean errors of the last type check",
      "err1",
      "",
      "## Reply format",
      "Give at most 4 candidates. Each candidate is one fenced block with exactly these three lines, in this order:",
      "```triple",
      "inv: <Lean term of type Prop over xs a x>",
      "measure: <Lean term of type Nat>",
      "result: <Lean term of the result type>",
      "```",
      "Text outside the fences is ignored. A block that does not have exactly these three keys is dropped." ]) ++ "\n"

/-- A fixture with each kind of verdict, three history triples and two errors. -/
def richInput : TriplePromptInput :=
  { l2PlusText := "L2 plus text", l3Text := "L3 text", slot := "slot statement", loopRule := "loop rule text",
    history := [(triOf "a", .real (cexOf (triOf "a") "shown-a" "why-a")),
                (triOf "b", .cti (cexOf (triOf "b") "shown-b" "why-b")),
                (triOf "c", .pass 200)],
    errors := ["error-one", "error-two"] }

/-- The fixture of `richInput` with an empty history. -/
def emptyHistory : TriplePromptInput := { richInput with history := [] }

/-- The fixture of `richInput` with no errors. -/
def emptyErrors : TriplePromptInput := { richInput with errors := [] }

/-- The fixture of `richInput` with an empty history and no errors. -/
def emptyBoth : TriplePromptInput := { richInput with history := [], errors := [] }

/-- Whether `out` holds `s`. The empty text is held by every text. -/
def holds (out s : String) : Bool := s.isEmpty || (out.splitOn s).length > 1

/-- The number of characters before the first `marker` in `out`. -/
def position (out marker : String) : Option Nat :=
  match out.splitOn marker with
  | pre :: _ :: _ => some pre.length
  | _ => none

/-- Whether the numbers are strictly increasing. -/
def increasing : List Nat → Bool
  | a :: b :: rest => a < b && increasing (b :: rest)
  | _ => true

/-- Whether each marker is in `out`, and the first occurrences come in the order of `markers`. -/
def inOrder (out : String) (markers : List String) : Bool :=
  match markers.mapM (position out) with
  | some ps => increasing ps
  | none => false

/-- The checks of the parts, the order, the boundaries, the negative cases and the determinism, each with its name. -/
def fixedChecks : List (String × Bool) :=
  let out := triplePrompt richInput
  let golden := triplePrompt goldenInput
  [ ("the golden input gives the golden text", golden == goldenText),
    ("the intro says what result is, and gives one worked example",
      holds golden "the value that the loop returns when it starts from the state x"
        && holds golden "Example, for a loop that is not in this task" && holds golden "result: x.rax + "),
    ("the intro names the y that the refuter binds",
      holds golden "The refuter binds a, xs and y"),
    ("the example is not the loop of a task of the benchmark",
      let intro := "\n".intercalate introText
      ["Sum", ".sum", "idxOf", "heapOf", "scanFrom", "runAt", "foldl"].all fun w => !holds intro w),
    ("the L2+ text is in the output", holds out "L2 plus text"),
    ("the L3 text is in the output", holds out "L3 text"),
    ("the slot statement is in the output", holds out "slot statement"),
    ("the loop rule is in the output", holds out "loop rule text"),
    ("each history invariant is in the output",
      ["inv-a", "inv-b", "inv-c"].all (holds out ·)),
    ("each history measure and result is in the output",
      ["measure-a", "result-a", "measure-b", "result-b", "measure-c", "result-c"].all (holds out ·)),
    ("each shown and why text is in the output",
      ["shown-a", "why-a", "shown-b", "why-b"].all (holds out ·)),
    ("each verdict is in the output",
      ["verdict: real", "verdict: cti", "verdict: pass (200 samples)"].all (holds out ·)),
    ("each Lean error is in the output",
      ["error-one", "error-two"].all (holds out ·)),
    ("the parts are in the order of section 3",
      inOrder out ["## L2+ model text", "## L3 text", "## Slot statement", "## Loop rule",
        "## Triples already tried", "## Lean errors of the last type check", "## Reply format"]),
    ("the history triples are in the order of the list",
      inOrder out ["Triple 1:", "inv: inv-a", "Triple 2:", "inv: inv-b", "Triple 3:", "inv: inv-c"]),
    ("each history triple is followed by its verdict",
      inOrder out ["inv: inv-a", "verdict: real", "inv: inv-b", "verdict: cti", "inv: inv-c", "verdict: pass"]),
    ("empty history: no history header",
      !holds (triplePrompt emptyHistory) "## Triples already tried"),
    ("empty history: no triple block",
      !holds (triplePrompt emptyHistory) "Triple 1:"),
    ("empty errors: no error header",
      !holds (triplePrompt emptyErrors) "## Lean errors of the last type check"),
    ("empty history and no errors: the other parts stay in order",
      inOrder (triplePrompt emptyBoth) ["## Loop rule", "## Reply format"]),
    ("the output of richInput has no replay secret",
      !holds out "REPLAY-SECRET"),
    ("the golden output has no replay word",
      !holds golden.toLower "replay"),
    ("the golden output has no hand proof phrase",
      !holds golden.toLower "hand proof"),
    ("the same input gives the same text",
      triplePrompt richInput == out),
    ("the golden input gives the same text twice",
      triplePrompt goldenInput == golden) ]

/-- The text of a generated field: its index and field number, then up to 8 characters of a small alphabet. -/
def genText (i j : Nat) : String :=
  let cs := "ab \n:".toList
  let body := (List.range ((i * 7 + j * 3) % 9)).map fun k =>
    cs.getD ((i * 5 + j * 11 + k * 13) % cs.length) 'a'
  s!"[{i}.{j}]" ++ String.ofList body

/-- The generated input of the index `i`: a history of 0 to 3 triples with each kind of verdict, and 0 to 2 errors. -/
def genInput (i : Nat) : TriplePromptInput :=
  let tri (j : Nat) : Triple := { inv := genText i j, measure := genText i (j + 1), result := genText i (j + 2) }
  let cex (j : Nat) : Cex := cexOf (tri j) (genText i (j + 3)) (genText i (j + 4))
  let verdict (j : Nat) : Verdict :=
    match i % 3 with
    | 0 => .pass i
    | 1 => .real (cex j)
    | _ => .cti (cex j)
  { l2PlusText := genText i 10, l3Text := genText i 11, slot := genText i 12, loopRule := genText i 13,
    history := (List.range (i % 4)).map fun j => (tri (5 * j), verdict (5 * j)),
    errors := (List.range (i / 4 % 3)).map fun j => genText i (20 + j) }

/-- The texts of a verdict that the prompt must hold: the shown and why texts of a counterexample. -/
def verdictTexts : Verdict → List String
  | .pass _ => []
  | .real c | .cti c => [c.shown, c.why]
  | .unknown w => [w]

/-- The texts of an input that the prompt must hold. -/
def fieldsOf (x : TriplePromptInput) : List String :=
  [x.l2PlusText, x.l3Text, x.slot, x.loopRule]
    ++ x.history.flatMap (fun (t, v) => [t.inv, t.measure, t.result] ++ verdictTexts v)
    ++ x.errors

/-- The checks that each text of each generated input is in its prompt. There are at least 100 inputs. -/
def propertyChecks (cases : Nat) : List (String × Bool) :=
  (List.range (max 100 cases)).map fun i =>
    let x := genInput i
    (s!"generated input {i}: each field is in the output", (fieldsOf x).all (holds (triplePrompt x) ·))

/-- Gives the number of failed checks. The suite runs when `only` is none or `prompt`. -/
def run (_seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "prompt" then return 0
  let mut failed := 0
  for (name, ok) in fixedChecks ++ propertyChecks cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  prompt: {name}"
  return failed

end PromptTests
