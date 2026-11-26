import Skel.Types

/-! The prompt of the model that proposes loop triples (`docs/research/class-r-coordinator-deepseek-20261118.md`,
section 3). The function is pure: the same input gives the same text, byte for byte. -/

namespace Skel

/-- The input of the triple prompt: the L2+ text, the L3 text, the slot statement of the loop row, the loop rule text,
the earlier triples with their refuter verdicts, and the Lean error messages of the last type check. -/
structure TriplePromptInput where
  (l2PlusText l3Text slot loopRule : String)
  (history : List (Triple × Verdict))
  (errors : List String)

/-- The fixed text that starts the prompt: the task and its rules. -/
private def introLines : List String :=
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

/-- The fixed text of the reply format: the fenced `triple` block and the rules of the parser. -/
private def replyLines : List String :=
  [ "Give at most 4 candidates. Each candidate is one fenced block with exactly these three lines, in this order:",
    "```triple",
    "inv: <Lean term of type Prop over xs a x>",
    "measure: <Lean term of type Nat>",
    "result: <Lean term of the result type>",
    "```",
    "Text outside the fences is ignored. A block that does not have exactly these three keys is dropped." ]

/-- A section: its title line, then its body lines. -/
private def headed (title : String) (body : List String) : List String := s!"## {title}" :: body

/-- The lines that show a verdict. A counterexample gives its `shown` and `why` texts. -/
private def verdictLines : Verdict → List String
  | .pass n => [s!"verdict: pass ({n} samples)"]
  | .real c => ["verdict: real", s!"shown: {c.shown}", s!"why: {c.why}"]
  | .cti c => ["verdict: cti", s!"shown: {c.shown}", s!"why: {c.why}"]
  | .unknown w => ["verdict: unknown", s!"why: {w}"]

/-- The lines that show the triple number `i` with its verdict. -/
private def triedLines (i : Nat) (t : Triple) (v : Verdict) : List String :=
  [s!"Triple {i}:", s!"inv: {t.inv}", s!"measure: {t.measure}", s!"result: {t.result}"] ++ verdictLines v

/-- The prompt text. The sections are separated by an empty line. The history and the error sections are left out
when they are empty. -/
def triplePrompt (x : TriplePromptInput) : String :=
  let triedBlock := headed "Triples already tried"
    (((List.range x.history.length).zip x.history).flatMap fun (i, t, v) => triedLines (i + 1) t v)
  let errorBlock := headed "Lean errors of the last type check" x.errors
  let blocks : List (List String) :=
    [ introLines,
      headed "L2+ model text" [x.l2PlusText],
      headed "L3 text" [x.l3Text],
      headed "Slot statement" [x.slot],
      headed "Loop rule" [x.loopRule] ]
    ++ (if x.history.isEmpty then [] else [triedBlock])
    ++ (if x.errors.isEmpty then [] else [errorBlock])
    ++ [headed "Reply format" replyLines]
  "\n\n".intercalate (blocks.map fun ls => "\n".intercalate ls) ++ "\n"

/-- The input of the sampler prompt (`docs/one-way-lift-g3-plan-20261118.md`, 5.6, step 2): the L2+ model text, the
precondition (`WF` and the `C` of the statement), the failing sampler and its error, and the mutants to catch, each with its
form and the `blocksP` text of the mutant. -/
structure SamplerPromptInput where
  (l2PlusText precondition failing error : String)
  (mutants : List (String × String))

/-- The fixed text that starts the sampler prompt: the task and the acceptance rules. -/
private def samplerIntroLines : List String :=
  [ "You write the samplers of a refuter for a loop in a Lean 4 model of x86-64 code.",
    "The refuter draws inputs with two functions: refuteAdmitted (a start state and its expected result) and refuteFree (any state).",
    "The sampler below fails. Write both functions again. Keep the names, the argument and the result types of the failing sampler.",
    "An admitted input must satisfy the precondition: the heap is well formed and the statement hypotheses hold.",
    "Your samplers are accepted when all three checks hold:",
    "1. Each of 200 admitted samples satisfies the precondition.",
    "2. The claim that the model returns the same result as the L3 function passes on your admitted samples.",
    "3. Your admitted samples show a wrong result for at least one of the mutants below (the mutants are models with one change).",
    "Use only the text of this prompt. Do not use tools." ]

/-- The fixed text of the reply format of the sampler prompt. -/
private def samplerReplyLines : List String :=
  [ "Give one fenced block that starts with ```lean and holds exactly two definitions: def refuteAdmitted and def refuteFree.",
    "Start each definition at the beginning of a line. Do not write other definitions. Text outside the fence is ignored." ]

/-- A mutant: its number, its form, and its text. -/
private def mutantLines (i : Nat) (m : String × String) : List String :=
  [s!"Mutant {i} (form {m.1}):", m.2]

/-- The sampler prompt. The sections are separated by an empty line. The mutant section is left out when there is no mutant.
The same input gives the same text, byte for byte. -/
def samplerPrompt (x : SamplerPromptInput) : String :=
  let blocks : List (List String) :=
    [ samplerIntroLines,
      headed "L2+ model text" [x.l2PlusText],
      headed "Precondition" [x.precondition],
      headed "Failing sampler" [x.failing],
      headed "Error" [x.error] ]
    ++ (if x.mutants.isEmpty then [] else
      [headed "Mutants to catch" (((List.range x.mutants.length).zip x.mutants).flatMap fun (i, m) => mutantLines (i + 1) m)])
    ++ [headed "Reply format" samplerReplyLines]
  "\n\n".intercalate (blocks.map fun ls => "\n".intercalate ls) ++ "\n"

end Skel
