import Skel.TempDir
import Skel.Driver
import Skel.Io
import Skel.Replies

/-! The tests of the model rung of the triple ladder (suite `model`): `lake exe skel-test --only model`. The rung gives
the action `ask` and reads the event `answered`; the reply store is in `Skel/Replies.lean`. The pure checks drive the
step function with a fake that answers each action: a check is accepted, a refute gives a verdict, an `ask` gets a reply
from a list (the reply `n` for the ask `n`) or from a reply store. No Lean subprocess runs and no model is called. A
check that does not hold prints one `FAIL` line. The property draws `max cases 200` cases from the seed. The suite gives
the number of failed checks and failed cases. -/

namespace ModelTests

open Skel
open Skel.Toy.Sum (sumId template1 template2)
open System (FilePath)

/-- The configuration of the tests, with the limit of asks `asks`. -/
def cfgWith (asks : Nat) : Config := { gate := .strict, limitMs := 30000, seed := 7, samples := 200, asks := asks }

/-- The texts of the prompt of the tests. -/
def texts : PromptTexts := { l2PlusText := "L2P-TEXT", l3Text := "L3-TEXT", loopRule := "LOOP-RULE" }

/-- The correct triple of `toySum` (T2, with the present field names `rcx` and `rax`). -/
def good : Triple := template2

/-- The triple of the replay rung. -/
def hand : Triple := { good with inv := "HANDINV" }

/-- A triple that no check accepts, numbered by `n`. -/
def bad (n : Nat) : Triple := { inv := s!"BADINV{n}", measure := "BADMEASURE", result := "BADRESULT" }

/-- The loop row of the tests: its statement is the slot statement of the prompt. -/
def loopOb : Obligation :=
  { id := sumId "loop", cls := .refine, origin := .loop "LBB1_1", statement := "SLOT-STATEMENT", deps := [],
    claim := .loop }

/-- The ladders of the tests with the template list `ts`, no proof replies and no replay store. -/
def lad (ts : List Triple) : Ladders := ladders ts texts [] [] [] hand

/-- A render that gives the candidate as the text of the file. -/
def render : Obligation → Candidate → LeanFile := fun o c =>
  { name := o.id.name, text := reprStr c, limitMs := 30000 }

/-- A fenced `triple` block of `t`. -/
def block (t : Triple) : String :=
  s!"```triple\ninv: {t.inv}\nmeasure: {t.measure}\nresult: {t.result}\n```"

/-- A reply with the blocks of `ts`, in order, and text around them. -/
def reply (ts : List Triple) : String := "Candidates:\n" ++ "\n".intercalate (ts.map block) ++ "\nEnd.\n"

/-- The counterexample of a pending refute. -/
def cexOf (p : Pending) : Cex :=
  { ob := p.ob, subject := (match p.candidate with | .triple _ t => .triple t | _ => .claim), seed := 7, index := 3,
    shown := "s", why := "w" }

/-- The fake: the verdict of each refute and the reply of the ask `n` (counted from 0) with its prompt. -/
structure Fake where
  verdict : Pending → Verdict
  ask : Nat → String → Option String

/-- The verdict that passes `g` and gives `cti` to each other triple. -/
def onlyGood (g : Triple) : Pending → Verdict := fun p =>
  match p.candidate with
  | .triple _ t => if t == g then .pass 200 else .cti (cexOf p)
  | _ => .pass 1

/-- The verdict that passes `g` and gives `real` to each other triple. -/
def onlyGoodReal (g : Triple) : Pending → Verdict := fun p =>
  match p.candidate with
  | .triple _ t => if t == g then .pass 200 else .real (cexOf p)
  | _ => .pass 1

/-- The fake with the verdict `v` and the replies `rs`: the ask `n` gets `rs[n]`; an ask past the list gets no reply. -/
def withReplies (v : Pending → Verdict) (rs : List String) : Fake := { verdict := v, ask := fun n _ => rs[n]? }

/-- The fake with the verdict `v` and the reply store `s`: an ask gets the reply of its prompt. -/
def withStore (v : Pending → Verdict) (s : ReplyStore) : Fake := { verdict := v, ask := fun _ p => s.lookup p }

/-- The actions of a run and the final ledger. -/
structure Run where
  actions : List Action
  final : Ledger

/-- Drives the step function with the fake. `asked` is the number of asks so far. `none` when the fuel ends. -/
def driveFake (cfg : Config) (ls : Ladders) (fk : Fake) : Nat → Nat → Ledger → Event → List Action → Option Run
  | 0, _, _, _, _ => none
  | n + 1, asked, l, e, acc =>
    let (l', a) := step cfg ls render l e
    match a with
    | .check p _ => driveFake cfg ls fk n asked l' (.checked p (.accepted ["propext"]) 1) (a :: acc)
    | .refute p _ => driveFake cfg ls fk n asked l' (.refuted p (fk.verdict p) 1) (a :: acc)
    | .ask p prompt => driveFake cfg ls fk n (asked + 1) l' (.answered p (fk.ask asked prompt) 1) (a :: acc)
    | .weaken .. => driveFake cfg ls fk n asked l' .start (a :: acc)
    | .done _ => some { actions := (a :: acc).reverse, final := l' }

/-- The run on the loop row from the start. -/
def runLoop (cfg : Config) (ls : Ladders) (fk : Fake) : Option Run :=
  driveFake cfg ls fk 500 0 (Ledger.init [loopOb]) .start []

/-- The prompts of the ask actions of a run, in order. -/
def prompts (r : Run) : List String :=
  r.actions.filterMap fun a => match a with
    | .ask _ p => some p
    | _ => none

/-- The number of ask actions of a run. -/
def askCount (r : Run) : Nat := (prompts r).length

/-- The triples of the refute actions of a run, in order. -/
def refuted (r : Run) : List Triple :=
  r.actions.filterMap fun a => match a with
    | .refute p _ => (match p.candidate with | .triple _ t => some t | _ => none)
    | _ => none

/-- The kinds of the actions of a run, in order. -/
def kinds (r : Run) : List String :=
  r.actions.map fun a => match a with
    | .check .. => "check" | .refute .. => "refute" | .ask .. => "ask" | .weaken .. => "weaken" | .done _ => "done"

/-- The triple and the rung that close the loop row of a run. -/
def closedTriple (r : Run) : Option (InvRung × Triple) :=
  match r.final.records[0]? with
  | some rec => (match rec.status with | .closed c => c.triple | _ => none)
  | none => none

/-- The rung that closes the loop row of a run. -/
def closedRung (r : Run) : Option Rung :=
  match r.final.records[0]? with
  | some rec => (match rec.status with | .closed c => some c.rung | _ => none)
  | none => none

/-- Whether `s` has `sub` as a substring. -/
def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- A test on a run: false when the run does not end. -/
def onRun (cfg : Config) (ls : Ladders) (fk : Fake) (f : Run → Bool) : Bool :=
  match runLoop cfg ls fk with
  | some r => f r
  | none => false

/-- The prompt of the first ask of a run with no reply: the prompt for the empty history, from `triplePrompt`. -/
def firstPrompt : String :=
  triplePrompt
    { l2PlusText := "L2P-TEXT", l3Text := "L3-TEXT", slot := "SLOT-STATEMENT", loopRule := "LOOP-RULE",
      history := [], errors := [] }

/-- The attempts of a failed check with the error text `e`. -/
def failedCheck (e : String) : Attempt :=
  { candidate := .proof .closing "by x", result := .checked (.failed [e]), ms := 0 }

/-- The text of `n` lines `ERRLINE-001-END`, `ERRLINE-002-END`, ... -/
def errorLines (n : Nat) : String :=
  "\n".intercalate ((List.range n).map fun i => s!"ERRLINE-{String.ofList ((Nat.toDigits 10 (1000 + i + 1)).drop 1)}-END")

/-- The message of the unsolved goals of the check of a toy sum triple:
two goals, `ret_1` and `back_1.inv` (`docs/research/ds-i-analysis-20261119.md`, section 1). -/
def sumGoalsError : String :=
  "unsolved goals\ncase ret_1\np : BitVec 64\nframe : Heap\nxs✝ : List (BitVec 64)\na : In2p\ny : BitVec 64\nxs : List (BitVec 64)\nhxs : xs✝ = xs\na✝ : SumSpec.run xs = some y\nleft✝² : a.rdi.toBitVec = p\nleft✝¹ : a.rsi.toNat = xs.length\nleft✝ : a.heap = objsP p xs ++ frame\nw✝¹ : CpuPolicy\nw✝ : DataMem\nh✝ : Heap.Holds w✝¹ a.heap w✝\nx : St In2p\nhx : x.input = a ∧ x.rcx.toNat ≤ xs.length ∧ x.rax.toBitVec + (List.drop x.rcx.toNat xs).sum = xs.sum\nhp1 : x.input.rsi = x.rcx\n⊢ x.rax = { toBitVec := xs.sum }\n\ncase back_1.inv\np : BitVec 64\nframe : Heap\nxs✝ : List (BitVec 64)\na : In2p\ny : BitVec 64\nxs : List (BitVec 64)\nhxs : xs✝ = xs\na✝ : SumSpec.run xs = some y\nleft✝² : a.rdi.toBitVec = p\nleft✝¹ : a.rsi.toNat = xs.length\nleft✝ : a.heap = objsP p xs ++ frame\nw✝¹ : CpuPolicy\nw✝ : DataMem\nh✝ : Heap.Holds w✝¹ a.heap w✝\nx : St In2p\nhx : x.input = a ∧ x.rcx.toNat ≤ xs.length ∧ x.rax.toBitVec + (List.drop x.rcx.toNat xs).sum = xs.sum\nhp1 : ¬x.input.rsi = x.rcx\nv1 : Width.W64.type\nhp2 : x.input.heap.load (x.input.rdi.toBitVec + x.rcx.toBitVec * 8) Width.W64 = Res.ok v1\n⊢ { input := x.input, rax := { toBitVec := v1 } + x.rax, rcx := x.rcx + 1 }.input = a ∧\n    { input := x.input, rax := { toBitVec := v1 } + x.rax, rcx := x.rcx + 1 }.rcx.toNat ≤ xs.length ∧\n      { input := x.input, rax := { toBitVec := v1 } + x.rax, rcx := x.rcx + 1 }.rax.toBitVec +\n          (List.drop { input := x.input, rax := { toBitVec := v1 } + x.rax, rcx := x.rcx + 1 }.rcx.toNat xs).sum =\n        xs.sum"

/-- The message of `n` unsolved goals `case g1` … `case gn`. Each has 30 hypotheses `hyp-K-01 : P` … and the goal
`⊢ GOAL-K-END`. -/
def manyGoalsError (n : Nat) : String :=
  let pad (k : Nat) : String := if k < 10 then s!"0{k}" else toString k
  let goal (k : Nat) : String :=
    "\n".intercalate ([s!"case g{k}"] ++ (List.range 30).map (fun j => s!"hyp-{k}-{pad (j + 1)} : P") ++ [s!"⊢ GOAL-{k}-END"])
  "unsolved goals\n" ++ "\n\n".intercalate ((List.range n).map fun k => goal (k + 1))

/-- The prompt that the model rung gives for the history `as`; none when it gives no ask. -/
def promptFor (acts : List Attempt) : Option String :=
  match modelRung texts loopOb { attempts := acts, cexs := [] } with
  | some (.ask p) => some p
  | _ => none

/-! The store. -/

/-- A text with a newline, quotes, a backslash, a tab, a carriage return and non-ASCII characters. -/
def awkward : String := "line1\nsay \"hi\" \\ back\t∀ x, μ x\r\nend"

/-- The store with two entries. -/
def store2 : ReplyStore := (ReplyStore.empty.insert "prompt one" "reply one").insert awkward awkward

/-- Whether the parse of `text` is an error that starts with `prefix`. -/
def errStarts (text pre : String) : Bool :=
  match ReplyStore.parse text with
  | .error e => e.startsWith pre
  | .ok _ => false

/-- Whether the parse gave the store `s`. -/
def okIs (e : Except String ReplyStore) (s : ReplyStore) : Bool :=
  match e with
  | .ok x => x == s
  | .error _ => false

/-- A valid line of the file form. -/
def goodLine : String := (ReplyStore.empty.insert "p" "r").toJsonl.trimAscii.toString

/-! The property. -/

/-- The next state of a linear congruential generator. -/
def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

/-- `n` values of a linear congruential generator from the seed `s`. -/
def stream : Nat → Nat → List Nat
  | _, 0 => []
  | s, n + 1 => (s / 65536) :: stream (lcg s) n

/-- The triples of the pool of the property: the correct triple, the first template, and four others. -/
def pool : List Triple := [good, template1, bad 1, bad 2, bad 3, bad 4]

/-- A reply from a list of numbers: each number gives a block of the pool; the number 6 gives text that is no block. -/
def replyOf (ns : List Nat) : String :=
  "\n".intercalate (ns.map fun n => if n % 7 == 6 then "no block here" else block (pool.getD (n % 7) good))

/-- The replies, the limit of asks and the verdict of the case of the seed. -/
def genCase (seed : Nat) : List String × Nat × (Pending → Verdict) :=
  let ns := stream seed 60
  let k := ns[0]! % 5
  let replies := (List.range k).map fun i => replyOf ((ns.drop (2 + 8 * i)).take (ns[1 + i]! % 7))
  let asks := ns[1]! % 6
  let v : Pending → Verdict := fun p =>
    match p.candidate with
    | .triple _ t =>
      match (hash (seed, reprStr t)).toNat % 3 with
      | 0 => .pass 200
      | 1 => .cti (cexOf p)
      | _ => .real (cexOf p)
    | _ => .pass 1
  (replies, asks, v)

/-- Whether a list has two equal elements. -/
def hasDup : List Triple → Bool
  | [] => false
  | t :: ts => ts.contains t || hasDup ts

/-- A case of the property is good when the run ends, the number of asks is at most the limit and no triple is tried
two times. -/
def caseOk (seed : Nat) : Bool :=
  let (rs, asks, v) := genCase seed
  match runLoop (cfgWith asks) (lad []) (withReplies v rs) with
  | none => false
  | some r => askCount r ≤ asks && !hasDup (refuted r) && r.final.finished

/-! The checks. -/

/-- The checks, each with its name. -/
def checks : List (String × Bool) :=
  [ -- the ladder and the configuration
    ("the triple rungs are template, model, replay",
      (lad []).triple.map (·.1) == ([.template, .model, .replay] : List InvRung)),
    ("the default limit of asks is 4",
      (({ gate := .strict, limitMs := 1, seed := 1, samples := 1 } : Config).asks) == 4),
    -- the model rung reached through an empty template list
    ("empty templates and a store with the reply: one ask, the row closes with the rung model",
      let s := ReplyStore.empty.insert firstPrompt (reply [good])
      onRun (cfgWith 3) (lad []) (withStore (onlyGood good) s) fun r =>
        askCount r == 1 && closedTriple r == some (.model, good) && refuted r == [good]),
    ("the first prompt is the prompt of the row texts with an empty history",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGood good) [reply [good]]) fun r =>
        prompts r == [firstPrompt]),
    ("the ask comes before any refute when the template list is empty",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGood good) [reply [good]]) fun r =>
        kinds r == ["ask", "refute", "check", "done"]),
    ("a template that passes means no ask",
      onRun (cfgWith 3) (lad [good]) (withReplies (onlyGood good) []) fun r =>
        askCount r == 0 && closedTriple r == some (.template, good)),
    ("a wrong triple first and the correct one second: the wrong one is refuted, the correct one follows, one ask",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGoodReal good) [reply [bad 1, good]]) fun r =>
        askCount r == 1 && refuted r == [bad 1, good] && closedTriple r == some (.model, good)),
    ("a reply of 5 blocks: only 4 are tried before the next ask",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGood good) [reply ((List.range 5).map bad)]) fun r =>
        (kinds r).take 6 == ["ask", "refute", "refute", "refute", "refute", "ask"] &&
        (refuted r).take 4 == (List.range 4).map bad && !(refuted r).contains (bad 4)),
    -- the ask limit
    ("a reply with no triple block counts as one ask: the ladder goes to replay after the limit",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGood hand) ["no block", "no block", "no block", "no block"]) fun r =>
        askCount r == 3 && refuted r == [hand] && closedTriple r == some (.replay, hand)),
    ("an empty reply counts as one ask",
      onRun (cfgWith 2) (lad []) (withReplies (onlyGood hand) ["", "", "", ""]) fun r =>
        askCount r == 2 && closedTriple r == some (.replay, hand)),
    ("a store miss counts as one ask",
      onRun (cfgWith 4) (lad []) (withStore (onlyGood hand) ReplyStore.empty) fun r =>
        askCount r == 4 && closedTriple r == some (.replay, hand)),
    ("a limit of 0 gives no ask",
      onRun (cfgWith 0) (lad []) (withReplies (onlyGood hand) [reply [good]]) fun r =>
        askCount r == 0 && closedTriple r == some (.replay, hand)),
    ("a limit of 1 gives one ask",
      onRun (cfgWith 1) (lad []) (withReplies (onlyGood hand) [reply [bad 1], reply [good]]) fun r =>
        askCount r == 1 && refuted r == [bad 1, hand]),
    ("the default limit of 4 gives 4 asks",
      onRun { cfgWith 0 with asks := 4 } (lad []) (withReplies (onlyGood hand) []) fun r => askCount r == 4),
    ("a limit that is reached with all triples refuted: the replay triple is the last refute",
      onRun (cfgWith 2) (lad []) (withReplies (onlyGood hand) [reply [bad 1], reply [bad 2]]) fun r =>
        refuted r == [bad 1, bad 2, hand] && askCount r == 2),
    -- the prompt of the next ask
    ("the second prompt differs from the first and holds the tried triple and its verdict",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGood hand) [reply [bad 1], "no block"]) fun r =>
        match prompts r with
        | p1 :: p2 :: _ =>
          p1 != p2 && has p2 "inv: BADINV1" && has p2 "verdict: cti" && !has p1 "BADINV1" && !has p1 "verdict:"
        | _ => false),
    ("the second prompt holds the verdict real of a real counterexample",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGoodReal hand) [reply [bad 1], "no block"]) fun r =>
        match prompts r with
        | _ :: p2 :: _ => has p2 "inv: BADINV1" && has p2 "verdict: real"
        | _ => false),
    ("the prompt holds the texts of the row",
      onRun (cfgWith 1) (lad []) (withReplies (onlyGood hand) []) fun r =>
        match prompts r with
        | [p] => has p "L2P-TEXT" && has p "L3-TEXT" && has p "SLOT-STATEMENT" && has p "LOOP-RULE"
        | _ => false),
    -- the cut of the errors
    ("errors of 50 lines: the prompt holds line 20 and not line 21",
      match promptFor [failedCheck (errorLines 50)] with
      | some p => has p "ERRLINE-020-END" && !has p "ERRLINE-021-END" && has p "ERRLINE-001-END"
      | none => false),
    ("errors of exactly 20 lines: all are in the prompt",
      match promptFor [failedCheck (errorLines 20)] with
      | some p => has p "ERRLINE-020-END"
      | none => false),
    ("errors of 21 lines: the 21st is cut",
      match promptFor [failedCheck (errorLines 21)] with
      | some p => has p "ERRLINE-020-END" && !has p "ERRLINE-021-END"
      | none => false),
    ("errors in two messages: the cut counts the lines of both",
      match promptFor [{ failedCheck "" with result := .checked (.failed [errorLines 15, (errorLines 15).replace "ERRLINE" "SECOND"]) }] with
      | some p => has p "ERRLINE-015-END" && has p "SECOND-005-END" && !has p "SECOND-006-END"
      | none => false),
    -- the unsolved goals
    ("unsolved goals of the toy sum: the prompt holds the case line and the goal of each goal",
      match promptFor [failedCheck sumGoalsError] with
      | some p => has p "case ret_1" && has p "⊢ x.rax = { toBitVec := xs.sum }" && has p "case back_1.inv"
          && has p "(List.drop { input := x.input, rax := { toBitVec := v1 } + x.rax, rcx := x.rcx + 1 }.rcx.toNat xs).sum ="
          && has p "        xs.sum"
      | none => false),
    ("unsolved goals of the toy sum: the hypotheses next to the goal are in the prompt",
      match promptFor [failedCheck sumGoalsError] with
      | some p => has p "hx : x.input = a ∧ x.rcx.toNat ≤ xs.length" && has p "hp2 : x.input.heap.load"
      | none => false),
    ("unsolved goals: the hypotheses far from the goal are cut",
      match promptFor [failedCheck (manyGoalsError 2)] with
      | some p => has p "hyp-1-30" && has p "hyp-1-25" && !has p "hyp-1-24" && !has p "hyp-1-01"
      | none => false),
    ("unsolved goals: each case line and each goal of 1 to 9 goals is in the prompt",
      (List.range 9).all fun i =>
        match promptFor [failedCheck (manyGoalsError (i + 1))] with
        | some p => (List.range (i + 1)).all fun k => has p s!"case g{k + 1}\n" && has p s!"⊢ GOAL-{k + 1}-END"
        | none => false),
    ("unsolved goals in two messages: the goals of both are in the prompt",
      match promptFor [{ failedCheck "" with result := .checked (.failed [manyGoalsError 2, (manyGoalsError 1).replace "GOAL-1" "OTHER"]) }] with
      | some p => has p "⊢ GOAL-2-END" && has p "⊢ OTHER-END"
      | none => false),
    ("an error that is not a goal keeps the cut of 20 lines next to unsolved goals",
      match promptFor [{ failedCheck "" with result := .checked (.failed [errorLines 30, manyGoalsError 1]) }] with
      | some p => has p "ERRLINE-020-END" && !has p "ERRLINE-021-END" && has p "⊢ GOAL-1-END"
      | none => false),
    ("the errors of the newest failed check are used",
      match promptFor [failedCheck "NEWERR", failedCheck "OLDERR"] with
      | some p => has p "NEWERR" && !has p "OLDERR"
      | none => false),
    ("no failed check gives no error section",
      match promptFor [] with
      | some p => !has p "Lean errors of the last type check"
      | none => false),
    -- the filter
    ("a triple tried by the template rung is not tried again from a reply",
      onRun (cfgWith 3) (lad [template1]) (withReplies (onlyGood good) [reply [template1, good]]) fun r =>
        refuted r == [template1, good] && askCount r == 1 && closedTriple r == some (.model, good)),
    ("a triple that the reply gives two times is tried once",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGood good) [reply [bad 1, bad 1, good]]) fun r =>
        refuted r == [bad 1, good]),
    ("a triple of the first reply that comes again in the second reply is not tried again",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGood good) [reply [bad 1], reply [bad 1, good]]) fun r =>
        refuted r == [bad 1, good] && askCount r == 2),
    ("a triple of the replay rung that the model gave is not tried again by replay",
      onRun (cfgWith 1) (lad []) (withReplies (onlyGood good) [reply [hand]]) fun r =>
        refuted r == [hand] && askCount r == 1),
    -- the ask is a state of the history: the same state gives the same ask
    ("the ask for a history is the same two times",
      promptFor [] == promptFor [] && (promptFor []).isSome),
    ("an unanswered ask in the history is one used ask",
      let a : Attempt := { candidate := .ask "p", result := .answered none, ms := 0 }
      (match modelRung texts loopOb { attempts := [a], cexs := [] } with | some (.ask _) => true | _ => false)),
    -- the template rung with the model rung present
    ("the model rung is not reached while a template is untried",
      (lad [good]).triple.head?.bind (fun (_, p) => p loopOb ⟨[], []⟩) == some (.triple good)),
    -- a closed row keeps the ask in its attempts
    ("the ledger has the ask and its answer as an attempt",
      onRun (cfgWith 3) (lad []) (withReplies (onlyGood good) [reply [good]]) fun r =>
        (r.final.history loopOb.id).attempts.any fun a =>
          match a.candidate, a.result with
          | .ask p, .answered (some rep) => p == firstPrompt && rep == reply [good]
          | _, _ => false),
    -- the store
    ("insert then lookup gives the reply", (ReplyStore.empty.insert "p" "r").lookup "p" == some "r"),
    ("lookup of another prompt gives none", (ReplyStore.empty.insert "p" "r").lookup "q" == none),
    ("lookup in the empty store gives none", ReplyStore.empty.lookup "p" == none),
    ("insert of a prompt that is in the store replaces its reply",
      let s := (ReplyStore.empty.insert "p" "r1").insert "p" "r2"
      s.lookup "p" == some "r2" && s.entries.length == 1),
    ("the file form of the store reads back to the same store", okIs (ReplyStore.parse store2.toJsonl) store2),
    ("the file form has one line for each entry", (store2.toJsonl.splitOn "\n").length == 3 &&
      store2.toJsonl.endsWith "\n"),
    ("the file form of the empty store is the empty text", ReplyStore.empty.toJsonl == ""),
    ("the empty text parses to the empty store", okIs (ReplyStore.parse "") ReplyStore.empty),
    ("the awkward reply is found after the round trip",
      match ReplyStore.parse store2.toJsonl with
      | .ok s => s.lookup awkward == some awkward && s.lookup "prompt one" == some "reply one"
      | .error _ => false),
    ("a line with no JSON is an error that names the line number",
      errStarts (goodLine ++ "\n{not json\n") "line 2:"),
    ("a line with a missing field is an error that names the line",
      errStarts "{\"hash\":\"0000000000000000\",\"prompt\":\"p\"}\n" "line 1:"),
    ("a line with a hash that is not the hash of its prompt is an error that names the line",
      errStarts (goodLine ++ "\n" ++ goodLine ++ "\n" ++
        "{\"hash\":\"0000000000000000\",\"prompt\":\"p\",\"reply\":\"r\"}\n") "line 3:"),
    ("a line with a field that is not a string is an error that names the line",
      errStarts "{\"hash\":1,\"prompt\":\"p\",\"reply\":\"r\"}\n" "line 1:"),
    ("an empty line in the middle is an error that names the line",
      errStarts (goodLine ++ "\n\n" ++ goodLine ++ "\n") "line 2:"),
    ("a file with no final newline parses", okIs (ReplyStore.parse goodLine) (ReplyStore.empty.insert "p" "r")),
    -- the hash
    ("hash of the empty string is the FNV-1a offset", hashPrompt "" == 0xcbf29ce484222325),
    ("hash of a", hashPrompt "a" == 0xaf63dc4c8601ec8c),
    ("hash of foobar", hashPrompt "foobar" == 0x85944171f73967e8),
    ("hash of a string with non-ASCII characters (UTF-8 bytes)", hashPrompt "∀ μ" == 0x186a379b960d679d),
    ("the hex form has 16 digits", hashHex (hashPrompt "a") == "af63dc4c8601ec8c" && (hashHex 1).length == 16),
    -- the run record of an ask
    ("the line of a hit has the hash, hit and the number of triples",
      Driver.askLine "a" (some (reply [good, bad 1])) 5 == "ask af63dc4c8601ec8c hit 2 triples 5 ms"),
    ("the line of a miss has miss and 0 triples", Driver.askLine "a" none 0 == "ask af63dc4c8601ec8c miss 0 triples 0 ms"),
    ("the line of a reply with no block is a hit with 0 triples",
      Driver.askLine "a" (some "none") 0 == "ask af63dc4c8601ec8c hit 0 triples 0 ms"),
    ("the line of a reply of 5 blocks counts 4 triples",
      Driver.askLine "a" (some (reply ((List.range 5).map bad))) 0 == "ask af63dc4c8601ec8c hit 4 triples 0 ms")
  ]

/-- The real `drive` with the step function of the core and an `ask` that reads a store: the loop row closes on the rung
`model` and the store is read once. -/
def driveCheck : IO Bool := do
  let s := ReplyStore.empty.insert firstPrompt (reply [bad 1, good])
  let seen ← IO.mkRef (0 : Nat)
  let rend : Obligation → Candidate → LeanFile := fun o c =>
    match c with
    | .triple _ t => { name := o.id.name, text := t.inv, limitMs := 1 }
    | _ => render o c
  let refute : Refuter := fun f => do
    let c : Cex := { ob := loopOb.id, subject := .claim, seed := 7, index := 0, shown := "s", why := "w" }
    pure ((if f.text == good.inv then .pass 200 else .cti c), 1)
  let report ← Skel.drive (fun _ => pure (.accepted ["propext"], 1)) refute (fun _ _ => pure ())
    (fun prompt => do seen.modify (· + 1); pure (s.lookup prompt, 0))
    (step (cfgWith 3) (lad []) rend) (Ledger.init [loopOb]) .start
  let n ← seen.get
  return n == 1 && report.rows.map (·.tripleRung) == [some .model]

/-- The store file: a missing file is the empty store, a written store reads back, and a broken file is an IO error that
names the line. -/
def fileCheck : IO Bool := do
  let dir ← Skel.tempDir "model-test"
  let missing ← Io.readReplies (dir / "none.jsonl")
  IO.FS.writeFile (dir / "replies.jsonl") store2.toJsonl
  let back ← Io.readReplies (dir / "replies.jsonl")
  IO.FS.writeFile (dir / "broken.jsonl") (goodLine ++ "\nbroken\n")
  let broken ← try
      discard <| Io.readReplies (dir / "broken.jsonl")
      pure ""
    catch e => pure (toString e)
  let (reply1, ms) ← (Io.storeAsker store2) "prompt one"
  let (reply2, _) ← (Io.storeAsker store2) "unknown"
  return missing == ReplyStore.empty && back == store2 && has broken "line 2" && reply1 == some "reply one" &&
    ms == 0 && reply2 == none

/-- The checks on the real sources: the setup of `toySum` has a model rung whose first prompt for the loop row holds the
texts of the real files (the model declarations, the slot statement, the loop skeleton) and none of the hand step. -/
def realChecks : IO (List (String × Bool)) := do
  let src : Skel.Toy.Sum.Sources :=
    { sum := ← IO.FS.readFile "Lift/Spike/Sum.lean", sites := ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean" }
  let prompt? : Option (Obligation × String) :=
    match Driver.setup (cfgWith 4) .none src with
    | .error _ => none
    | .ok s =>
      match s.ladders.triple.find? (·.1 == .model), s.env.gen.obligations.find? (·.claim == .loop) with
      | some (_, p), some ob =>
        (match p ob ⟨[], []⟩ with
         | some (.ask text) => some (ob, text)
         | _ => none)
      | _, _ => none
  match prompt? with
  | none => return [("the setup of the real sources has a model rung that asks for the loop row", false)]
  | some (ob, p) =>
    return
      [ ("the real prompt holds the model declarations",
          ["structure In2p", "inductive Lbl", "structure St", "def blocksP", "def run", "def C"].all (has p ·)),
        ("the real prompt holds the slot statement of the loop row", has p ob.statement && has p "SimArr xs a"),
        ("the real prompt holds the loop proof text and SimArr",
          has p "lift_loop!" && has p "def SimArr" && has p "MEASURE"),
        ("the real prompt holds no line of the hand step",
          !has p "rintro x ⟨rfl, hle⟩ ih" && !has p "by_cases hc : x.rcx.toNat = xs.length"),
        ("the real prompt has no model text of the proofs of the blocks", !has p "theorem decompiles_l2") ]

/-- Gives the number of failed checks and failed cases. The suite runs when `only` is none or `model`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "model" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  model: {name}"
  for (name, ok) in ← realChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  model: {name}"
  unless ← driveCheck do
    failed := failed + 1
    IO.println "FAIL  model: drive with a store ask closes the loop row on the rung model"
  unless ← fileCheck do
    failed := failed + 1
    IO.println "FAIL  model: the store file reads back, a missing file is empty, a broken file names its line"
  for i in List.range (max cases 200) do
    unless caseOk (seed + i) do
      failed := failed + 1
      IO.println s!"FAIL  model: asks are over the limit, a triple repeats or the run does not end (seed {seed + i})"
  return failed

end ModelTests
