import Skel.Discover.Lang
import Skel.Discover.Site
import Skel.Discover.Trace
import Skel.Ask

/-! The prompt of the LLM proposer of the invariant discovery (`docs/research/invariant-discovery-design-20261119.md`,
section 3.3 (c), task D10), and the asks for it.

The prompt has the Lean text of the site (the step, the state, the parameters, the fuel at the entry and the entry
condition), the context of the site (`ProposerInput.context`: for a machine site the names of the refuter, the loop row, the
head registers, the L3 spec and the blocks), the callees of the step with their L3 specs (DISC-CALL; only for a step with a call), the feature names, the first ten rows of a trace, the atoms that passed the trace pass, and each rejected
candidate with its counterexample (`shown`, `why`). The reply is the fenced `quad` blocks that `parseQuads` reads. The
prompt is a pure function of its input: the same input gives the same text, byte for byte.

An ask goes through the reply store of `Skel.Ask`, keyed by the hash of the prompt. A stored reply gives its candidates
with no call. Otherwise `leantools ask` runs with `--max-usd` of one ask: the USD cap of the site divided by the asks.
The bound of a call is at least its cost, so the bounds of the asks of a site add up to at most the USD cap. The
budget file is the one of `leantools ask`. The count of asks is the caller's: `propose` refuses the ask when `made`
reaches `asks`, so the caller counts the asks of one run of the site. A value outside the grammar is a free Lean term
(`parseQuadsFree`, HARNESS-LOOP2): elaboration, the refuter and the closer judge it. Only a block of a bad form refuses the
reply; the next prompt shows the refused reply with its reason (`ProposerInput.refused`), so it has a new hash in the store. -/

namespace Skel.Discover

/-- A candidate that the refuter rejected, with its counterexample: the state `shown` and the reason `why`. -/
structure Rejected where
  quad : Quad
  shown : String
  why : String
  deriving DecidableEq, Repr

/-- A reply that was refused before the refuter (HARNESS-LOOP2): its text and the reason. The next prompt shows it. -/
structure Refusal where
  reply : String
  why : String
  deriving DecidableEq, Repr

/-- The most characters of a refused reply in a prompt. -/
def refusalChars : Nat := 4000

/-- The input of the proposer prompt of one site. Of `rows`, the first `promptRows` are shown. -/
structure ProposerInput where
  site : LoopSite
  features : List Feature
  rows : Trace
  passed : List Atom
  rejected : List Rejected
  /-- More facts of the site, as prompt lines (HARNESS-LOOP D5): for a machine site the names that an atom may use with their
  types, the hypotheses of the loop row, the entry values of the head registers, the L3 spec and the blocks. Empty: no section. -/
  context : List String := []
  /-- The replies of the earlier asks that were refused before the refuter, with the reason (HARNESS-LOOP2). -/
  refused : List Refusal := []

/-- The number of trace rows in the prompt. -/
def promptRows : Nat := 10

/-- The caps of the proposer of one site: at most `asks` asks, and at most `usdMicro` micro-dollars for all of them
(`50000` is 0.05 USD). -/
structure AskCap where
  asks : Nat := 2
  usdMicro : Nat := 50000
  deriving DecidableEq, Repr

/-- The `--max-usd` of one ask: the USD cap divided by the asks. -/
def AskCap.perAskMicro (c : AskCap) : Nat := c.usdMicro / c.asks

/-- The decimal text of micro-dollars, without trailing zeros: `50000` is `0.05`, `1000000` is `1`. -/
def usdText (micro : Nat) : String :=
  let digits := toString (micro % 1000000)
  let padded := String.ofList (List.replicate (6 - digits.length) '0') ++ digits
  let frac := String.ofList ((padded.toList.reverse.dropWhile (· == '0')).reverse)
  let whole := toString (micro / 1000000)
  if frac.isEmpty then whole else whole ++ "." ++ frac

/-- The reasons that an ask gives no candidates. -/
inductive ProposeError where
  | capReached (asks : Nat)      -- the site has had all its asks
  | noReply                      -- no stored reply, and the call gave none (the reason is in the log)
  | refused (e : QuadError) (reply : String)  -- the blocks of the reply have a bad form; the reply text
  deriving DecidableEq, Repr

/-- The models of the chain with the caps of their asks. The first model has the cap `cap` (its `asks` replaced by the `asks`
of the model, when it has one); a later model has its own `asks` (else `cap.asks`) and its own `--ask-max-usd` as the USD cap
of its asks of one site. -/
def linkCaps (cap : AskCap) (c : Skel.Ask.Cfg) : List (AskCap × Skel.Ask.Link) :=
  (List.range c.links.length).zip c.links |>.map fun (i, l) =>
    let asks := l.asks.getD cap.asks
    (if i == 0 then { cap with asks } else { asks, usdMicro := ((Skel.Prove.usdOfText l.maxUsd).toOption.getD 0) / 10 ^ 6 }, l)

/-- The model of the ask number `made` of a site (from 0), with its index in the chain: the first model has its asks, then the
next model has its asks, and so on. None after the last ask of the last model. -/
def pickLink : List (AskCap × Skel.Ask.Link) → Nat → Option (Nat × AskCap × Skel.Ask.Link)
  | [], _ => none
  | (c, l) :: rest, n =>
    if n < c.asks then some (0, c, l)
    else (pickLink rest (n - c.asks)).map fun (i, c', l') => (i + 1, c', l')

/-- The id of the site of a prompt: the text after `loop: ` on its line; `""` when the prompt has no such line. -/
def siteIdOf (prompt : String) : String :=
  ((prompt.splitOn "\n").findSome? fun l => if l.startsWith "loop: " then some (l.drop 6).toString else none).getD ""

/-- One ask of a site. `made` is the number of asks of the site before this one. A stored reply of `prompt` gives its
candidates with no call. Otherwise the call of `leantools ask` runs with the settings `base` (`none`: no model, no call).
With a chain of models the asks go to the models in turn (`pickLink`): the first model gets its asks, with the rejected
candidates of the site in each prompt. A reply that the grammar refuses is an ask that is made. The final models (after the
first) get their asks only for a site that the allow file of `base` names (`siteIdOf`). For any other site the ask is refused
(`capReached`), and the site is written to the escalation list `escalate.jsonl` next to the reply store, with the prompt (which
has the rejected candidates and their counterexamples). Each call has the bound of one ask of its model. -/
def propose (cap : AskCap) (made : Nat) (base : Option Skel.Ask.Cfg) (store : System.FilePath)
    (log : String → IO Unit) (prompt : String) : IO (Except ProposeError (List Quad)) := do
  let caps := (base.map (linkCaps cap)).getD [(cap, { config := "", maxUsd := "0" })]
  match pickLink caps made with
  | none => return .error (.capReached ((caps.map (·.1.asks)).foldl (· + ·) 0))
  | some (i, lc, l) =>
    let id := siteIdOf prompt
    let allowed ← if i == 0 then pure true else do
      pure (!id.isEmpty && (← Skel.Prove.readAllow (base.bind (·.allow))).contains id)
    if !allowed then
      let dir := store.parent.getD "."
      Skel.Prove.escalate (dir / "escalate.jsonl") "ask" id
        [("dir", Lean.toJson dir.toString), ("reason", Lean.toJson "cap"), ("rounds", Lean.toJson made),
         ("prompt", Lean.toJson prompt)]
      log s!"escalate {id}: the first model had its {made} asks; the final model is not allowed ({dir / "escalate.jsonl"})"
      return .error (.capReached made)
    let cfg := base.map fun c => { toLink := { l with maxUsd := usdText lc.perAskMicro }, wide := c.wide : Skel.Ask.Cfg }
    match ← Skel.Ask.askerAt i cfg store log prompt with
    | (some reply, _) => pure ((parseQuadsFree reply).mapError fun e => ProposeError.refused e reply)
    | (none, _) => pure (.error .noReply)

/-- Atoms of the grammar: the prompt shows them, and the tests read them back. -/
def exampleAtoms : List Atom :=
  [ .le (.field ["st", "size", "toNat"]) (.len ["xs"]),
    .forallBelow (.field ["st", "size", "toNat"]) ["st", "pend"] .neNone,
    .inverse (.field ["st", "size", "toNat"]) ["st", "pend"] ["st", "trace"],
    .injOn (.len ["xs"]) ["xs"],
    .permSlice (.len ["xs"]) ["xs"] "xs0",
    .wordSum ["st", "acc"] (.field ["st", "size", "toNat"]) (.len ["xs"]),
    .frameEq ["st", "size"] ]

/-- Linear combinations of features: a measure or a side of an atom may be one. -/
def exampleLin : Lin :=
  { terms := [(2, .field ["st", "size", "toNat"]), (-1, .field ["st", "pend", "toNat"])], const := 0 }

def exampleLins : List Lin :=
  [ exampleLin,
    { terms := [(1, .field ["st", "size", "toNat"]), (1, .len ["xs"])], const := 3 } ]

/-- Measures of the grammar: one feature, a linear combination, and a tuple of two. -/
def exampleMeasures : List Measure :=
  [ .one (.field ["st", "size", "toNat"]),
    .one exampleLin.toFeature,
    .two (.field ["st", "size", "toNat"]) (.field ["st", "pend", "toNat"]) ]

/-- The fixed text that starts the prompt: the task and the rules. -/
private def introLines : List String :=
  [ "You propose candidates for one loop of a Lean 4 model of x86-64 code.",
    "A candidate is a quad: inv (a conjunction of atoms that holds at each head state of the loop), measure (a tuple of features that falls at each step and stays at least zero), bound (optional: the measure at the entry is at most the fuel or a constant) and result (optional: a name or a term).",
    "Each rejected candidate below failed on a sampled state: shown is that state, and why is the reason. A candidate whose file did not elaborate has shown: none, and why is the error of Lean.",
    "Each value is a form of the grammar below, or a free Lean 4 term on one line (section Free terms). Use only the text of this prompt. Do not use tools." ]

/-- The rule of the free terms (HARNESS-LOOP2): the judges are elaboration, the refuter and the closer, not the grammar. -/
private def freeLines : List String :=
  [ "A value that the grammar does not read is a free Lean 4 term. It may use st (the head state), the names of section Context (when there is one) and the constants of the Lean text of this prompt. Do not bind the names st or x in a term (as in fun x => ...): the harness writes each term over the state x of the slots.",
    "inv: a decidable proposition (Prop with a Decidable instance; the refuter evaluates it with decide). Each inv line is one conjunct; the refuter can drop a conjunct that a counterexample blames.",
    "measure: a Nat term, or a tuple (a, b) or (a, b, c) of Nat terms (lexicographic order).",
    "result: a term of the result type of the loop: the value that the loop returns from this head state (see the conclusion of the statement of the loop row).",
    "A free term that does not elaborate gives no verdict; the next prompt shows the error of Lean." ]

/-- The fixed text of the grammar, with the examples of the atoms and of the measures. A machine site has no frame atom (its pool
has none: the state of the loop row has no entry state), so its grammar does not offer one. -/
private def grammarLines (machine : Bool) : List String :=
  [ "Features: a field path, a length (name.length), a count of the elements of a vector that pass a test, a difference (a - b, truncated at 0), a sum, a scaling (2 * a) or a constant.",
    "A feature may also be a linear combination of features: c1 * f1 + c2 * f2 + ... + k, with whole-number constants (negative ones too, as in -1 * a + 4). Its value is the sum over the integers, cut at 0. There is no product of two features and no division.",
    "Atoms: a relation of two features (≤, <, =); a bounded forall; an inverse table; an injective range; a permutation of a slice of a vector against a list; a word equality with wrap-around (w + UInt64.ofNat g = UInt64.ofNat f: the word w plus the feature g is the feature f in UInt64, modulo 2^64)" ++
      (if machine then "." else "; a frame equality (st.f = st₀.f, the entry value of a field)."),
    "Examples of atoms:" ]
  ++ ((exampleAtoms.filter fun a => !(machine && a matches .frameEq _)).map fun a => s!"  {a.text}")
  ++ ["Examples of linear combinations:"]
  ++ exampleLins.map (fun l => s!"  measure: {l.text}")
  ++ ["Examples of measures:"]
  ++ exampleMeasures.map (fun m => s!"  {m.text}")

/-- The fixed text of the reply format: the fenced `quad` blocks and the rules of the reader. -/
private def replyLines : List String :=
  [ "Give at most 4 candidates. Each candidate is one fenced block that starts with the line ```quad.",
    "Inside a block, each line is a key, a colon and a value: inv: <atom or free term> (any number of lines), measure: <measure or free term> (exactly one), result: <name or free term> (at most one), bound: fuel or bound: const <number> (at most one).",
    "A block with a line of another form (no key, an unknown key, a key with no value, two measure lines) refuses the whole reply. Text outside the blocks is ignored." ]

/-- A section: its title line, then its body lines. -/
private def headed (title : String) (body : List String) : List String := s!"## {title}" :: body

/-- The lines of the site: its constant, its state type, its parameters, its step, its fuel and its entry condition. With a
context (`ProposerInput.context`) the entry condition is the hypotheses of the loop row there. -/
private def siteLines (s : LoopSite) (context : Bool) : List String :=
  [ s!"loop: {s.fn}", s!"state type: {s.stateTy}",
    s!"parameters: {", ".intercalate (s.params.map fun (n, t) => s!"{n} : {t}")}",
    "step (one unfolding of the loop: Step.cont gives the next state, Step.exit the result):", s.step,
    s!"fuel at the entry: {s.fuelExpr.getD "none"}",
    if context then "entry condition: the hypotheses of the loop row (section Context)" else s!"entry condition: {s.entry}" ]

/-- The lines of the callees of a site: the rule of a call, then each callee with the constant and the text of its L3 spec. -/
private def calleeLines (cs : List CalleeSpec) : List String :=
  "The step calls a callee. A call does not run the machine code of the callee: it goes on with the result of its L3 spec, the meaning that the goals of the loop give to the call." ::
    cs.flatMap fun c => [s!"callee: {c.name}, L3 spec: {c.run}", c.text]

/-- The lines of the feature names, each with its column of the trace rows. -/
private def featureLines (fs : List Feature) : List String :=
  ((List.range fs.length).zip fs).map fun (i, f) => s!"f{i}: {f.text}"

/-- The line of a trace row `k`: its seed, run, visit, exit and the feature values in the order of the columns. -/
private def rowLine (k : Nat) (v : Visit) : String :=
  s!"row {k}: seed {v.seed}, run {v.index}, visit {v.visit}, exit {(v.exit.map Exit.word).getD "none"}, values [{", ".intercalate (v.features.map toString)}]"

/-- The lines of the atoms that passed the trace pass. -/
private def passedLines (as : List Atom) : List String :=
  if as.isEmpty then ["none"] else as.map fun a => s!"- {a.text}"

/-- The word of a bound, as the reply gives it. -/
private def boundWord : Bound → String
  | .fuel => "fuel"
  | .const k => s!"const {k}"

/-- The lines of a quad, in the form of the reply. -/
private def quadLines (q : Quad) : List String :=
  q.inv.map (fun a => s!"inv: {a.text}") ++ [s!"measure: {q.measure.text}"]
    ++ q.result.toList.map (fun r => s!"result: {r}")
    ++ q.bound.toList.map (fun b => s!"bound: {boundWord b}")

/-- The lines of a rejected candidate `i`: the quad, then its counterexample. -/
private def rejectedLines (i : Nat) (r : Rejected) : List String :=
  s!"Rejected candidate {i}:" :: (quadLines r.quad ++ [s!"shown: {r.shown}", s!"why: {r.why}"])

/-- The lines of a refused reply `i`: the reason, then the reply (cut to `refusalChars`). -/
private def refusalLines (i : Nat) (r : Refusal) : List String :=
  [s!"Refused reply {i}:", s!"why: {r.why}"] ++
    (if r.reply.isEmpty then [] else ["reply:", (r.reply.take refusalChars).toString])

/-- The prompt text. The sections are separated by an empty line. Each section is headed by its title. The section of the
refused replies is there only when a reply was refused. -/
def promptText (x : ProposerInput) : String :=
  let shown := x.rows.take promptRows
  let rejected :=
    if x.rejected.isEmpty then ["none"]
    else ((List.range x.rejected.length).zip x.rejected).flatMap fun (i, r) => rejectedLines (i + 1) r
  let refused := ((List.range x.refused.length).zip x.refused).flatMap fun (i, r) => refusalLines (i + 1) r
  let blocks : List (List String) :=
    [ introLines,
      headed "Loop site" (siteLines x.site !x.context.isEmpty) ] ++
    (if x.context.isEmpty then [] else [headed "Context" x.context]) ++
    (if x.site.callees.isEmpty then [] else [headed "Callees" (calleeLines x.site.callees)]) ++
    [ headed "Grammar" (grammarLines (x.site.kind matches .machine _)),
      headed "Free terms" freeLines,
      headed "Feature names" (featureLines x.features),
      headed "Trace rows" (((List.range shown.length).zip shown).map fun (k, v) => rowLine (k + 1) v),
      headed "Atoms that passed the trace pass" (passedLines x.passed),
      headed "Rejected candidates" rejected ] ++
    (if refused.isEmpty then [] else [headed "Refused replies" refused]) ++
    [ headed "Reply format" replyLines ]
  "\n\n".intercalate (blocks.map fun ls => "\n".intercalate ls) ++ "\n"

end Skel.Discover
