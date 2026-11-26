import Skel.Types
import Skel.Parse
import Skel.Prompt
import Skel.Houdini
import Skel.Prove

/-! The proposers of the two ladders of the skeleton (`docs/one-way-lift-skeleton-plan-20261118.md`, section 5). Each
proposer is pure: it reads the obligation and its history, and gives the next candidate, or `none`. -/

namespace Skel

/-- The closing texts of 5.1, item 2, in order. -/
def closingTexts : List String :=
  ["by intros; exact ⟨_, rfl⟩", "by simp_all", "by grind", "by bv_omega", "by bv_decide"]

/-- Whether a proof text is an attempt of the history. -/
def triedText (c : String) (h : History) : Bool :=
  h.attempts.any fun a => match a.candidate with
    | .proof _ t => t == c
    | .triple _ _ | .ask _ => false

/-- Whether a triple is an attempt of the history, with any rung and any result. -/
def triedTriple (t : Triple) (h : History) : Bool :=
  h.attempts.any fun a => match a.candidate with
    | .triple _ u => u == t
    | .proof _ _ | .ask _ => false

/-- Whether a triple is an attempt of the history with the result `cti`. -/
def ctiOn (t : Triple) (h : History) : Bool :=
  h.attempts.any fun a => match a.candidate, a.result with
    | .triple _ u, .refuted (.cti _) => u == t
    | _, _ => false

/-- The first text of `cs` that is not an attempt of the history. -/
def firstNew (cs : List String) (h : History) : Option String :=
  cs.find? fun c => !triedText c h

/-- The deterministic texts of an obligation: `by intros; lift_block` for a block. A link row or a contract row has its text in
`det` (`Gen.linkText` of the names of its function, `generateUpper`). -/
def detTexts (ob : Obligation) : List String :=
  match ob.origin with
  | .block _ => ["by intros; lift_block"]
  | _ => []

/-- Rung 1 of the proof ladder: the generated text of the id (`det`), then the deterministic text, each once. -/
def liftBlock (det : List (ObId × String)) : Proposer String := fun ob h =>
  firstNew ((det.filter (·.1 == ob.id)).map (·.2) ++ detTexts ob) h

/-- Rung 2 of the proof ladder: the closing texts, in order. -/
def closing : Proposer String := fun _ h => firstNew closingTexts h

/-- Rung 3 of the proof ladder: the recorded replies of the name of the obligation, in order. -/
def model (replies : List (String × String)) : Proposer String := fun ob h =>
  firstNew ((replies.filter fun r => r.1 == ob.id.name).map (·.2)) h

/-- Rung 4 of the proof ladder: the stored proof text of the obligation, once. -/
def replay (store : List (ObId × String)) : Proposer String := fun ob h =>
  match store.find? fun p => p.1 == ob.id with
  | some (_, text) => firstNew [text] h
  | none => none

/-- Rung 5 of the proof ladder (R9): the proof of the newest reply of the prove run in the history, once. The reply is the
answer to the ask with `Prove.candidate`; a reply with no proof, a reply that does not read, and no reply give none. -/
def proveRung : Proposer String := fun _ h =>
  let reply := h.attempts.findSome? fun a =>
    match a.candidate, a.result with
    | .ask p, .answered (some r) => if p == Prove.marker then Prove.Reply.decode? r else none
    | _, _ => none
  (reply.bind (·.proof)).bind fun t => firstNew [t] h

/-- Rung 1 of the invariant ladder: the first template of `ts` that is not an attempt of the history. A template is
given only when each template before it is an attempt with the verdict `cti`. -/
def templates (ts : List Triple) : Proposer Triple := fun _ h =>
  let rec go : List Triple → Option Triple
    | [] => none
    | t :: rest => if !triedTriple t h then some t else if ctiOn t h then go rest else none
  go ts

/-- Rung 1 of the invariant ladder for generated templates (`Gen.loopTemplates`): the first triple of `ts` that is not an
attempt of the history, whatever the verdicts of the triples before it. The generated triples are not ordered from weak to
strong, so the verdict `real` of one says nothing of the next. -/
def eachTemplate (ts : List Triple) : Proposer Triple := fun _ h => ts.find? (!triedTriple · h)

/-- Rung 2 of the invariant ladder: the hand triple, once. -/
def replayTriple (t : Triple) : Proposer Triple := fun _ h =>
  if triedTriple t h then none else some t

/-- Rung of the discovery ladder (`Skel/Discover/Ladder.lean`): the triple of the quad that the discovery closed, once. The
discovery runs before the loop; this proposer only gives its result to the loop, which refutes and checks it as any triple. -/
def discoverRung (t : Triple) : Proposer Triple := replayTriple t

/-- The verdict that the history has for the triple of the atoms `s` with the measure `m` and the result `r`, from any rung. -/
def houdiniVerdict (h : History) (m r : String) (s : List Houdini.Atom) : Option Verdict :=
  let t : Triple := { inv := Houdini.conj s, measure := m, result := r }
  h.attempts.findSome? fun a =>
    match a.candidate, a.result with
    | .triple _ u, .refuted v => if u == t then some v else none
    | _, _ => none

/-- Rung 2 of the invariant ladder (D18): the Houdini triple. For each measure and result of the template rule in order, the
drop loop of `Houdini.next` reads the verdicts of the history and gives the next conjunction of atoms to refute; the invariant of
the triple is that conjunction. A tail for which the loop ends gives the next tail. No tail, or an end of the loop for each tail,
gives none. -/
def houdiniRung (spec : Houdini.Spec) : Proposer Triple := fun _ h =>
  spec.tails.findSome? fun (m, r) =>
    (Houdini.next (houdiniVerdict h m r) spec.atoms.length spec.atoms).map fun s =>
      { inv := Houdini.conj s, measure := m, result := r }

/-- The texts of the prompt of the model rung that the row does not carry: the L2+ text, the L3 text and the loop rule
text. The slot statement is the statement of the loop row. -/
structure PromptTexts where (l2PlusText l3Text loopRule : String)

/-- The number of lines of the Lean errors, other than unsolved goals, that go into a prompt. -/
def errorLineLimit : Nat := 20

/-- The number of lines of the unsolved goals that go into a prompt. -/
def goalLineLimit : Nat := 120

/-- The number of hypotheses of a goal, counted from the goal, that go into a prompt. -/
def hypLimit : Nat := 6

/-- The number of lines of the goal itself (`⊢` and its continuation lines) that go into a prompt. -/
def goalConclusionLimit : Nat := 12

/-- A hypothesis with its continuation lines (the lines that start with a space) is one entry. -/
private def hypEntries (ctx : List String) : List (List String) :=
  ctx.foldl (fun acc l =>
    match acc with
    | last :: rest => if l.startsWith " " then (last ++ [l]) :: rest else [l] :: acc
    | [] => [[l]]) [] |>.reverse

/-- The lines of one unsolved goal: its `case` and `unsolved goals` lines, the last `hypLimit` hypotheses and the whole of the
conclusion (`⊢` with its continuation lines), cut at `goalConclusionLimit` lines. The hypotheses far from the goal are cut:
the slot statement already gives them. -/
private def goalLines (block : List String) : List String :=
  let ctx := block.takeWhile (!·.startsWith "⊢")
  let concl := block.dropWhile (!·.startsWith "⊢")
  let (heads, hyps) := ctx.partition fun l => l.startsWith "case " || l == "unsolved goals"
  heads ++ ((hypEntries hyps).reverse.take hypLimit).reverse.flatten ++ concl.take goalConclusionLimit

/-- The blocks of a message: the runs of lines between empty lines. -/
private def blocksOf (ls : List String) : List (List String) :=
  (ls.foldr (fun l acc =>
    if l.isEmpty then [] :: acc
    else match acc with
      | b :: rest => (l :: b) :: rest
      | [] => [[l]]) [[]]).filter (!·.isEmpty)

/-- Whether the message is a list of unsolved goals: a line starts with `⊢`. -/
private def hasGoal (ls : List String) : Bool := ls.any (·.startsWith "⊢")

/-- The prompt lines of one error message: an error with goals gives each goal in the short form of `goalLines`, an error with no
goal gives its lines. The first value says whether the lines are goal lines. -/
def errorMessageLines (e : String) : Bool × List String :=
  let ls := e.splitOn "\n"
  if hasGoal ls then (true, ((blocksOf ls).flatMap fun b => if hasGoal b then goalLines b else b).take goalLineLimit)
  else (false, ls)

/-- The tried triples of the history with their refuter verdicts, oldest first. -/
def triedVerdicts (h : History) : List (Triple × Verdict) :=
  h.attempts.reverse.filterMap fun a =>
    match a.candidate, a.result with
    | .triple _ t, .refuted v => some (t, v)
    | _, _ => none

/-- The lines of the errors of the newest failed check of the history. An error with unsolved goals gives each goal
(`goalLines`); the other errors give their first `errorLineLimit` lines together. -/
def errorLines (h : History) : List String :=
  match h.attempts.findSome? fun a => match a.result with | .checked (.failed es) => some es | _ => none with
  | some es =>
    let (_, out) := es.foldl (init := (errorLineLimit, ([] : List String))) fun (left, acc) e =>
      match errorMessageLines e with
      | (true, ls) => (left, acc ++ ls)
      | (false, ls) => (left - (ls.take left).length, acc ++ ls.take left)
    out
  | none => []

/-- The triples of the replies in the history, oldest reply first, at most 4 for each reply. A reply that is `none` gives
no triple. -/
def repliedTriples (h : History) : List Triple :=
  (h.attempts.reverse.filterMap fun a =>
    match a.candidate, a.result with
    | .ask _, .answered (some reply) => some reply
    | _, _ => none).flatMap parseTriples

/-- Rung 2 of the invariant ladder: the first triple of the replies in the history that is not an attempt; when there is
none, the ask with the prompt for this history. The loop gives the ask only while the count of asks of the history is
below the limit of the configuration. -/
def modelRung (texts : PromptTexts) : TripleProposer := fun ob h =>
  match (repliedTriples h).find? fun t => !triedTriple t h with
  | some t => some (.triple t)
  | none =>
    some (.ask (triplePrompt
      { l2PlusText := texts.l2PlusText, l3Text := texts.l3Text, slot := ob.statement, loopRule := texts.loopRule,
        history := triedVerdicts h, errors := errorLines h }))

/-- A proposer of triples as a proposer of proposals. -/
def liftTriple (p : Proposer Triple) : TripleProposer := fun ob h => (p ob h).map .triple

/-- The two ladders of an obligation: the proof rungs and the triple rungs, in order. `ts` are the template triples; an
empty list gives a template rung that gives nothing. `det` are the generated texts of the proofs (`Generated.det`). `houdini` is
the Houdini rung between the templates and the model; none gives a ladder with no Houdini rung. `discovered` is the triple of the
discovery ladder: the discover rung follows the templates; none gives a ladder with no discover rung. -/
def ladders (ts : List Triple) (texts : PromptTexts) (replies : List (String × String))
    (store det : List (ObId × String)) (t : Triple) (houdini : Option Houdini.Spec := none) (prove : Bool := false)
    (discovered : Option Triple := none) : Ladders :=
  { proof := [(.liftBlock, liftBlock det), (.closing, closing), (.model, model replies), (.replay, replay store)],
    prove := prove,
    triple := [(.template, liftTriple (templates ts))] ++
      (discovered.map fun d => (InvRung.discover, liftTriple (discoverRung d))).toList ++
      (houdini.map fun spec => (.houdini, liftTriple (houdiniRung spec))).toList ++
      [(.model, modelRung texts), (.replay, liftTriple (replayTriple t))] }

/-! ## The sampler rung (D20, step 2)

When the generated sampler of a function fails, a model proposes the two sampler definitions (`docs/one-way-lift-g3-plan-20261118.md`,
5.6). The functions here are pure. The IO part (the model call through `leantools ask`, the run of the refuter on the reply)
gives them the reply text and the evidence of the run. -/

/-- The number of admitted samples that must satisfy the precondition (5.6, check (a)). -/
def samplerCount : Nat := 200

/-- The least number of mutants that the samples must show as `real` (5.6, check (c)). -/
def minCaught : Nat := 1

/-- The reply of the model: the Lean text of `refuteAdmitted` and of `refuteFree`. -/
structure SamplerReply where (admitted free : String) deriving DecidableEq, Repr

/-- The two definitions of a reply, as one text. -/
def SamplerReply.text (r : SamplerReply) : String := r.admitted ++ "\n\n" ++ r.free

/-- Why a reply is refused. -/
inductive SamplerReason where
  /-- The reply has no usable code: what is wrong with it. -/
  | noCode (what : String)
  /-- The code does not compile: the errors. -/
  | compile (errors : List String)
  /-- The sampler gave fewer admitted samples than `samplerCount`. -/
  | tooFewSamples (got : Nat)
  /-- An admitted sample fails the precondition: its index, whether `WF` holds, whether `C` holds, and its text. -/
  | outsidePrecondition (index : Nat) (wf pre : Bool) (shown : String)
  /-- The claim has the verdict `v`, not `pass`. -/
  | claimNotPass (v : Verdict)
  /-- The samples catch fewer than `minCaught` of the mutants: the number tried. -/
  | noMutantCaught (tried : Nat)
  deriving DecidableEq, Repr

/-- The check of one admitted sample (5.1, step 4): its index, the heap check `WF`, the check `C` of the statement, and its text. -/
structure SampleCheck where (index : Nat) (wf pre : Bool) (shown : String) deriving DecidableEq, Repr

/-- The result of the refuter on one mutant, with the name of its form. -/
structure MutantRun where (form : String) (verdict : Verdict) deriving DecidableEq, Repr

/-- A mutant is caught when the verdict is `real`. -/
def MutantRun.caught (m : MutantRun) : Bool :=
  match m.verdict with
  | .real _ => true
  | .pass _ | .cti _ | .unknown _ => false

/-- The evidence of the run of a reply: the check of each admitted sample, the verdict of the claim, and the run of each mutant. -/
structure SamplerEvidence where (samples : List SampleCheck) (claim : Verdict) (mutants : List MutantRun)

/-- An accepted reply: the number of admitted samples, and the run of each mutant (each result is recorded). -/
structure SamplerAccepted where (samples : Nat) (mutants : List MutantRun) deriving DecidableEq, Repr

/-- The number of mutants that the samples catch. -/
def SamplerAccepted.caught (a : SamplerAccepted) : Nat := (a.mutants.filter (·.caught)).length

/-- The lines of the declaration that starts with the first line: up to the next line that starts in column 0. -/
private def declLines : List String → List String
  | [] => []
  | l :: ls =>
    l :: ls.takeWhile fun x => x.trimAscii.toString == "" || (x.toList.head?.map Char.isWhitespace).getD true

/-- The lines without the empty lines at the end. -/
private def dropBlankEnd (ls : List String) : List String :=
  (ls.reverse.dropWhile fun x => x.trimAscii.toString == "").reverse

/-- Whether the line starts the definition `name`. -/
private def startsDef (name l : String) : Bool :=
  l.startsWith s!"def {name}" &&
    match (l.toList.drop (4 + name.length)).head? with
    | none => true
    | some c => c == ' ' || c == ':' || c == '('

/-- The one definition `name` of the lines, or what is wrong. -/
private def defOf (lines : List String) (name : String) : Except SamplerReason String :=
  let starts := (List.range lines.length).filter fun i => startsDef name (lines.getD i "")
  match starts with
  | [i] => .ok ("\n".intercalate (dropBlankEnd (declLines (lines.drop i))))
  | [] => .error (.noCode s!"no definition of {name} in a lean block")
  | _ => .error (.noCode s!"the definition of {name} is more than once in the lean blocks")

/-- The reply of the model: the definitions `refuteAdmitted` and `refuteFree` in the closed `lean` blocks. Each must be there
once. Lines outside the definitions are ignored. -/
def parseSamplerReply (reply : String) : Except SamplerReason SamplerReply := do
  let lines := (reply.replace "\r\n" "\n").splitOn "\n"
  let code := ((fencedBlocks lines).filter fun (info, _) => info == "lean" || info == "lean4").flatMap (·.2)
  let admitted ← defOf code "refuteAdmitted"
  let free ← defOf code "refuteFree"
  pure { admitted, free }

/-- The acceptance checks of 5.6, on the evidence of the run of a reply. Order: (a) each admitted sample passes `WF` and `C`,
and there are `samplerCount` of them; (b) the claim gives `pass`; (c) at least `minCaught` mutants give `real`. The first check
that fails gives the reason. -/
def acceptSampler (ev : SamplerEvidence) : Except SamplerReason SamplerAccepted := do
  match ev.samples.find? fun s => !(s.wf && s.pre) with
  | some s => throw (.outsidePrecondition s.index s.wf s.pre s.shown)
  | none => pure ()
  unless samplerCount ≤ ev.samples.length do throw (.tooFewSamples ev.samples.length)
  match ev.claim with
  | .pass _ => pure ()
  | v => throw (.claimNotPass v)
  unless minCaught ≤ (ev.mutants.filter (·.caught)).length do throw (.noMutantCaught ev.mutants.length)
  pure { samples := ev.samples.length, mutants := ev.mutants }

/-- The text of a verdict for a prompt. -/
private def verdictText : Verdict → String
  | .pass n => s!"pass ({n} samples)"
  | .real c => s!"real (shown: {c.shown}; why: {c.why})"
  | .cti c => s!"cti (shown: {c.shown}; why: {c.why})"
  | .unknown why => s!"unknown ({why})"

/-- The text of a reason, for the next prompt. -/
def SamplerReason.render : SamplerReason → String
  | .noCode what => s!"The reply has no usable code: {what}."
  | .compile errors => "The sampler does not compile:\n" ++ "\n".intercalate errors
  | .tooFewSamples got => s!"The sampler gives {got} admitted samples; {samplerCount} are needed."
  | .outsidePrecondition i wf pre shown =>
    s!"Admitted sample {i} is outside the precondition (WF {if wf then "holds" else "fails"}, C {if pre then "holds" else "fails"}). The sample: {shown}"
  | .claimNotPass v => s!"The claim does not pass on the admitted samples: verdict {verdictText v}."
  | .noMutantCaught tried => s!"The samples show a wrong result for none of the {tried} mutants; at least {minCaught} is needed."

/-- A failed try of the sampler rung: the code that failed (the definitions of the reply, or the reply when it did not parse),
and why. -/
structure SamplerTry where (code : String) (reason : SamplerReason)

/-- The texts of the first prompt of the sampler rung: the L2+ text, the precondition, the generated sampler that failed with
its error, and the mutants (the form and the `blocksP` text of each). -/
structure SamplerBase where
  (l2PlusText precondition generated generatedError : String)
  (mutants : List (String × String))

/-- The sampler rung: the prompt of the next ask, or `none` when `limit` asks are made. The tries are newest first. The failing
sampler of the prompt is the newest try with its reason, or the generated sampler with its error when there is no try. -/
def samplerRung (base : SamplerBase) (limit : Nat) (tries : List SamplerTry) : Option String :=
  if tries.length < limit then
    let (failing, error) := match tries with
      | t :: _ => (t.code, t.reason.render)
      | [] => (base.generated, base.generatedError)
    some (samplerPrompt
      { l2PlusText := base.l2PlusText, precondition := base.precondition, failing, error, mutants := base.mutants })
  else none

end Skel
