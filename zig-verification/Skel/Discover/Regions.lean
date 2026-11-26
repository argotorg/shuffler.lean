import Skel.Discover.Joint
import Skel.Gen.Regions
import Skel.Render
import Skel.Io
import Lift.Sem.Cut

/-! The production checks of a joint region map. Each checked local row has the whole map in its statement.
Only a checked proof of the generated joint row can close the map. -/

namespace Skel.Discover.Regions

open Skel Skel.Gen Skel.Discover Joint
open System (FilePath)

/-- The generated function and its joint row, with the settings of its Lean checks. -/
structure Context where
  plan : UpperPlan
  shape : StmtShape
  callees : List Callee
  header : Header
  model : String
  row : Obligation
  gate : Gate
  limitMs : Nat
  dir : FilePath
  procs : Nat := 2

/-- Proofs for the local steps and the two boundaries of a certificate. -/
structure Proofs where
  steps : List (String × String)
  entry : String
  result : String

/-- The saved proposal format. Each head has one Nat rank and a proof of its local region statement. -/
structure HeadProposal where
  head : String
  inv : List String
  rank : String
  result : String
  proof : String
  deriving Lean.ToJson, Lean.FromJson

structure ProposalText where
  heads : List HeadProposal
  entry : String
  result : String
  deriving Lean.ToJson, Lean.FromJson

/-- A proposal has a complete candidate map before any Lean check starts. -/
structure Proposal where private mk ::
  map : CandidateMap
  proofs : Proofs

/-- Parse the saved proposal at its boundary. Invalid maps or missing proofs start no Lean checks. -/
def Proposal.parse (heads : List String) (j : Lean.Json) : Except String Proposal := do
  let p : ProposalText ← Lean.fromJson? j
  let raw := p.heads.map fun h =>
    (h.head, { inv := h.inv.map Atom.free, measure := freeMeasure h.rank, bound := none, result := some h.result : Quad })
  let map ← CandidateMap.parse heads raw
  let nonblank (s : String) := s.toList.any (!·.isWhitespace)
  for h in p.heads do
    unless nonblank h.proof do throw s!"head {h.head}: blank local proof"
  unless nonblank p.entry do throw "blank entry proof"
  unless nonblank p.result do throw "blank result proof"
  pure ⟨map, { steps := p.heads.map (fun h => (h.head, h.proof)), entry := p.entry, result := p.result }⟩

/-- The external proposer fills these fields and saves the file next to the request. -/
def proposalExample (heads : List String) : ProposalText :=
  { heads := heads.map fun head => { head, inv := [], rank := "0", result := "0", proof := "by\n  sorry" },
    entry := "sorry", result := "sorry" }

/-- Other generated callee statements are context only. The file may use only checked theorem declarations as facts. -/
def calleeRowContext (rows : List Obligation) : String :=
  let rows := rows.filter fun ob =>
    let n := ob.id.name
    (n.splitOn ".").length > 1 && !n.startsWith "block." && !n.startsWith "loop." &&
      (n.splitOn ".block.").length == 1 && (n.splitOn ".loop.").length == 1
  if rows.isEmpty then "" else
    "\n-- Generated callee statements. These are open goals unless this file contains a checked theorem.\n" ++
      "-- These comments add no hypotheses.\n" ++
      "\n".intercalate (rows.flatMap fun ob =>
        (s!"{ob.id.name} : {ob.statement}".splitOn "\n").map ("-- " ++ ·)) ++ "\n"

private def stateTy (c : Context) : String := c.plan.stateType

private def outputTy (c : Context) : String :=
  match c.plan.kind with
  | .heap => "Heap"
  | .both => "(UInt64 × Heap)"
  | .value => "UInt64"

def inputName (c : Context) : String := freshName c.shape c.plan "a"
def resultName (c : Context) : String := freshName c.shape c.plan "y"
private def args (c : Context) : List String := c.plan.params.map (·.name.s) ++ ["frame"] ++ c.shape.form.names
def names (c : Context) : List String := args c ++ [inputName c, resultName c]

def binders (c : Context) : List String :=
  c.plan.params.map binderText ++ ["(frame : Heap)"] ++ c.shape.form.binderTexts ++
    [s!"({inputName c} : In2p)", c.shape.resultBinder (resultName c)]

def premises (c : Context) : String :=
  s!"SimArr {" ".intercalate (args c)} {inputName c} → " ++
    s!"{c.shape.returnsText (resultName c)} → "

private def invText (q : HeadCandidate) : String :=
  if q.inv.isEmpty then "True" else " ∧ ".intercalate (q.inv.map fun a => s!"({a.text})")

/-- The invariant, scalar rank and predicted output as functions on all labels. Other labels have a false invariant. -/
def mapTerms (c : Context) (m : CandidateMap) : String × String × String :=
  let funText (ty : String) (body : HeadCandidate → String) (fallback : String) :=
    s!"(fun (l : Lbl) (st : {stateTy c}) => (match l with\n" ++
      "\n".intercalate (m.entries.map fun (h, q) => s!"  | .{h} => {body q}") ++
      s!"\n  | _ => {fallback} : {ty}))"
  let inv := funText "Prop" (fun q => s!"st.input = {inputName c} ∧ ({invText q})") "False"
  let rank := funText "Nat" (·.rank.text) "0"
  let fallback := (m.entries.head?.map (·.2.out)).getD "0"
  let out := funText (outputTy c) (·.out) fallback
  (inv, rank, out)

def localName (c : Context) (head : String) : String :=
  let i := ((regionLabels c.plan).zipIdx.find? (·.1 == head)).map (·.2) |>.getD 0
  s!"region_step_{i}"

/-- A region's statement includes every head's candidate, so all cross-head edges use the same maps. -/
def localRow (c : Context) (m : CandidateMap) (head : String) : Except String Obligation := do
  unless m.names == regionLabels c.plan do throw "the map does not have the generated region heads"
  unless m.names.contains head do throw s!"no candidate for region {head}"
  let (inv, rank, out) := mapTerms c m
  let callee := if c.callees.isEmpty then "noCall" else calleeRel c.callees
  let body :=
    s!"∀ {" ".intercalate (binders c)}, {premises c}\n" ++
    s!"  ∀ st, {inv} .{head} st →\n" ++
    s!"    ∃ e, (blocksP.cut regionHeads).Returns {callee} (.block .{head}) st e ∧\n" ++
    s!"      Lift.Sem.CutExit.Progress {inv} {rank} {out} .{head} st e"
  pure { id := ⟨c.plan.fn, localName c head⟩, cls := .refine, origin := .unit,
         statement := body, deps := c.row.deps, claim := .none }

private def indent (s : String) : String := "\n".intercalate ((s.splitOn "\n").map ("    " ++ ·))

/-- Build the joint certificate from checked local theorems. The entry and result remain separate proof goals. -/
def certificate (c : Context) (m : CandidateMap) (p : Proofs) : String :=
  let (inv, rank, out) := mapTerms c m
  let applications := m.names.map fun h =>
    s!"exact {localName c h} {" ".intercalate (names c)} hs hy st hi"
  "\n".intercalate
    (["by", s!"  intro {" ".intercalate (names c)} hs hy",
      s!"  refine ⟨{inv}, {rank}, {out}, ?_, ?_, ?_⟩",
      "  ·", indent p.entry,
      "  · intro l st hi", "    cases l <;> first"] ++
      applications.map ("    | " ++ ·) ++ ["    | exact False.elim hi", "  ·", indent p.result])

private def check (c : Context) (model : String) (answers : List String) (ob : Obligation) (proof : String) : IO Checked := do
  let (outcome, ms) ← Io.checker c.dir c.gate
    { name := s!"{c.header.namespace_}.{ob.id.name}", limitMs := c.limitMs,
      text := Skel.checkFile c.header model answers ob proof }
  pure ⟨proof, outcome, ms⟩

/-- Concrete Lean checks for `runMaps`. A local acceptance never substitutes for the final generated row check. -/
def env (c : Context) (proofs : CandidateMap → Proofs) : Joint.Env :=
  { heads := regionLabels c.plan, procs := c.procs,
    regionCheck := fun m h => do
      match localRow c m h with
      | .error e => pure ⟨"", .failed [e], 0⟩
      | .ok row =>
        match (proofs m).steps.lookup h with
        | none => pure ⟨"", .failed [s!"no proof for region {h}"], 0⟩
        | some p => check c c.model [] row p,
    compose := fun m checked => do
      let answers := checked.filterMap fun (h, chk) =>
        (localRow c m h).toOption.map fun ob => theoremText ob.id.name ob.statement chk.proof
      let proof := Proof.text { helpers := "\n\n".intercalate answers, proof := certificate c m (proofs m) }
      check c c.model [] c.row proof }

/-- Check the candidate maps against the generated local and joint rows. -/
def run (c : Context) (proofs : CandidateMap → Proofs) (maps : List (List (String × Quad))) : IO Joint.Result :=
  runMaps (env c proofs) maps

/-- The saved proposal uses the same local checks and the same final generated-row check as in-memory maps. -/
def runProposal (c : Context) (p : Proposal) : IO Joint.Result :=
  run c (fun _ => p.proofs) [p.map.entries.map fun (h, q) =>
    (h, { inv := q.inv, measure := .one q.rank, bound := none, result := some q.out })]

end Skel.Discover.Regions
