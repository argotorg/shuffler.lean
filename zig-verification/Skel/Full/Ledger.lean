import Lean.Data.Json
import Skel.Report.Level3Pilot

/-! The one ledger of `skel full` (task FULL-DRV, W9 and W10): each obligation of each function, with its status, rung, model,
cost and run directory. It is made from the results of the level 3 driver (`FnRes`) and the facts of the run across functions
(the statement of each function, its callees that are open). The JSON file and the Markdown summary are pure functions of it.

The statuses:
- `closed`: Lean accepted the check of the row (the gate admits its axioms); for a statement, the function has one;
- `open`: the row was generated and not closed (its first error);
- `noStatement`: the function has no statement, so the upper chain does not run;
- `notGenerated`: the generator did not make the row (its cause);
- `calleeOpen`: the row uses the L2 contract of a callee that is not closed. A row of a caller other than a block row is
  `calleeOpen` while a callee is open, also when its own check passed: the caller's proof is counted only when its callees close. -/

namespace Skel.Full

open Lean (Json)
open Skel.Report.Level3

/-- The kind of an obligation: a row of the chain, a loop row, or the statement of the function. -/
inductive Kind where
  | row | loop | statement
  deriving DecidableEq, Repr

def Kind.text : Kind → String
  | .row => "row" | .loop => "loop" | .statement => "statement"

/-- The status of an obligation (see the module text). -/
inductive Status where
  | closed | «open» | noStatement | notGenerated | calleeOpen
  deriving DecidableEq, Repr

def Status.text : Status → String
  | .closed => "closed" | .«open» => "open" | .noStatement => "no statement" | .notGenerated => "not generated"
  | .calleeOpen => "callee open"

def Status.all : List Status := [.closed, .«open», .noStatement, .notGenerated, .calleeOpen]

/-- One obligation. `rung` is the rung that closed it (empty when it is not closed); `costMicro` is in millionths of a USD;
`frozen` is the frozen file of a dry run of the prover (empty: none). -/
structure Entry where
  fn : String
  name : String
  kind : Kind
  status : Status
  rung : String := ""
  model : String := ""
  costMicro : Nat := 0
  runDir : String := ""
  detail : String := ""
  frozen : String := ""
  deriving DecidableEq, Repr

/-- Where the statement of a function comes from. -/
inductive Source where
  | trusted (module : String) | moved (module : String) | proposed (module : String) | none
  deriving DecidableEq, Repr

def Source.text : Source → String
  | .trusted _ => "trusted" | .moved _ => "moved" | .proposed _ => "proposed" | .none => "none"

def Source.module? : Source → Option String
  | .trusted m | .moved m | .proposed m => some m
  | .none => Option.none

/-- The cause of the upper rows of a function with no statement. -/
def noStatementCause : String := "no statement: the upper chain does not run"

/-- The cause of the upper rows of a function with a callee that is open. -/
def calleeOpenCause (cs : List String) : String := s!"callee open: {", ".intercalate cs}"

/-- Whether a row name is a block row of the function (not a callee row `F.<label>`). -/
def isBlockRow (name : String) : Bool := name.startsWith "block."

/-- The entry of a row `r` of the function `fn`, whose open callees are `openCallees`. -/
def entryOf (fn : String) (openCallees : List String) (r : ObRow) : Entry :=
  let kind : Kind := if r.name.startsWith "loop." then .loop else .row
  let base : Entry := { fn, name := r.name, kind, status := .«open», model := r.model, costMicro := r.costMicro, runDir := r.runDir }
  let calleeHeld := !openCallees.isEmpty && !isBlockRow r.name
  match r.st with
  | .closed how rung =>
    if calleeHeld then
      { base with status := .calleeOpen, rung,
                  detail := s!"{calleeOpenCause openCallees}; its own check passed ({St.text (.closed how rung)}), not counted" }
    else { base with status := .closed, rung, detail := St.text (.closed how rung) }
  | .«open» e =>
    if calleeHeld then { base with status := .calleeOpen, detail := s!"{calleeOpenCause openCallees}; {e}" }
    else { base with detail := e }
  | .notGenerated c =>
    if c == noStatementCause then { base with status := .noStatement, detail := c }
    else if c.startsWith "callee open" || calleeHeld then { base with status := .calleeOpen, detail := c }
    else { base with status := .notGenerated, detail := c }

/-- The entry of the statement of the function `fn`. -/
def statementEntry (fn : String) (s : Source) : Entry :=
  match s.module? with
  | some m => { fn, name := "statement", kind := .statement, status := .closed, rung := s!"statement/{s.text}", detail := m }
  | Option.none => { fn, name := "statement", kind := .statement, status := .noStatement, detail := "no moved, proposed or trusted statement" }

/-- The result of one function in the run: its label, its statement, its callees that are open, its result, and whether its
L2 rows are closed with those of all its callees (`l2Closed`). -/
structure FnOut where
  label : String
  source : Source
  callees : List String
  openCallees : List String
  res : FnRes
  l2Closed : Bool
  /-- The module of the function (`Lift.Shuffler.Proved.<F>` or the test root), when it was written and built. -/
  module : Option String := Option.none
  /-- A closed semantic summary exported by a built module. -/
  semanticSummary : Bool := false
  deriving Repr

/-- The entries of a function: its statement, then its rows. -/
def entriesOf (o : FnOut) : List Entry :=
  statementEntry o.label o.source :: o.res.rows.map (entryOf o.label o.openCallees)

/-- Whether the L2 rows (block rows and `decompiles_l2`) of a result are all closed, and there is at least one. -/
def l2RowsClosed (r : FnRes) : Bool :=
  let l2 := r.rows.filter fun row => isBlockRow row.name || row.name == "decompiles_l2"
  !l2.isEmpty && l2.all fun row => row.st matches .closed ..

/-- The entries with their frozen files: `frozen` gives the path of the frozen file of a row of a function, if any. -/
def withFrozen (frozen : String → String → Option String) (es : List Entry) : List Entry :=
  es.map fun e => match frozen e.fn e.name with
    | some p => { e with frozen := p }
    | Option.none => e

/-! ## The composition -/

/-- The composition of the run: `proved` with the axioms of `final` of the top function when every function's `final` closes,
else the functions that block it with the state of their `final`. -/
inductive Composition where
  | proved (axioms : List String)
  | blocked (by_ : List (String × String))
  deriving DecidableEq, Repr

/-- The composition of the outputs `os` with the top function `top` (`solidity_shuffler_shuffle`). -/
def compositionOf (top : String) (os : List FnOut) : Composition :=
  let blockers := os.filterMap fun o =>
    match o.source, o.res.final with
    | .none, _ => some (o.label, "no statement")
    | _, .closed _ => if o.openCallees.isEmpty then none else some (o.label, calleeOpenCause o.openCallees)
    | _, f => some (o.label, shortError f.text)
  match blockers, ((os.find? (·.label == top)).map (·.res.final) : Option FinalSt) with
  | [], some (FinalSt.closed axs) => .proved axs
  | [], _ => .blocked [(top, "the top function is not in the run")]
  | bs, _ => .blocked bs

/-! ## The files -/

/-- A cost in USD with 6 decimals. -/
def usdOf (micro : Nat) : String := usd micro

def Entry.toJson (e : Entry) : Json :=
  Json.mkObj [("function", e.fn), ("name", e.name), ("kind", e.kind.text), ("status", e.status.text), ("rung", e.rung),
    ("model", e.model), ("costUsd", usdOf e.costMicro), ("runDir", e.runDir), ("detail", e.detail), ("frozen", e.frozen)]

/-- The count of the entries with the status `s`. -/
def countStatus (es : List Entry) (s : Status) : Nat := es.countP (·.status == s)

/-- The rungs of the closed entries with their counts, in the order of first use. -/
def rungCounts (es : List Entry) : List (String × Nat) :=
  let closed := es.filter (·.status == .closed)
  (closed.map (·.rung)).eraseDups.map fun r => (r, closed.countP (·.rung == r))

def Composition.toJson : Composition → Json
  | .proved axs => Json.mkObj [("state", "proved"), ("axioms", Json.arr (axs.map Json.str).toArray)]
  | .blocked bs => Json.mkObj [("state", "blocked"),
      ("blockedBy", Json.arr (bs.map fun (f, w) => Json.mkObj [("function", f), ("why", w)]).toArray)]

/-- The ledger file: the command, the order of the run, the counts, the composition and the entries. -/
def ledgerJson (command : String) (order : List String) (os : List FnOut) (es : List Entry) (c : Composition) : Json :=
  Json.mkObj [("command", command), ("order", Json.arr (order.map Json.str).toArray),
    ("counts", Json.mkObj (Status.all.map fun s => (s.text, Json.num (countStatus es s : Nat)))),
    ("rungs", Json.mkObj ((rungCounts es).map fun (r, n) => (r, Json.num n))),
    ("functions", Json.arr (os.map fun o => Json.mkObj [("function", o.label), ("statement", o.source.text),
      ("callees", Json.arr (o.callees.map Json.str).toArray), ("openCallees", Json.arr (o.openCallees.map Json.str).toArray),
      ("l2Closed", o.l2Closed), ("module", (o.module.map Json.str).getD Json.null),
      ("final", o.res.final.state)]).toArray),
    ("composition", c.toJson), ("obligations", Json.arr (es.map Entry.toJson).toArray)]

/-- The causes of the rows that are not generated: each function and cause with the number of its rows, in the order of first use. -/
def notGeneratedCauses (es : List Entry) : List ((String × String) × Nat) :=
  let ng := es.filter (·.status == .notGenerated)
  (ng.map fun e => (e.fn, e.detail)).eraseDups.map fun k => (k, ng.countP fun e => (e.fn, e.detail) == k)

/-- The Markdown summary: the counts per status and per rung, the functions, the causes of the rows that are not generated, the
lines `extra` (pass 2), and the composition. -/
def summaryMd (title command : String) (os : List FnOut) (es : List Entry) (c : Composition) (extra : List String := []) : String :=
  let fnLine (o : FnOut) : String :=
    let mine := es.filter (·.fn == o.label)
    s!"| {o.label} | {o.source.text} | {countStatus mine .closed} | {countStatus mine .«open»} | {countStatus mine .noStatement} | " ++
      s!"{countStatus mine .notGenerated} | {countStatus mine .calleeOpen} | {o.res.final.state} |"
  "\n".intercalate ([s!"# {title}", "", "Command:", "", "    " ++ command, "",
    s!"Obligations: {es.length}.", "", "| status | count |", "|---|---|"] ++
    Status.all.map (fun s => s!"| {s.text} | {countStatus es s} |") ++
    ["", "| rung (closed) | count |", "|---|---|"] ++ (rungCounts es).map (fun (r, n) => s!"| {r} | {n} |") ++
    ["", "| function | statement | closed | open | no statement | not generated | callee open | final |",
      "|---|---|---|---|---|---|---|---|"] ++ os.map fnLine ++
    ["", "## Rows that are not generated", "", "| function | cause | rows |", "|---|---|---|"] ++
    (notGeneratedCauses es).map (fun ((f, w), n) => s!"| {f} | {cell w} | {n} |") ++ extra ++
    ["", "## Composition", ""] ++
    (match c with
      | .proved axs => [s!"Every `final` closes. Axioms of `final` of the top function: {", ".intercalate axs}."]
      | .blocked bs => ["Blocked. The functions whose `final` does not close:", ""] ++ bs.map fun (f, w) => s!"- {f}: {cell w}") ++ [""])

end Skel.Full
