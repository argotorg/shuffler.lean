import Skel.TempDir
import Skel.Toy.Held
import Skel.Test.Par
import Skel.Test.GenStmt
import Lift.Toys.Code

/-! The tests of `Skel/Toy/Held.lean` (suite `held`): `lake exe skel-test --only held`. Each check is a value that must
hold; a check that does not hold prints one `FAIL` line. The programs are the real functions of `Lift.Toys.Code`.

Checks:
* The list has the six toys of the plan and the two callees `toyTwo` and `toyHalf`.
* The call graph: `toyOuter` calls `toyTwo`, `toyTwo` calls `toyHalf`, `toyAt` has no callee.
* The interfaces of the callees are those of the generated callees (G1-16): `toyTwo` has the room 32 and the inputs of
  its model (`rax`, `rbx`, `rsi`, `rdi`, `r14`), `toyHalf` the room 0 and the input `rdi`.
* `toyOuter` (a call) generates; its det text of `decompiles_l2` has no `fail`, and its model text has the closed models of
  `toyTwo` and of `toyHalf` in their namespaces, before its own model. The check files import the stack room and the frame
  tactics. The table of a generation failure has one line, `<fn>.generate failed <cause>`.
* An unknown name gives `GenError.noFunction`; its table has one line and no Lean run.
* The ladder of a generated toy has the rungs `liftBlock` and `closing` only: no replay store and no triple rung.
* The rows of a generated toy are block rows and `decompiles_l2`: no L2+ rows.
* The table lines have the row name, two spaces and the rung or `open`.
* The ledger of a held run (F6): one table line for each row, a check line with a time for each checked row, and the summary line. -/

namespace HeldTests

open Skel Skel.Gen Skel.Toy.Held

/-- The six toys of the plan (`docs/one-way-lift-g1-plan-20261118.md`, section 6.3). -/
def toyNames : List String := ["toyAt", "toyClamp", "toyFind", "toyFill", "toyWalk", "toyOuter"]

/-- The two callees of the plan. -/
def calleeNames : List String := ["toyTwo", "toyHalf"]

/-- The configuration of the test runs. -/
def testCfg : Config := { gate := .strict, limitMs := 30000, seed := 1, samples := 200 }

/-- The generation of `toyAt`, which has no call and no memory. -/
def atGen : Option Generated :=
  match generateOf "toyAt" with
  | .ok g => some g
  | .error _ => none

/-- The rows of `toyAt` are block rows and `decompiles_l2`. -/
def rowsAreL2 (g : Generated) : Bool :=
  g.obligations.all fun o => o.id.name.startsWith "block." || o.id.name == "decompiles_l2"

/-- The upper chain and the Houdini spec of `fn`. -/
def upperSpec (fn : String) : Option (Upper × Houdini.Spec) :=
  match upperOf fn with
  | .ok u => (houdiniSpecOf fn u).map (u, ·)
  | .error _ => none

/-- The number of atoms of the Houdini spec of `fn`: the words of its state with their bounds. -/
def atomCount (fn : String) : Option Nat := (upperSpec fn).map (·.2.atoms.length)

/-- The first triple of the Houdini rung of the upper ladder of `fn`, with an empty history. -/
def firstHoudini (fn : String) : Option Triple := do
  let (u, sp) ← upperSpec fn
  let (_, p) ← (upperLadders u (u.withRefute 1 1) (some sp)).triple.find? (·.1 == .houdini)
  match p ⟨⟨fn, "loop"⟩, .refine, .loop "L", "", [], .loop⟩ ⟨[], []⟩ with
  | some (.triple t) => some t
  | _ => none

/-- The pure checks of the suite. -/
def pureChecks : List (String × Bool) :=
  [ ("the list has the six toys of the plan", toys == toyNames),
    ("the list has the two callees of the plan", callees == calleeNames),
    ("toyOuter calls toyTwo, toyTwo calls toyHalf, toyAt has no callee",
      (targetOf "toyOuter").callees.map (·.name) == [".Ltoy.toyTwo"] &&
      (targetOf "toyTwo").callees.map (·.name) == [".Ltoy.toyHalf"] &&
      (targetOf "toyAt").callees.isEmpty),
    ("the interface of toyTwo is that of its model: room 32, inputs rax, rbx, rsi, rdi, r14",
      (targetOf "toyOuter").callees.map (fun c => (c.room, c.inputs, c.mem)) == [(32, [.rax, .rbx, .rsi, .rdi, .r14], true)]),
    ("the interface of toyHalf is that of its model: room 0, input rdi",
      (targetOf "toyTwo").callees.map (fun c => (c.room, c.inputs, c.mem)) == [(0, [.rdi], false)]),
    ("toyOuter (a call of a callee with a room): generate is ok and its det text of decompiles_l2 has no fail",
      match generateOf "toyOuter" with
      | .ok g => (g.det.filter (·.1.name == "decompiles_l2")).all fun (_, t) => !t.contains "fail \""
      | .error _ => false),
    ("toyOuter: the model text has the namespaces toyTwo and toyHalf (nested) with their decompiles_l2, then its own model",
      match generateOf "toyOuter" with
      | .ok g =>
        let t := g.modelText
        let at_ (s : String) : Nat := (t.splitOn s).headD "" |>.length
        let after := (t.splitOn "end toyTwo").getLastD ""
        t.startsWith "namespace toyTwo" && at_ "namespace toyHalf" < at_ "end toyHalf" &&
          at_ "end toyHalf" < at_ "end toyTwo" && (t.splitOn "theorem decompiles_l2 :").length == 3 &&
          (after.splitOn "structure In2").length == 2
      | .error _ => false),
    ("the check files import the stack room and the frame tactics",
      ["Lift.Sem.StackRoom", "Lift.Tactic.FrameMem"].all imports.contains),
    ("a generation failure: its table has one line, the failure",
      tableLines "f" (.error (.callee ".Ltoy.toyTwo")) == ["f.generate failed callee .Ltoy.toyTwo"]),
    ("an unknown name: generate gives noFunction",
      match generateOf "noSuchToy" with
      | .error (.noFunction "noSuchToy") => true
      | _ => false),
    ("the table of two rows has one line each",
      tableLines "f" (.ok [("block.entry", "liftBlock"), ("decompiles_l2", "open")]) ==
        ["block.entry  liftBlock", "decompiles_l2  open"]),
    ("toyAt: the ladder has liftBlock and closing only (no replay store, no triple rung)",
      (atGen.map fun g => ((ladderOf g).proof.map (·.1) == [.liftBlock, .closing]) && (ladderOf g).triple.isEmpty)
        == some true),
    ("toyAt: the rows are block rows and decompiles_l2 (no L2+ rows)",
      (atGen.map rowsAreL2) == some true),
    ("the check header imports the sites of the proofs (`Sites.readRet`) and opens their namespace",
      (headerOf "toyFind").imports.contains "Lift.Spike.Sites" && (headerOf "toyFind").opens.contains "Lift.Spike"),
    ("the Houdini specs of toyFind, toyWalk and toyFill have 4, 4 and 2 atoms",
      ["toyFind", "toyWalk", "toyFill"].map atomCount == [some 4, some 4, some 2]),
    ("the Houdini spec of an unknown function is none", (upperSpec "noSuchToy").isNone),
    ("the upper ladder with a spec has the triple rungs template, houdini",
      (upperSpec "toyFind").all fun (u, sp) =>
        (upperLadders u (u.withRefute 1 1) (some sp)).triple.map (·.1) == [.template, .houdini]),
    ("the upper ladder with no spec has the triple rung template only",
      match upperOf "toyFind" with
      | .ok u => (upperLadders u (u.withRefute 1 1)).triple.map (·.1) == [.template]
      | .error _ => false),
    ("the first Houdini triple of toyFind has the measure and the result of its template and all atoms",
      match upperSpec "toyFind", firstHoudini "toyFind" with
      | some (u, sp), some t =>
        u.templates.any (fun tp => tp.measure == t.measure && tp.result == t.result) && t.inv == Houdini.conj sp.atoms
      | _, _ => false),
    ("the first Houdini triple of toyFind is no template", match upperSpec "toyFind", firstHoudini "toyFind" with
      | some (u, _), some t => !u.templates.contains t
      | _, _ => false),
    ("the check header has the imports of the IO tests of genstmt (one list)",
      (headerOf "toyFind").imports == GenStmtTests.toysImports) ]

/-- The time of a log line of a check, `check NAME RESULT MS ms`; `none` for another line. -/
def checkMs (line : String) : Option Nat :=
  match line.splitOn " " with
  | "check" :: _ :: rest =>
    match rest.reverse with
    | "ms" :: n :: _ => n.toNat?
    | _ => none
  | _ => none

/-- The rows of `fn` that have a check line with a time in the ledger text: the rows named in a check line of the ledger. -/
def timedRows (ledger : String) (fn : String) (rows : List String) : List String :=
  let lines := (ledger.splitOn "\n").filter fun l => (checkMs l).isSome
  rows.filter fun r => lines.any fun l => (l.splitOn s!"Skel.Gen.Held.{fn}.{r} ").length > 1

/-- The IO checks: the run of a function whose generation fails gives one line and no Lean run; a short held run writes its
ledger: one table line for each row and a check line with a time for each checked row. -/
def runChecks : IO (List (String × Bool)) := do
  -- new directories: two runs of the suite at once (in this process or in another) do not share a path
  let dir ← Skel.tempDir "held-test"
  let (r2, n2) ← runFn dir testCfg "noSuchToy"
  let ledgerDir ← Skel.tempDir "held-test-ledger"
  runFns ledgerDir testCfg ["toyClamp"]
  let ledger ← IO.FS.readFile (ledgerDir / "ledger.txt")
  let rows := match generateOf "toyClamp" with
    | .ok g => g.obligations.map (·.id.name)
    | .error _ => []
  let tableRows := rows.filter fun r => (ledger.splitOn s!"toyClamp.{r}  ").length > 1
  return [
    ("an unknown name: the run gives one table line and no Lean run",
      (tableLines "noSuchToy" r2).length == 1 && n2 == 0 && (match r2 with | .error _ => true | .ok _ => false)),
    ("an unknown name: the ledger has its one table line",
      (← IO.FS.readFile (dir / "ledger.txt")).trimAscii.toString == "noSuchToy.generate failed noFunction noSuchToy"),
    ("a held run of toyClamp: the ledger has a table line for each of its rows", !rows.isEmpty && tableRows == rows),
    ("a held run of toyClamp: each row has a check line with a time in the ledger",
      !rows.isEmpty && timedRows ledger "toyClamp" rows == rows),
    ("a held run: the ledger ends with the summary line",
      (ledger.trimAscii.toString.splitOn "\n").getLast?.any (·.startsWith "summary: rows ")) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `held`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "held" then return 0
  let mut failed := 0
  -- two runs of the IO checks at once: each has its own directories
  let both ← Skel.Test.parMapM (fun (_ : Nat) => runChecks) [1, 2]
  for (name, ok) in pureChecks ++ both.flatten do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  held: {name}"
  return failed

end HeldTests
