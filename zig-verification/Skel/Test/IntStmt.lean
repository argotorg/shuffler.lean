import Skel.TempDir
import Lift.Shuffler.Internal.Unit

/-! The tests of the internal statements of the full shuffler (suite `intstmt`, task INT-STMT): `lake exe skel-test --only
intstmt`. The files under test are made by `tools/shuffler-pilot/internal_statements.py`: `Lift/Shuffler/Internal/Fns.lean`
(the functions of the symbol table) and `Lift/Shuffler/Internal/<N>Statement.lean` (the 8 pilot statements on the shuffler code).

Checks:
* The unit: 31 functions with no repeat; the 8 moved functions are those of the pilot, and `roomOf` gives each a room.
* The symbol table (one Lean run of a check file): 31 functions; each entry is the address of its label in `Code.code`; each size
  is the next entry minus the entry (the last: the end of the code); the room is `roomOf` when it is known, and none when `roomOf`
  gives an error.
* The moved statements (one Lean run of `#stmt_shape`, `runShapes`): `#stmt_shape` reads each; the room of each is the room of
  `roomOf` (`checkRoom`); the shape is the shape of the pilot statement, but for the function and the statement namespaces; the
  `Fn` of each has the code `Lift.Shuffler.Code.code`, and the entry, the room and the result width of its symbol.
* Negative: the Pop statement with the room 8 in its `Fn` (a Lean run) is read by `#stmt_shape` and refused by `checkRoom`; a
  shape with a changed room is refused. -/

namespace IntStmtTests

open Lean Skel Skel.Gen Skel.Report.Level3 Lift.Shuffler.Internal

/-- The label of each function of the unit. -/
def labels : List String := unit.fns.map (·.entry)

def pureChecks : List (String × Bool) :=
  [ ("the unit has 31 functions, with no repeat", labels.length == 31 && labels.eraseDups.length == 31),
    ("the moved functions are the 8 functions of the pilot",
      moved.length == 8 && (pilotFns.map (·.entry)).all (moved.map (·.entry)).contains),
    ("roomOf gives a room for each moved function", moved.all fun f => (roomOf unit f).isOk),
    -- READER: each block of the 31 functions derives, so each function has a room
    ("roomOf gives a room for each of the 31 functions", (unit.fns.filter fun f => (roomOf unit f).isOk).length == 31) ]

/-- The value of an `Except` as an `Option`. -/
def ok? {α ε : Type} (e : Except ε α) : Option α := match e with | .ok a => some a | .error _ => none

/-- The address of the label `l` in the code, as a natural number. -/
def addrOf (l : String) : Nat := (unit.code.labels.label l).toBitVec.toNat

/-- The first address after the code. -/
def endAddr : Nat := (unit.code.startAddr + Int64.ofNat (unit.code.sizeBefore unit.code.program.length)).toBitVec.toNat

/-- A line `SYM <label> <entry> <size> <ret bits> <args> <room or ->` of the check file. -/
structure SymLine where
  (label : String) (entry size ret args : Nat) (room : Option Nat)

def parseSym (s : String) : Option SymLine :=
  match s.splitOn " " with
  | ["SYM", l, e, z, r, a, m] => do
    let room ← if m == "-" then pure none else (m.toNat?).map some
    pure ⟨l, ← e.toNat?, ← z.toNat?, ← r.toNat?, ← a.toNat?, room⟩
  | _ => none

/-- A line `FN <label> <entry> <room> <ret bits>` of the `Fn` of a moved statement. -/
def parseFn (s : String) : Option (String × Nat × Nat × Nat) :=
  match s.splitOn " " with
  | ["FN", l, e, r, w] => do pure (l, ← e.toNat?, ← r.toNat?, ← w.toNat?)
  | _ => none

/-- The lines of the info messages of a Lean run, and the error messages. -/
def runLean (dir : System.FilePath) (name text : String) : IO (List String × List String) := do
  let path := dir / name
  IO.FS.writeFile path text
  let r ← NxLift.Proc.runLean #["--json", path.toString] 600000
  let ms := NxLift.parseJsonMessages r.output
  let infos := ms.toList.filter (·.severity == NxLift.Severity.info) |>.flatMap fun m => m.text.splitOn "\n"
  let errs := ms.toList.filter (·.severity == NxLift.Severity.error) |>.map fun m => s!"{m.line}: {m.text}"
  let errs := match r.ending with
    | .timedOut _ => "the run timed out" :: errs
    | .exited _ => errs
  pure (infos, errs)

/-- The check file of the symbol table and of the `Fn` of each moved statement. `fnTerm` gives the `Fn` constant of the moved
statement of each label (from its shape). -/
def symFile (fnTerms : List (String × String)) : String :=
  "\n".intercalate <|
    ["import Lift.Shuffler.Internal.Fns"] ++ (moved.map fun f => s!"import {stmtModule unit f}") ++
    ["#eval Lift.Shuffler.Internal.Fns.syms.forM fun s => IO.println s!\"SYM {s.label} {s.entry.toBitVec.toNat} {s.size} " ++
      "{s.ret.bits} {s.args.length} {match s.room with | some r => toString r | none => \"-\"}\""] ++
    fnTerms.flatMap fun (l, t) =>
      [s!"#eval IO.println s!\"FN {l} \{{t}.entry.toBitVec.toNat} \{{t}.room} \{{t}.ret.bits}\"",
       s!"example : {t}.code = Lift.Shuffler.Code.code := rfl"]

/-- The text of the shape `sh` with the statement namespaces of the pilot renamed to those of the shuffler. -/
def renamed (j : String) : String :=
  pilotFns.foldl (fun s f => s.replace s!"Lift.Pilot.{f.stmt}Statement" s!"Lift.Shuffler.Internal.{f.stmt}Statement") j

/-- The pilot shape with the function of the moved shape and the namespaces of the shuffler. -/
def asMoved (pilot moved : StmtShape) : String :=
  renamed ((StmtShape.toJson { pilot with fn := { pilot.fn with room := moved.fn.room }, l3Text := moved.l3Text }).compress)

/-- The mutated Pop statement: the generated text as a plain file, in another namespace, with the room 8 in its `Fn`. -/
def badPop (gen : String) : String :=
  let t := (gen.replace "public import " "import ").replace "@[expose] public section" ""
  let t := (t.splitOn "\n").filter (fun l => l != "module") |> "\n".intercalate
  let t := t.replace "namespace Lift.Shuffler.Internal.PopStatement" "namespace Lift.Shuffler.Internal.Bad.PopStatement"
  let t := t.replace "end Lift.Shuffler.Internal.PopStatement" "end Lift.Shuffler.Internal.Bad.PopStatement"
  let t := t.replace "⟨Lift.Shuffler.Code.code, 0x101714, 0, " "⟨Lift.Shuffler.Code.code, 0x101714, 8, "
  "import Skel.Lean.Shape\n" ++ t ++ "\n#stmt_shape Lift.Shuffler.Internal.Bad.PopStatement.PopStatement\n"

def leanChecks : IO (List (String × Bool)) := do
  let dir ← tempDir "intstmt"
  -- the moved statements and the pilot statements, read by `#stmt_shape`
  let (shapes, _) ← runShapes (dir / "moved") moved (stmtModule unit) 600000
  let (pilot, _) ← runShapes (dir / "pilot") pilotFns (stmtModule smallUnit) 600000
  let shapeOf (f : PFn) : Option StmtShape := (shapes.lookup f.short).bind ok?
  let pilotOf (f : PFn) : Option StmtShape := (pilot.lookup f.short).bind ok?
  for (n, s) in shapes do
    if let .error e := s then IO.println s!"  intstmt: {n}: {e}"
  let readAll := moved.all fun f => (shapeOf f).isSome
  let roomsOk := moved.all fun f => match shapeOf f with
    | some sh => (checkRoom f sh).isOk
    | none => false
  let sameShape := moved.all fun f => match shapeOf f, pilotOf f with
    | some sh, some p => asMoved p sh == (StmtShape.toJson sh).compress
    | _, _ => false
  -- the symbol table and the `Fn` of each moved statement
  let fnTerms := moved.filterMap fun f => (shapeOf f).map fun sh => (f.entry, sh.fn.term.s)
  let (infos, errs) ← runLean dir "Syms.lean" (symFile fnTerms)
  unless errs.isEmpty do IO.println s!"  intstmt: Syms.lean: {errs.take 3}"
  let syms := infos.filterMap parseSym
  let fns := infos.filterMap parseFn
  let byAddr := (syms.map (·.entry)).mergeSort (· ≤ ·)
  let nextOf (e : Nat) : Nat := ((byAddr.filter (· > e)).head?).getD endAddr
  let symOf (l : String) : Option SymLine := syms.find? (·.label == l)
  -- the negative statement: a changed room
  let popF := moved.find? (·.stmt == "Pop")
  let gen ← (IO.FS.readFile "Lift/Shuffler/Internal/PopStatement.lean").toBaseIO
  let (badInfos, badErrs) ← match gen with
    | .ok g => runLean dir "Bad.lean" (badPop g)
    | .error e => pure ([], [s!"{e}"])
  let badShape := (badInfos.filterMap fun t => ok? (Json.parse t >>= Shape.parse)).head?
  pure
    [ ("#stmt_shape reads each moved statement", readAll),
      ("the room of each moved statement is the room of frameFacts", roomsOk),
      ("each moved shape is the pilot shape but for the function and the namespaces", sameShape),
      ("the check file of the symbol table has no error", errs.isEmpty),
      ("the symbol table has 31 functions, the labels of the unit", syms.length == 31 &&
        (syms.map (·.label)).all labels.contains && labels.all (syms.map (·.label)).contains),
      ("each entry is the address of its label in the code", syms.all fun s => s.entry == addrOf s.label),
      ("each size is the next entry minus the entry", syms.all fun s => s.size == nextOf s.entry - s.entry),
      ("the room of each symbol is roomOf, and none when roomOf gives an error",
        unit.fns.all fun f => (symOf f.entry).map (·.room) == some (ok? (roomOf unit f))),
      ("the Fn of each moved statement has the entry, the room and the result width of its symbol",
        fns.length == 8 && fns.all fun (l, e, r, w) => match symOf l with
          | some s => s.entry == e && s.room == some r && s.ret == w
          | none => false),
      ("the result width of each moved statement is the width of the signature",
        moved.all fun f => match shapeOf f, symOf f.entry with
          | some sh, some s => sh.fn.ret.bits == s.ret
          | _, _ => false),
      ("negative: #stmt_shape reads the Pop statement with the room 8", badErrs.isEmpty && badShape.map (·.fn.room) == some 8),
      ("negative: checkRoom refuses the Pop statement with the room 8", match popF, badShape with
        | some f, some sh => !(checkRoom f sh).isOk
        | _, _ => false),
      ("negative: checkRoom refuses each moved shape with the room plus 8", moved.all fun f => match shapeOf f with
        | some sh => !(checkRoom f { sh with fn := { sh.fn with room := sh.fn.room + 8 } }).isOk
        | none => false) ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "intstmt" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks ++ (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  intstmt: {name}"
  return failed

end IntStmtTests
