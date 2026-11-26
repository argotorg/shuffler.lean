import Skel.Report.Level3Pilot
import Skel.Gen.Derived.Shuffler

/-! The full shuffler (`Lift.Shuffler.Code.code`, 31 functions) as a unit of the level 3 driver, for the internal statements
(task INT-STMT). Its functions are the labels of the derived blocks (`Skel.Gen.Derived.shuffler`); a function of the pilot keeps
its names of `pilotFns` (its statement module is `Lift.Shuffler.Internal.<stmt>Statement`). The room of a function is
`roomOf` (`frameFacts` of the derived blocks, the callees first): the rule of `tools/shuffler-pilot/fast_statements.py`.
`tools/shuffler-pilot/Rooms.lean` prints `roomLines`, which `tools/shuffler-pilot/internal_statements.py` reads. -/

namespace Lift.Shuffler.Internal

open Skel.Gen Skel.Report.Level3

/-- The function at the label `l`: the pilot function of the label, else a function with the label as each name and no
statement. -/
def fnOf (l : String) : PFn :=
  (pilotFns.find? (·.entry == l)).getD ⟨l, l, l, "", l⟩

/-- The shuffler unit. -/
def unit : Skel.Report.Level3.PUnit :=
  { name := "Shuffler", code := Lift.Shuffler.Code.code, codeName := "Lift.Shuffler.Code.code", l1 := "Lift.Shuffler.L1",
    pcNs := "Lift.Shuffler", lo := "Lift.Shuffler.shufflePC", hi := "Lift.Shuffler.shufflerEndPC", derived := Skel.Gen.Derived.shuffler, sites := "Skel.Gen.Sites.Shuffler",
    stmtNs := "Lift.Shuffler.Internal", fns := Skel.Gen.Derived.shuffler.map fun p => fnOf p.1 }

/-- The functions of the unit that have a statement: the 8 functions of the pilot. -/
def moved : List PFn := unit.fns.filter (·.stmt != "")

/-- One line for each function: `<label> <room>`, or `<label> - <cause>` when `roomOf` gives an error (a block of the function
or of a callee does not derive). The cause is on one line. -/
def roomLines : List String :=
  unit.fns.map fun f => match roomOf unit f with
    | .ok r => s!"{f.entry} {r}"
    | .error e => s!"{f.entry} - {" ".intercalate (e.splitOn "\n")}"

/-- The room of the statement shape `sh` of `f` is the room of `f` (`roomOf`). Else the error names both rooms: a statement
with a changed room is refused. -/
def checkRoom (f : PFn) (sh : StmtShape) : Except String Unit := do
  let r ← roomOf unit f
  unless sh.fn.room == r do
    throw s!"{f.entry}: the room {sh.fn.room} of the statement is not the room {r} of frameFacts"

end Lift.Shuffler.Internal
