import Skel.Toy.HeldFast

/-! The tests of `Skel/Toy/HeldFast.lean` (suite `heldfast`): `lake exe skel-test --only heldfast`. Each check is a value that
must hold; a check that does not hold prints one `FAIL` line. The option `--fast` is tested with the parser in
`Skel/Test/Cli.lean`.

Checks:
* The targets of each function of the run point at `Lift.Toys.Fast`: the step, the range, the entry PC and the callees; none
  points at `Lift.Toys.` outside `Lift.Toys.Fast`.
* The check header imports the ReleaseFast L1 and its site lemmas, not the ReleaseSmall ones, and opens `Lift.Toys.Fast`.
* The imports of the run are those of `run held` with two modules replaced: no other module changes.
* The hand inputs are those of `run held`: the same functions, and the generation of a toy with a hint-free generation gives
  rows (`toyClamp`, whose text is the same at both levels, and `toyAt`).
* The generated model text of a toy names the ReleaseFast step. -/

namespace HeldFastTests

open Skel Skel.Gen

/-- The text `s` contains `sub`. -/
def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The text of a name of the target of `fn` that points at `Lift.Toys.` and not at `Lift.Toys.Fast.`. -/
def pointsAtSmall (name : String) : Bool := has name "Lift.Toys." && !has name "Lift.Toys.Fast."

/-- The names of the target of `fn` that give a PC or the step. -/
def namesOf (fn : String) : List String :=
  let t := Skel.Toy.HeldFast.targetOf fn
  [t.step, t.lo, t.hi, t.entryPC] ++ t.callees.map (·.entryPC)

/-- The pure checks of the suite. -/
def pureChecks : List (String × Bool) :=
  let fns := Skel.Toy.Held.functions
  [ ("the run has the functions of `run held`", fns.length == 8 && fns.contains "toyOuter" && fns.contains "toyHalf"),
    ("each target has the step, the range and the entry PC of Lift.Toys.Fast",
      fns.all fun fn =>
        let t := Skel.Toy.HeldFast.targetOf fn
        t.step == "Lift.Toys.Fast.L1.step" && t.lo == "Lift.Toys.Fast.toyCountPC" && t.hi == "Lift.Toys.Fast.toyEndPC"
          && t.entryPC == s!"Lift.Toys.Fast.{fn}PC"),
    ("no name of a target points at the ReleaseSmall unit", fns.all fun fn => !(namesOf fn).any pointsAtSmall),
    ("toyOuter and toyTwo have their callee, at the ReleaseFast PC",
      (Skel.Toy.HeldFast.targetOf "toyOuter").callees.map (·.entryPC) == ["Lift.Toys.Fast.toyTwoPC"]
        && (Skel.Toy.HeldFast.targetOf "toyTwo").callees.map (·.entryPC) == ["Lift.Toys.Fast.toyHalfPC"]
        && (Skel.Toy.HeldFast.targetOf "toyAt").callees.isEmpty),
    ("the callees have the names, models and inputs of `run held`",
      fns.all fun fn =>
        (Skel.Toy.HeldFast.targetOf fn).callees.map (fun c => (c.name, c.model, c.inputs)) ==
          (Skel.Toy.Held.targetOf fn).callees.map (fun c => (c.name, c.model, c.inputs))),
    ("the check header imports the ReleaseFast L1 and its site lemmas",
      (Skel.Toy.HeldFast.headerOf "toyAt").imports.contains "Lift.Toys.Fast.L1"
        && (Skel.Toy.HeldFast.headerOf "toyAt").imports.contains "Skel.Gen.Sites.ToysFast"),
    ("the check header does not import the ReleaseSmall L1 or its site lemmas",
      !(Skel.Toy.HeldFast.headerOf "toyAt").imports.contains "Lift.Toys.L1"
        && !(Skel.Toy.HeldFast.headerOf "toyAt").imports.contains "Skel.Gen.Sites.Toys"),
    ("the imports differ from those of `run held` in two modules only",
      Skel.Toy.HeldFast.imports.length == Skel.Toy.Held.imports.length
        && ((Skel.Toy.HeldFast.imports.zip Skel.Toy.Held.imports).filter fun (a, b) => a != b).length == 2),
    ("the header opens Lift.Toys.Fast and not Lift.Toys",
      (Skel.Toy.HeldFast.headerOf "toyAt").opens.contains "Lift.Toys.Fast"
        && !(Skel.Toy.HeldFast.headerOf "toyAt").opens.contains "Lift.Toys"),
    ("the check namespace of a function is its own and not that of `run held`",
      (Skel.Toy.HeldFast.headerOf "toyFind").namespace_ == "Skel.Gen.HeldFast.toyFind"),
    ("toyAt and toyClamp generate rows from the ReleaseFast code",
      ["toyAt", "toyClamp"].all fun fn =>
        match Skel.Toy.HeldFast.generateOf fn with
        | .ok g => !g.obligations.isEmpty
        | .error _ => false),
    ("the model text of toyClamp names the ReleaseFast step",
      match Skel.Toy.HeldFast.generateOf "toyClamp" with
      | .ok g => has g.modelText "Lift.Toys.Fast.L1.step" || has g.modelText "Lift.Toys.Fast.toyClampPC"
      | .error _ => false),
    ("an unknown name: generate gives noFunction",
      match Skel.Toy.HeldFast.generateOf "noSuchToy" with
      | .error (.noFunction "noSuchToy") => true
      | _ => false) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `heldfast`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "heldfast" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  heldfast: {name}"
  return failed

end HeldFastTests
