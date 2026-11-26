import Skel.Gen.Asm
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/Asm.lean` (suite `genasm`): `lake exe skel-test --only genasm`. Each check is a value that
must hold. A check that does not hold prints one `FAIL` line. The property is over the function names of
`Lift.Toys.Code.program` (the labels that do not start with `.`); there are finitely many, so it needs no random
generator. The suite gives the number of failed checks and functions. -/

namespace GenAsmTests

open Skel.Gen

/-- The sites, when `sites` succeeds. -/
def okSites : Except GenError (List Site) → Option (List Site)
  | .ok ss => some ss
  | .error _ => none

/-- Is the value the error `noFunction`? -/
def isNoFunction : Except GenError (List Site) → Bool
  | .error (.noFunction _) => true
  | _ => false

/-- Is the value the error `shape`, at this offset? -/
def isShapeAt (n : Nat) : Except GenError (List Site) → Bool
  | .error (.shape m _) => m == n
  | _ => false

/-- Is the site an `ud2`? -/
def isUd2 (s : Site) : Bool :=
  match s.instr with
  | .regular _ _ .ud2 => true
  | _ => false

/-- Is the directive the end label of a function? -/
def isFuncEnd (d : Directive) : Bool := d.label?.any (·.startsWith ".Lfunc_end")

/-- Is the directive an instruction? -/
def isInstr : Directive → Bool
  | .instr _ => true
  | _ => false

/-- The number of instructions of the function `name` in `Lift.Toys.Code.program`: from its label up to its end label,
the labels not counted. -/
def instrCount (name : String) : Nat :=
  ((Lift.Toys.Code.program.dropWhile (fun d => d.label? != some name)).takeWhile (fun d => !isFuncEnd d)).countP isInstr

/-- Is the list strictly increasing? -/
def strictlyIncreasing : List Nat → Bool
  | a :: b :: rest => a < b && strictlyIncreasing (b :: rest)
  | _ => true

/-- The function names of `Lift.Toys.Code.program`: its labels that do not start with `.`. -/
def functionNames : List String := Lift.Toys.Code.program.labels.filter (fun l => !l.startsWith ".")

/-- The property of one function of `Lift.Toys.Code`. When `sites` succeeds, the offsets start at 0, strictly increase,
and there is one site for each instruction (so no label is a site). -/
def propertyHolds (name : String) : Bool :=
  match okSites (Skel.Gen.sites Lift.Toys.Code.code name) with
  | none => true
  | some ss =>
    let offs := ss.map (·.offset)
    offs.head? == some 0 && strictlyIncreasing offs && ss.length == instrCount name

/-- A function with data after its `retq`: the label `f`, `retq` (1 byte), two bytes of data, the end label. -/
def dataProgram : Executable :=
  ⟨1000, [⟨.label "f", 0⟩, ⟨.instr (.regular .W64 .W64 .ret), 1⟩,
    ⟨.byteArray (ByteArray.mk #[0x0f, 0x0b]), 2⟩, ⟨.label ".Lfunc_end0", 0⟩]⟩

/-- A function of one instruction, at the address 1000. -/
def oneProgram : Executable :=
  ⟨1000, [⟨.label "one", 0⟩, ⟨.instr (.regular .W64 .W64 .ret), 1⟩, ⟨.label ".Lfunc_end0", 0⟩]⟩

/-- The offsets of the sites of `name` in `code`, when `sites` succeeds. -/
def offsetsIn (code : Executable) (name : String) : Option (List Nat) :=
  (okSites (Skel.Gen.sites code name)).map (·.map (·.offset))

/-- The names of the functions of `Lift.Toys.Code` for which `sites` fails. -/
def failures : List String := functionNames.filter (fun n => !propertyHolds n)

/-- The checks, each with its name. -/
def checks : List (String × Bool) :=
  let toyAt := okSites (Skel.Gen.sites Lift.Toys.Code.code "toyAt")
  [ ("toySum: offsets are 0 2 4 7 9 13 16 18",
      offsetsIn Lift.Spike.Code.code "toySum" == some [0, 2, 4, 7, 9, 13, 16, 18]),
    ("toyAt: 5 sites", toyAt.map List.length == some 5),
    ("toyAt: the ud2 is at offset 10", (toyAt.bind (·.find? isUd2)).map (·.offset) == some 10),
    ("unknown name is noFunction", isNoFunction (Skel.Gen.sites Lift.Spike.Code.code "noSuchFunction")),
    ("empty name is noFunction", isNoFunction (Skel.Gen.sites Lift.Spike.Code.code "")),
    ("data in the function is shape, at its offset", isShapeAt 1 (Skel.Gen.sites dataProgram "f")),
    ("toyInc (the last function): offsets are 0 4", offsetsIn Lift.Spike.Code.code "toyInc" == some [0, 4]),
    ("a function of one instruction: offset is 0", offsetsIn oneProgram "one" == some [0]),
    ("Lift.Toys.Code has 14 functions", functionNames.length == 14),
    ("every function of Lift.Toys.Code gives sites",
      functionNames.all (fun n => (okSites (Skel.Gen.sites Lift.Toys.Code.code n)).isSome)) ]

/-- Gives the number of failed checks and functions. The suite runs when `only` is none or `genasm`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genasm" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genasm: {name}"
  for n in failures do
    failed := failed + 1
    IO.println s!"FAIL  genasm: the property fails for {n}"
  return failed

end GenAsmTests
