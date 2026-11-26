import Skel.Cli

/-! The tests of `Skel/Cli.lean` (suite `cli`): `lake exe skel-test --only cli`. Each check is a value that must hold.
A check that does not hold prints one `FAIL` line. The property draws `cases` triples of numbers, with the generator of
seed `seed + i` for the `i`-th triple, and prints one `FAIL` line for each triple that the parser does not map to the
run command with these values. The suite gives the number of failed checks and triples. `Config` has no `BEq`, so the
tests compare the fields of a command. -/

namespace CliTests

open Skel

/-- The fields of a `run` command: the function, the gate, the limit, the seed, the samples and the fault. -/
abbrev RunFields := String × Gate × Nat × Nat × Nat × Fault

/-- The fields of a `run` command, when the value is a `run` command. -/
def runFields : Except String Command → Option RunFields
  | .ok (.run fn cfg fault) => some (fn, cfg.gate, cfg.limitMs, cfg.seed, cfg.samples, fault)
  | _ => none

/-- The use of the templates by a `run` command, when the value is a `run` command. -/
def templatesOf : Except String Command → Option Bool
  | .ok (.run _ cfg _) => some cfg.useTemplates
  | _ => none

/-- The limit, the seed and the samples of a `run held --fast` command, when the value is one. -/
def fastFields : Except String Command → Option (Gate × Nat × Nat × Nat)
  | .ok (.runHeldFast cfg) => some (cfg.gate, cfg.limitMs, cfg.seed, cfg.samples)
  | _ => none

/-- The directory of a `replay-cex` command, when the value is one. -/
def replayDir : Except String Command → Option String
  | .ok (.replayCex dir) => some dir
  | _ => none

/-- The file, the gate and the limit of a `check-file` command, when the value is one. -/
def checkFields : Except String Command → Option (String × Gate × Nat)
  | .ok (.checkFile path g limitMs) => some (path, g, limitMs)
  | _ => none

/-- Is the value an error? -/
def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

/-- Does the value give an error whose message contains the text `s`? -/
def errorNames {α : Type} (s : String) : Except String α → Bool
  | .error m => (m.splitOn s).length > 1
  | .ok _ => false

/-- The defaults of `run` with the function `sum`. -/
def defaults : RunFields := ("sum", .strict, 30000, 1, 200, .none)

/-- The order of the options of the first full command line. -/
def fullA : List String :=
  ["run", "sum", "--gate", "bv", "--limit", "5", "--seed", "7", "--samples", "9", "--fault", "slow:x"]

/-- The options of `fullA` in another order. -/
def fullB : List String :=
  ["run", "sum", "--fault", "slow:x", "--samples", "9", "--seed", "7", "--limit", "5", "--gate", "bv"]

/-- The numbers of case `i`: a limit, a seed and a sample count, drawn by the generator of seed `seed + i`. -/
def numbers (seed i : Nat) : Nat × Nat × Nat :=
  let (l, g) := randNat (mkStdGen (seed + i)) 0 1000000000
  let (s, g) := randNat g 0 1000000000
  let (n, _) := randNat g 0 1000000000
  (l, s, n)

/-- The cases whose command line does not give the run command with the numbers of the case. -/
def propertyFailures (seed cases : Nat) : List (Nat × Nat × Nat) :=
  ((List.range cases).map (numbers seed)).filter fun (l, s, n) =>
    runFields (parse ["run", "sum", "--limit", toString l, "--seed", toString s, "--samples", toString n])
      != some ("sum", .strict, l, s, n, .none)

/-- The cases whose negative sample count is not an error. -/
def negativeFailures (seed cases : Nat) : List Nat :=
  ((List.range cases).map (fun i => (numbers seed i).2.2 + 1)).filter fun n =>
    !isError (parse ["run", "sum", "--samples", "-" ++ toString n])

/-- The checks of the parser, each with its name. -/
def checks : List (String × Bool) :=
  [ -- the defaults and each option alone
    ("run sum gives the defaults", runFields (parse ["run", "sum"]) == some defaults),
    ("--gate strict alone", runFields (parse ["run", "sum", "--gate", "strict"]) == some defaults),
    ("--gate bv alone", runFields (parse ["run", "sum", "--gate", "bv"]) == some ("sum", .bvDecide, 30000, 1, 200, .none)),
    ("--limit alone", runFields (parse ["run", "sum", "--limit", "5"]) == some ("sum", .strict, 5, 1, 200, .none)),
    ("--seed alone", runFields (parse ["run", "sum", "--seed", "7"]) == some ("sum", .strict, 30000, 7, 200, .none)),
    ("--samples alone", runFields (parse ["run", "sum", "--samples", "9"]) == some ("sum", .strict, 30000, 1, 9, .none)),
    ("--fault bad-replay alone", runFields (parse ["run", "sum", "--fault", "bad-replay:a.b"]) ==
      some ("sum", .strict, 30000, 1, 200, .badReplay "a.b")),
    ("--fault slow alone", runFields (parse ["run", "sum", "--fault", "slow:x"]) ==
      some ("sum", .strict, 30000, 1, 200, .slow "x")),
    -- all the options, in two orders
    ("all options in order A", runFields (parse fullA) == some ("sum", .bvDecide, 5, 7, 9, .slow "x")),
    ("all options in order B", runFields (parse fullB) == some ("sum", .bvDecide, 5, 7, 9, .slow "x")),
    ("orders A and B give the same fields", runFields (parse fullA) == runFields (parse fullB)),
    -- the option that turns the templates off (R13)
    ("the templates are used by default", templatesOf (parse ["run", "sum"]) == some true),
    ("--no-templates turns the templates off", templatesOf (parse ["run", "sum", "--no-templates"]) == some false),
    ("--no-templates with the other options keeps them",
      templatesOf (parse ["run", "sum", "--limit", "5", "--no-templates", "--seed", "7"]) == some false &&
      runFields (parse ["run", "sum", "--limit", "5", "--no-templates", "--seed", "7"]) ==
        some ("sum", .strict, 5, 7, 200, .none)),
    ("--no-templates given two times is an error", isError (parse ["run", "sum", "--no-templates", "--no-templates"])),
    ("--no-templates with a value is an error", isError (parse ["run", "sum", "--no-templates", "x"])),
    ("--no-templates before the function name is an error", isError (parse ["run", "--no-templates", "sum"])),
    -- the held toys at ReleaseFast (AF2-F)
    ("run held --fast gives the fast command with the defaults",
      fastFields (parse ["run", "held", "--fast"]) == some (.strict, 30000, 1, 200)),
    ("run held --fast keeps the other options, in any order",
      fastFields (parse ["run", "held", "--limit", "5", "--fast", "--seed", "7", "--gate", "bv"]) == some (.bvDecide, 5, 7, 200)),
    ("run held has no fast command", fastFields (parse ["run", "held"]) == none && (runFields (parse ["run", "held"])).isSome),
    ("--fast given two times is an error", isError (parse ["run", "held", "--fast", "--fast"])),
    ("--fast with a value is an error", isError (parse ["run", "held", "--fast", "x"])),
    ("--fast of another function is an error naming the function",
      errorNames "run sum" (parse ["run", "sum", "--fast"]) && errorNames "run held' only" (parse ["run", "find", "--fast"])),
    ("--fast before the function name is an error", isError (parse ["run", "--fast", "held"])),
    -- check-file
    ("check-file has the strict gate and 300000 ms by default",
      checkFields (parse ["check-file", "a.lean"]) == some ("a.lean", .strict, 300000)),
    ("check-file reads --gate and --limit",
      checkFields (parse ["check-file", "a.lean", "--limit", "5", "--gate", "bv"]) == some ("a.lean", .bvDecide, 5)),
    ("check-file with no file is an error", isError (parse ["check-file"])),
    ("check-file with an option as the file is an error", isError (parse ["check-file", "--gate", "bv"])),
    ("check-file with a run option is an error", isError (parse ["check-file", "a.lean", "--seed", "1"])),
    ("check-file with a flag of run is an error", isError (parse ["check-file", "a.lean", "--discover"])),
    -- replay-cex
    ("replay-cex gives its directory", replayDir (parse ["replay-cex", "out/cex"]) == some "out/cex"),
    -- boundary values
    ("--limit 0 is accepted", runFields (parse ["run", "sum", "--limit", "0"]) == some ("sum", .strict, 0, 1, 200, .none)),
    ("--seed 0 is accepted", runFields (parse ["run", "sum", "--seed", "0"]) == some ("sum", .strict, 30000, 0, 200, .none)),
    ("--samples 0 is accepted", runFields (parse ["run", "sum", "--samples", "0"]) == some ("sum", .strict, 30000, 1, 0, .none)),
    ("--samples -1 is an error", isError (parse ["run", "sum", "--samples", "-1"])),
    ("--limit with an empty value is an error", isError (parse ["run", "sum", "--limit", ""])),
    ("--limit +1 is an error", isError (parse ["run", "sum", "--limit", "+1"])),
    ("--limit 1_0 is an error", isError (parse ["run", "sum", "--limit", "1_0"])),
    ("--limit with the value --seed is an error", isError (parse ["run", "sum", "--limit", "--seed", "1"])),
    ("a function name that starts with -- is an error", isError (parse ["run", "--sum"])),
    ("an empty function name is an error", isError (parse ["run", ""])),
    ("a directory that starts with -- is an error", isError (parse ["replay-cex", "--x"])),
    ("an empty directory is an error", isError (parse ["replay-cex", ""])),
    -- error cases
    ("no arguments is an error", isError (parse [])),
    ("an unknown command is an error", isError (parse ["frob"])),
    ("run with no function name is an error", isError (parse ["run"])),
    ("run with an option but no function name is an error", isError (parse ["run", "--limit", "5"])),
    ("the function name after the options is an error", isError (parse ["run", "--limit", "5", "sum"])),
    ("an unknown option is an error", isError (parse ["run", "sum", "--bogus", "1"])),
    ("an extra argument after the function is an error", isError (parse ["run", "sum", "extra"])),
    ("an option with no value is an error", isError (parse ["run", "sum", "--limit"])),
    ("--limit x is an error", isError (parse ["run", "sum", "--limit", "x"])),
    ("--seed with a negative value is an error", isError (parse ["run", "sum", "--seed", "-3"])),
    ("--gate other is an error", isError (parse ["run", "sum", "--gate", "other"])),
    ("--fault other:NAME is an error", isError (parse ["run", "sum", "--fault", "other:NAME"])),
    ("--fault slow: with an empty name is an error", isError (parse ["run", "sum", "--fault", "slow:"])),
    ("--fault bad-replay: with an empty name is an error", isError (parse ["run", "sum", "--fault", "bad-replay:"])),
    ("--fault with no colon is an error", isError (parse ["run", "sum", "--fault", "slow"])),
    ("--fault with two colons is an error", isError (parse ["run", "sum", "--fault", "slow:a:b"])),
    ("--limit given two times is an error", isError (parse ["run", "sum", "--limit", "5", "--limit", "6"])),
    ("--gate given two times is an error", isError (parse ["run", "sum", "--gate", "strict", "--gate", "bv"])),
    ("replay-cex with no directory is an error", isError (parse ["replay-cex"])),
    ("replay-cex with two arguments is an error", isError (parse ["replay-cex", "a", "b"])),
    ("the error of --gate other names other", errorNames "other" (parse ["run", "sum", "--gate", "other"])),
    ("the error of --limit x names x", errorNames "x" (parse ["run", "sum", "--limit", "x"])),
    ("the error of --bogus names --bogus", errorNames "--bogus" (parse ["run", "sum", "--bogus", "1"]))
  ]

/-- Gives the number of failed checks and failed cases of the property. The suite runs when `only` is none or `cli`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "cli" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  cli: {name}"
  for (l, s, n) in propertyFailures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  cli: --limit {l} --seed {s} --samples {n} does not give these values"
  for n in negativeFailures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  cli: --samples -{n} is not an error"
  return failed

end CliTests
