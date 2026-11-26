import Skel.Types

/-! The command line of the walking skeleton (`docs/one-way-lift-skeleton-plan-20261118.md`, K17). `parse` turns the
arguments into a typed `Command`; no later code reads the strings again. Pure: the arguments are the only input. -/

namespace Skel

/-- The fault that a run injects: none, a bad replay of a name, or a slow check of a name. -/
inductive Fault where | none | badReplay (name : String) | slow (name : String)
  deriving DecidableEq, Repr

/-- A command: a run of a function with its configuration and fault, or the replay of the counterexamples in a
directory. -/
inductive Command where
  | run (fn : String) (cfg : Config) (fault : Fault)
  | runHeldFast (cfg : Config)
  | replayCex (dir : String)
  | checkFile (path : String) (gate : Gate) (limitMs : Nat)

/-- The options of `run` that the command line has given so far. A field is `none` until its option is read. -/
structure Opts where
  gate : Option Gate := none
  limitMs : Option Nat := none
  seed : Option Nat := none
  samples : Option Nat := none
  fault : Option Fault := none
  noTemplates : Option Unit := none
  discover : Option Unit := none
  solver : Option Unit := none
  fast : Option Unit := none

/-- The options that take a value. -/
private def valueOpts : List String := ["--gate", "--limit", "--seed", "--samples", "--fault"]

/-- A function name or a directory: not empty, and not an option. -/
private def plainArg (what s : String) : Except String String :=
  if s.isEmpty || s.startsWith "--" then .error s!"expected {what}, got '{s}'" else .ok s

/-- A natural number in decimal digits, with the option `opt` in its error. -/
private def natArg (opt v : String) : Except String Nat :=
  let bad : Except String Nat := .error s!"{opt} needs a natural number, got '{v}'"
  if v.isEmpty || !v.all Char.isDigit then bad
  else match v.toNat? with
    | some n => .ok n
    | none => bad

/-- The value of `--gate`: `strict` or `bv`. -/
private def gateArg (v : String) : Except String Gate :=
  match v with
  | "strict" => .ok .strict
  | "bv" => .ok .bvDecide
  | _ => .error s!"--gate needs strict or bv, got '{v}'"

/-- The value of `--fault`: `bad-replay:NAME` or `slow:NAME`, with a nonempty name. -/
private def faultArg (v : String) : Except String Fault :=
  let bad : Except String Fault := .error s!"--fault needs bad-replay:NAME or slow:NAME, got '{v}'"
  match v.splitOn ":" with
  | [kind, name] =>
    if name.isEmpty then .error s!"--fault needs a nonempty name, got '{v}'"
    else match kind with
      | "bad-replay" => .ok (.badReplay name)
      | "slow" => .ok (.slow name)
      | _ => bad
  | _ => bad

/-- Sets an option that is not set yet. A second use of the option is an error. -/
private def once {α : Type} (opt : String) (cur : Option α) (v : α) : Except String (Option α) :=
  match cur with
  | none => .ok (some v)
  | some _ => .error s!"{opt} is given more than once"

/-- Reads the value `v` of the option `opt` into `o`. -/
private def setOpt (o : Opts) (opt v : String) : Except String Opts := do
  match opt with
  | "--gate" =>
    let x ← once opt o.gate (← gateArg v)
    return { o with gate := x }
  | "--limit" =>
    let x ← once opt o.limitMs (← natArg opt v)
    return { o with limitMs := x }
  | "--seed" =>
    let x ← once opt o.seed (← natArg opt v)
    return { o with seed := x }
  | "--samples" =>
    let x ← once opt o.samples (← natArg opt v)
    return { o with samples := x }
  | "--fault" =>
    let x ← once opt o.fault (← faultArg v)
    return { o with fault := x }
  | _ => .error s!"unknown option '{opt}'"

/-- The options of `run`, each followed by its value, in any order. -/
private def options (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--no-templates" :: rest => do
    let x ← once "--no-templates" o.noTemplates ()
    options { o with noTemplates := x } rest
  | "--discover" :: rest => do
    let x ← once "--discover" o.discover ()
    options { o with discover := x } rest
  | "--solver" :: rest => do
    let x ← once "--solver" o.solver ()
    options { o with solver := x } rest
  | "--fast" :: rest => do
    let x ← once "--fast" o.fast ()
    options { o with fast := x } rest
  | opt :: rest =>
    if !valueOpts.contains opt then .error s!"unknown option '{opt}'"
    else match rest with
      | v :: rest' => do options (← setOpt o opt v) rest'
      | [] => .error s!"option '{opt}' has no value"

/-- The arguments after `run`: a function name, then the options. The defaults are those of the plan (section 7). `run held --fast`
is the held toys at ReleaseFast (`Skel/Toy/HeldFast.lean`). -/
private def runCmd : List String → Except String Command
  | [] => .error "run: expected a function name"
  | fn :: opts => do
    let fn ← plainArg "a function name" fn
    let o ← options {} opts
    let cfg : Config :=
      { gate := o.gate.getD .strict, limitMs := o.limitMs.getD 30000,
        seed := o.seed.getD 1, samples := o.samples.getD 200, useTemplates := o.noTemplates.isNone, discover := o.discover.isSome,
        solver := o.solver.isSome }
    match o.fast with
    | none => return .run fn cfg (o.fault.getD Fault.none)
    | some _ =>
      if fn == "held" then return .runHeldFast cfg
      else .error s!"--fast is an option of 'run held' only, not of 'run {fn}'"

/-- The arguments after `replay-cex`: exactly one directory. -/
private def replayCmd : List String → Except String Command
  | [dir] => do return .replayCex (← plainArg "a directory" dir)
  | _ => .error "replay-cex: expected exactly one directory"

/-- The arguments after `check-file`: one file, then the options `--gate` (default `strict`) and `--limit` (default 300000 ms). -/
private def checkFileCmd : List String → Except String Command
  | [] => .error "check-file: expected a file"
  | file :: opts => do
    let file ← plainArg "a file" file
    let o ← options {} opts
    unless o.seed.isNone && o.samples.isNone && o.fault.isNone && o.noTemplates.isNone && o.discover.isNone && o.fast.isNone do
      throw "check-file: the options are --gate and --limit"
    return .checkFile file (o.gate.getD .strict) (o.limitMs.getD 300000)

/-- The command of the arguments of the program (without its name). -/
def parse : List String → Except String Command
  | [] => .error "no command: expected run FN [options], replay-cex DIR or check-file FILE [options]"
  | "run" :: rest => runCmd rest
  | "replay-cex" :: rest => replayCmd rest
  | "check-file" :: rest => checkFileCmd rest
  | c :: _ => .error s!"unknown command '{c}'"

end Skel
