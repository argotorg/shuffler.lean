import Skel.Ask
import Skel.Prove

/-! The flags of the two LLM rungs (task RUNG-WIRE), the same set for `skel run`, `skel discover` and `skel report level3`:

    --ask-config PATH --ask-max-usd X [--ask-budget PATH] [--ask-cmd CMD] [--ask-asks N] [--ask-dry-run]  the proposer (`Skel.Ask`)
    --prove-config PATH --prove-max-usd X [--prove-budget PATH] [--prove-cmd CMD] [--prove-dry-run]       the prover (`Skel.Prove`)
    --ask-parallel N                                                                    at most N model calls (asks and prove runs) at once
    --total-max-usd X                                                                   the run-wide cap of all the budget files
    --account-budget FILE                                                               include prior spend from another model book (repeatable)
    --final-allow FILE                                                                  the obligations that the final models may take

Each of `--ask-config` and `--prove-config` may be given more than once, in order (task FALLBACK-RUNG): the first model runs
first (`--ask-asks N` asks of a site, or the rounds of its prove config), and the models after it are the final models. A final
model runs only for an obligation that the first model left open AND that `--final-allow FILE` names (one obligation id on each
line: the name of the row, `dir/row`, or the site of a proposer). Without the file no final model runs: the obligation goes to the
list `escalate.jsonl` in the directory of the run, for review. The flags after a config belong to it (its cap, its budget
file, its command). `--total-max-usd` is the cap of the sum of `spentUsd` and the reservations of all the budget files of both
chains, with the bound of one call.

With no flag both rungs are off: no ask and no prove run is made, so tests and CI make no paid call. `--ask-max-usd` is the
cap of all asks of one site or row; `--prove-max-usd` is the cap of one prove run. `--ask-parallel` needs `--ask-config` or
`--prove-config`. In `skel report level3` the number of Lean runs at once is `--procs`; `skel discover` still runs `--ask-parallel`
functions at once. -/

namespace Skel.RungFlags

open System (FilePath)

/-- The settings of the two rungs. `none`: the rung is off. `parallel`: the number of model calls that run at the same time
(`skel discover`: the number of functions); `none` keeps the default of the command. -/
structure Rungs where
  ask : Option Skel.Ask.Cfg := none
  prove : Option Skel.Prove.Cfg := none
  parallel : Option Nat := none
  deriving DecidableEq, Repr

/-- The value of `--ask-parallel` and the other arguments, in order. -/
def takeParallel : List String → Except String (Option Nat × List String)
  | [] => pure (none, [])
  | "--ask-parallel" :: v :: rest => do
    let some n := v.toNat? | throw s!"--ask-parallel needs a number above 0, got '{v}'"
    if n == 0 then throw "--ask-parallel needs a number above 0"
    let (p, others) ← takeParallel rest
    if p.isSome then throw "--ask-parallel is given more than once"
    pure (some n, others)
  | ["--ask-parallel"] => throw "--ask-parallel has no value"
  | a :: rest => do
    let (p, others) ← takeParallel rest
    pure (p, a :: others)

/-- The value of `--total-max-usd` and the other arguments, in order. -/
def takeTotal : List String → Except String (Option String × List String)
  | [] => pure (none, [])
  | "--total-max-usd" :: v :: rest => do
    unless !v.isEmpty && v.any Char.isDigit && v.all (fun c => c.isDigit || c == '.') && (v.splitOn ".").length ≤ 2 do
      throw s!"--total-max-usd needs a decimal number, got '{v}'"
    let (t, others) ← takeTotal rest
    if t.isSome then throw "--total-max-usd is given more than once"
    pure (some v, others)
  | ["--total-max-usd"] => throw "--total-max-usd has no value"
  | a :: rest => do
    let (t, others) ← takeTotal rest
    pure (t, a :: others)

/-- Extra books contribute prior spend even when their model is not configured. -/
def takeAccounts : List String → Except String (List String × List String)
  | [] => pure ([], [])
  | "--account-budget" :: v :: rest => do
    if v.startsWith "--" || v.isEmpty then throw "--account-budget has no value"
    let (books, others) ← takeAccounts rest
    pure (v :: books, others)
  | ["--account-budget"] => throw "--account-budget has no value"
  | a :: rest => do
    let (books, others) ← takeAccounts rest
    pure (books, a :: others)

/-- The value of `--final-allow` and the other arguments, in order. -/
def takeAllow : List String → Except String (Option String × List String)
  | [] => pure (none, [])
  | "--final-allow" :: v :: rest => do
    if v.startsWith "--" then throw "--final-allow has no value"
    let (t, others) ← takeAllow rest
    if t.isSome then throw "--final-allow is given more than once"
    pure (some v, others)
  | ["--final-allow"] => throw "--final-allow has no value"
  | a :: rest => do
    let (t, others) ← takeAllow rest
    pure (t, a :: others)

/-- The settings of the rungs and the other arguments of the command line, in order. `--total-max-usd` gives each chain the
run-wide cap over the budget files of both, and `--final-allow` gives each chain the allow file of its final models. -/
def take (args : List String) : Except String (Rungs × List String) := do
  let (ask, a1) ← Skel.Ask.takeFlags args
  let (prove, a2) ← Skel.Prove.takeFlags a1
  let (parallel, a3) ← takeParallel a2
  let (total, a4a) ← takeTotal a3
  let (accounts, a4b) ← takeAccounts a4a
  let (allow, a4) ← takeAllow a4b
  if !accounts.isEmpty && total.isNone then throw "--account-budget needs --total-max-usd"
  if parallel.isSome && ask.isNone && prove.isNone then throw "--ask-parallel needs --ask-config or --prove-config"
  if total.isSome && ask.isNone && prove.isNone then throw "--total-max-usd needs --ask-config or --prove-config"
  if allow.isSome && ask.isNone && prove.isNone then throw "--final-allow needs --ask-config or --prove-config"
  let wide : Option Skel.Prove.Wide := total.map fun t =>
    { totalUsd := t, files := ((ask.map (·.links.map (·.budget))).getD [] ++ (prove.map (·.links.map (·.budget))).getD [] ++ accounts).eraseDups }
  pure ({ ask := ask.map ({ · with wide, allow }), prove := prove.map ({ · with wide, allow }), parallel }, a4)

/-- Whether both rungs are off. -/
def Rungs.off (r : Rungs) : Bool := r.ask.isNone && r.prove.isNone

/-- The row-loop configuration. The first ask model can set its ask limit. With no override, keep the caller limit.
Later models have limits for discovery sites and do not change the row limit. -/
def Rungs.loopConfig (r : Rungs) (cfg : Config) : Config :=
  { cfg with asks := (r.ask.bind (·.asks)).getD cfg.asks }

/-- `--ask-parallel`, else `dflt`. -/
def Rungs.width (r : Rungs) (dflt : Nat) : Nat := r.parallel.getD dflt

/-- The first model of a row. Split its row cap among at most `asks` calls. Integer division rounds down,
so the bounds of the calls sum to at most the row cap. A zero limit gives a zero call cap. -/
def Rungs.rowAskCfg (r : Rungs) (asks : Nat) : Option Skel.Ask.Cfg :=
  r.ask.map fun c =>
    { c with maxUsd := Skel.Prove.usdText ((Skel.Prove.usdOfText c.maxUsd).toOption.getD 0 / asks) }

/-- The asker of the loop of the skeleton: a prove request goes to the prover (`Prove.asker`, files below `proveDir`), any
other prompt to the proposer (`Ask.asker`, with the reply store `store`). A rung that is off gives no reply. -/
def Rungs.asker (r : Rungs) (asks : Nat) (proveDir store : FilePath) (log : String → IO Unit) : Asker := fun prompt =>
  if (Skel.Prove.Request.decode? prompt).isSome then Skel.Prove.asker r.prove proveDir log prompt
  else Skel.Ask.asker (r.rowAskCfg asks) store log prompt

/-- The number of actions that run now, for `Slots.run`. -/
abbrev Slots := IO.Ref Nat

/-- Runs `act` when fewer than `n` actions of `s` run (`n = 0` is `1`); else waits, polling every 10 ms. -/
partial def Slots.run {α : Type} (s : Slots) (n : Nat) (act : IO α) : IO α := do
  let ok ← s.modifyGet fun r => if r < max n 1 then (true, r + 1) else (false, r)
  if ok then
    try act finally s.modify (· - 1)
  else
    IO.sleep 10
    s.run n act

/-- A worker of `mapPar`: takes the next index of `next` until there is none, and stores the result of `f` at the index. -/
private partial def worker {α β : Type} (arr : Array α) (f : α → IO β) (next : IO.Ref Nat)
    (res : IO.Ref (Array (Option (Except IO.Error β)))) : IO Unit := do
  let i ← next.modifyGet fun i => (i, i + 1)
  if h : i < arr.size then
    let r ← (f arr[i]).toBaseIO
    res.modify (·.set! i (some r))
    worker arr f next res

/-- `f` on each element, at most `n` at the same time (`n = 0` is `1`), started in the order of the list; a function that ends
frees its place at once. The results are in the order of the list; the first error in that order is thrown after all end. -/
def mapPar {α β : Type} (n : Nat) (f : α → IO β) (xs : List α) : IO (List β) := do
  let arr := xs.toArray
  let next ← IO.mkRef 0
  let res ← IO.mkRef (arr.map fun _ => (none : Option (Except IO.Error β)))
  let tasks ← (List.range (min (max n 1) arr.size)).mapM fun _ => IO.asTask (prio := .dedicated) (worker arr f next res)
  for t in tasks do
    IO.ofExcept (← IO.wait t)
  (← res.get).toList.mapM fun r =>
    match r with
    | some r => IO.ofExcept r
    | none => throw (IO.userError "mapPar: a function has no result")

end Skel.RungFlags
