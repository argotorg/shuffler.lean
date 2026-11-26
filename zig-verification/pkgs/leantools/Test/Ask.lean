import LeanTools.AskMain
import Test.OpenAI

/-! Tests of `leantools ask`: the pure functions, and the command (`Ask.run`) against the `ask`
endpoint of `Test/mock_http.py`. No test contacts a real endpoint. -/

open Lean LeanTools Ask Test

namespace Test.Ask

/-- The key of the tests; it must never appear in a file or an output. -/
def secret := "sk-ask-secret"
def configSecret := "CONFIG-SECRET"

/-- The pico-USD of a decimal text of USD, for the expected values of the tests. -/
def usd (s : String) : Money := (Money.ofText s).toOption.get!

structure Setup where
  dir : System.FilePath
  config : System.FilePath
  budget : System.FilePath
  prompt : System.FilePath

/-- Prices: 1, 0.5 and 2 USD for a million tokens: 1e6, 5e5 and 2e6 pico-USD for a token. -/
def configJson (base key : String) (usage finish : String) (delay retries maxTokens : Nat)
    (prices : String × String × String) : String :=
  s!"\{\"baseUrl\": \"{base}/v1/ask/{key}/{usage}/{finish}/{delay}\", \"model\": \"m1\", \"apiKeyEnv\": \"ASK_KEY\",
    \"maxTokens\": {maxTokens}, \"maxRetries\": {retries}, \"timeoutSeconds\": 10,
    \"price\": \{\"input\": {prices.1}, \"cachedInput\": {prices.2.1}, \"output\": {prices.2.2}},
    \"extra\": \{\"max_tokens\": 7, \"headers\": \{\"Authorization\": \"{configSecret}\"}}}"

def budgetJson (total spent : String) : String :=
  s!"\{\n  \"note\": \"a note\",\n  \"budgetUsd\": {total},\n  \"spentUsd\": {spent},\n  \"runs\": []\n}\n"

def setup (base key budget : String) (usage := "10/4/20/stop") (delay := 0) (retries := 0)
    (maxTokens := 100) (prices := ("1", "0.5", "2")) (prompt := "hello") : IO Setup := do
  let dir ← IO.FS.createTempDir
  let s : Setup := { dir, config := dir / "config.json", budget := dir / "budget.json", prompt := dir / "prompt.txt" }
  -- the usage text holds the finish reason as its last part
  let (u, f) := match usage.splitOn "/" with
    | [p, c, o, f] => (s!"{p}/{c}/{o}", f)
    | _ => (usage, "stop")
  IO.FS.writeFile s.config (configJson base key u f delay retries maxTokens prices)
  IO.FS.writeFile s.budget budget
  IO.FS.writeFile s.prompt prompt
  return s

def env (s : Setup) (key : Option String := some secret) : Env :=
  { root := s.dir, getEnv := fun k => pure (if k == "ASK_KEY" then key else none), sleep := fun _ => pure () }

def args (s : Setup) (maxUsd : String) (dry := false) : Ask.Args :=
  { config := s.config.toString, budget := s.budget.toString, maxUsd := usd maxUsd, dryRun := dry,
    system := none, prompt := .file s.prompt.toString }

def parsedBudget (s : Setup) : IO Budget := do
  match Budget.parse (← IO.ofExcept ((Json.parse (← IO.FS.readFile s.budget)).mapError IO.userError)) with
  | .ok b => pure b
  | .error e => throw (IO.userError e)

/-- All text of the files below `dir`. -/
partial def allText (dir : System.FilePath) : IO String := do
  unless ← dir.pathExists do return ""
  let mut out := ""
  for e in (← dir.readDir) do
    let t ← if ← e.path.isDir then allText e.path else IO.FS.readFile e.path
    out := out ++ t
  return out

def jc (j : Json) : String := j.compress

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

def cleanup (s : Setup) : IO Unit := IO.FS.removeDirAll s.dir

/-- The files `events.jsonl` and `summary.json` of the runs below `s.dir`: the parsed lines of each. -/
def runFiles (s : Setup) (name : String) : IO (Array String) := do
  let runs := LeanTools.stateDir s.dir / "runs"
  unless ← runs.pathExists do return #[]
  let mut out := #[]
  for e in (← runs.readDir) do
    let f := e.path / name
    if ← f.pathExists then out := out.push (← IO.FS.readFile f)
  return out

/-- The `reply` events of the run records of `s`. -/
def replyEvents (s : Setup) : IO (List Json) := do
  let texts ← runFiles s "events.jsonl"
  return texts.toList.flatMap fun t =>
    (t.splitOn "\n").filterMap fun l => (Json.parse l).toOption.filter fun j => j.getObjValD "event" == "reply"

/-- The `outcome` of the one summary of the runs of `s`. -/
def summaryOutcome (s : Setup) : IO (Option String) := do
  let texts ← runFiles s "summary.json"
  return texts[0]?.bind fun t => (Json.parse t).toOption.bind fun j => (j.getObjValAs? String "outcome").toOption

/-- Pico-USD per token of a price with at most 6 decimals, as the unit of a million tokens. -/
def priceText (k : Nat) : String :=
  let frac := toString (k % 1000000)
  s!"{k / 1000000}.{"".pushn '0' (6 - frac.length)}{frac}"

/-- The text of a budget in pico-USD, as USD with 12 decimals. -/
def pico12 (n : Nat) : String :=
  let frac := toString (n % 10 ^ 12)
  s!"{n / 10 ^ 12}.{"".pushn '0' (12 - frac.length)}{frac}"

/-- The bound of the setup defaults: 21 prompt tokens ("hello" and 16), 100 reply tokens. -/
def defaultBound : String := "0.000221"
/-- The cost of the usage 10 prompt, 4 cached, 20 reply tokens. -/
def defaultCost : String := "0.000048"

def pureSuite : T Unit := do
  -- money
  checkEq "Money.ofText" (Money.ofText "10.00").toOption (some ⟨10000000000000⟩)
  checkEq "Money.ofText rounds down" (Money.ofText "0.0000000000019").toOption (some ⟨1⟩)
  check "Money.ofText: not a number" (Money.ofText "ten").toOption.isNone
  check "Money.ofText: negative" (Money.ofText "-1").toOption.isNone
  check "Money.ofText: huge number of decimals" (Money.ofText ("0." ++ "".pushn '0' 200 ++ "1")).toOption.isNone
  checkEq "Money.parse rounds up" ((Json.parse "0.0000000000011").toOption.bind fun j => (Money.parse true j).toOption) (some ⟨2⟩)
  checkEq "Money text" (toString (usd "0.003412345678")) "0.003412345678"
  -- prices (USD for a million tokens, pico-USD for a token)
  let price := Price.parse (Json.mkObj [("input", .num ⟨14, 2⟩), ("output", .num ⟨28, 1⟩)])
  checkEq "Price.parse: cachedInput defaults to input" (price.toOption.map fun p => (p.input, p.cachedInput, p.output))
    (some (140000, 140000, 2800000))
  check "Price.parse: output is required" (Price.parse (Json.mkObj [("input", .num ⟨1, 0⟩)])).toOption.isNone
  check "Price.parse: negative" (Price.parse (Json.mkObj [("input", .num ⟨-1, 0⟩), ("output", .num ⟨1, 0⟩)])).toOption.isNone
  -- configuration
  let cfgOf (extra : String) : Option Ask.Config :=
    (Json.parse s!"\{\"model\": \"m\", \"price\": \{\"input\": 1, \"output\": 2}{extra}}").toOption.bind fun j => (Config.parse j).toOption
  check "Config: maxTokens is required" (cfgOf "").isNone
  check "Config: maxTokens 0" (cfgOf ", \"maxTokens\": 0").isNone
  check "Config: maxTokens negative" (cfgOf ", \"maxTokens\": -3").isNone
  checkEq "Config: maxTokens" ((cfgOf ", \"maxTokens\": 9").map (·.maxTokens)) (some 9)
  check "Config: price is required"
    ((Json.parse "{\"model\": \"m\", \"maxTokens\": 9}").toOption.bind fun j => (Config.parse j).toOption).isNone
  -- the time-out follows `maxTokens` (which replaces `extra.max_tokens`), unless it is given
  checkEq "Config: timeout from maxTokens"
    ((cfgOf ", \"maxTokens\": 65536, \"extra\": {\"max_tokens\": 7}").map (·.prove.timeoutSeconds)) (some 776)
  checkEq "Config: timeout given" ((cfgOf ", \"maxTokens\": 65536, \"timeoutSeconds\": 10").map (·.prove.timeoutSeconds)) (some 10)
  -- the arguments
  let parse (l : List String) := (Args.parse l).toOption
  check "Args: the full form"
    ((parse ["--config", "c", "--budget", "b", "--max-usd", "0.5", "--dry-run", "--system", "s", "p"]).any fun a =>
      a.config == "c" && a.budget == "b" && a.maxUsd == usd "0.5" && a.dryRun && a.system == some "s")
  check "Args: stdin" ((parse ["--config", "c", "--budget", "b", "--max-usd", "1", "-"]).any fun a =>
    match a.prompt with | .stdin => true | .file _ => false)
  check "Args: no prompt" (parse ["--config", "c", "--budget", "b", "--max-usd", "1"]).isNone
  check "Args: two prompts" (parse ["--config", "c", "--budget", "b", "--max-usd", "1", "p", "q"]).isNone
  check "Args: no config" (parse ["--budget", "b", "--max-usd", "1", "p"]).isNone
  check "Args: no budget" (parse ["--config", "c", "--max-usd", "1", "p"]).isNone
  check "Args: no max-usd" (parse ["--config", "c", "--budget", "b", "p"]).isNone
  check "Args: bad max-usd" (parse ["--config", "c", "--budget", "b", "--max-usd", "x", "p"]).isNone
  check "Args: unknown option" (parse ["--config", "c", "--budget", "b", "--max-usd", "1", "--bogus", "p"]).isNone
  check "Args: option without value" (parse ["--config", "c", "--budget", "b", "p", "--max-usd"]).isNone
  -- the budget file
  let budgetOf (t : String) : Option Budget := (Json.parse t).toOption.bind fun j => (Budget.parse j).toOption
  check "Budget: parses" (budgetOf (budgetJson "10.00" "0.00")).isSome
  check "Budget: no budgetUsd" (budgetOf "{\"spentUsd\": 0, \"runs\": []}").isNone
  check "Budget: no spentUsd" (budgetOf "{\"budgetUsd\": 1, \"runs\": []}").isNone
  check "Budget: no runs" (budgetOf "{\"budgetUsd\": 1, \"spentUsd\": 0}").isNone
  check "Budget: runs is no list" (budgetOf "{\"budgetUsd\": 1, \"spentUsd\": 0, \"runs\": {}}").isNone
  check "Budget: text for a number" (budgetOf "{\"budgetUsd\": \"1\", \"spentUsd\": 0, \"runs\": []}").isNone
  check "Budget: negative spent" (budgetOf "{\"budgetUsd\": 1, \"spentUsd\": -1, \"runs\": []}").isNone
  check "Budget: not an object" (budgetOf "[]").isNone
  let b? := budgetOf (budgetJson "10.00" "0.5")
  check "Budget: the note is kept"
    (b?.any fun b => (b.toJson.getObjValD "note") == toJson "a note")
  check "Budget: write and read again"
    (b?.any fun b => (budgetOf b.toJson.pretty).any fun b' => b'.total == b.total && b'.spent == b.spent)
  -- the decision
  let b := (b?.getD { total := ⟨0⟩, spent := ⟨0⟩, runs := #[], rest := [] })   -- total 10, spent 0.5
  let left := usd "9.5"
  check "decide: the bound is equal to what is left" (match decide b (usd "20") left with | .ok () => true | _ => false)
  check "decide: one pico-USD more than what is left"
    (match decide b (usd "20") ⟨left.pico + 1⟩ with | .error (.overBudget ..) => true | _ => false)
  check "decide: --max-usd equal to the bound" (match decide b (usd "1") (usd "1") with | .ok () => true | _ => false)
  check "decide: --max-usd one pico-USD below the bound"
    (match decide b ⟨(usd "1").pico - 1⟩ (usd "1") with | .error (.overMax ..) => true | _ => false)
  check "Refusal: the message names the three numbers"
    (let m := (Refusal.overBudget (usd "0.5") (usd "9.600001") (usd "10")).message
     contains m "0.5" && contains m "9.600001" && contains m "10")
  -- reservations: the spend and the bounds of the calls in flight count against the budget
  let two : Array (String × Money) := #[("a", usd "0.25"), ("b", usd "0.25")]
  let rb : Budget := { total := usd "1", spent := usd "0.5", runs := #[], rest := [], reservations := two }
  let rb1 : Budget := { rb with reservations := #[("a", usd "0.25")] }
  check "decide: spent + reserved + bound equal to the budget" (match decide rb1 (usd "1") (usd "0.25") with | .ok () => true | _ => false)
  check "decide: one pico-USD above the budget with reservations"
    (match decide rb1 (usd "1") ⟨(usd "0.25").pico + 1⟩ with | .error (.overReserved ..) => true | _ => false)
  check "decide: a reserved budget refuses" (match decide rb (usd "1") (usd "0.000001") with | .error (.overReserved ..) => true | _ => false)
  check "Refusal: the message names the reservations"
    (let m := (Refusal.overReserved (usd "0.5") (usd "0.25") (usd "0.3") (usd "1")).message
     contains m "reserved 0.25 " && contains m "bound 0.3 ")
  checkEq "settle: the reservation goes, the cost and the entry come"
    ((rb.settle "a" (usd "0.1") (toJson 1)).reservations.map (·.1), (rb.settle "a" (usd "0.1") (toJson 1)).spent, (rb.settle "a" (usd "0.1") (toJson 1)).runs.size)
    (#["b"], usd "0.6", 1)
  check "Budget: the reservations survive the file"
    ((budgetOf rb.toJson.pretty).any fun b => b.reservations == rb.reservations && b.rest.isEmpty)
  let rb0 : Budget := { rb with reservations := #[] }
  check "Budget: no reservations, no field" (rb0.toJson.getObjVal? "reservations").toOption.isNone
  check "Budget: a reservation that is not a list is an error"
    (budgetOf "{\"budgetUsd\": 1, \"spentUsd\": 0, \"runs\": [], \"reservations\": 3}").isNone
  check "Budget: a reservation with no bound is an error"
    (budgetOf "{\"budgetUsd\": 1, \"spentUsd\": 0, \"runs\": [], \"reservations\": [{\"run\": \"a\"}]}").isNone
  -- properties
  forAll "cost is at most the bound (usage within the bound)" 300 11
    (fun g =>
      let (pb, g) := Test.below 500 g
      let (mt, g) := Test.below 500 g
      let (c, g) := Test.below 5000000 g
      let (ci, g) := Test.below 5000000 g
      let (o, g) := Test.below 5000000 g
      let (p, g) := Test.below (pb + 1) g
      let (ca, g) := Test.below (p + 1) g
      let (co, g) := Test.below (mt + 1) g
      ((pb, mt, c, ci, o, p, ca, co), g))
    (fun (pb, mt, c, ci, o, p, ca, co) =>
      let pr : Price := { input := c, cachedInput := ci, output := o }
      pr.cost { prompt := p, cached := ca, completion := co } ≤ pr.bound pb mt)
  forAll "the record adds the cost to spentUsd and one entry" 300 12
    (fun g =>
      let (s, g) := Test.below 1000000000 g
      let (c, g) := Test.below 1000000000 g
      ((s, c), g))
    (fun (s, c) =>
      let b : Budget := { total := ⟨10 ^ 13⟩, spent := ⟨s⟩, runs := #[toJson 1], rest := [] }
      let b' := b.record ⟨c⟩ (toJson 2)
      b'.spent.pico == s + c && b'.runs.size == 2 && b'.total == b.total)
  forAll "Money survives the file" 300 13 (Test.below 100000000000000)
    (fun n => (Money.parse false (Money.toJson ⟨n⟩)).toOption == some ⟨n⟩)

/-- The one counted request of the key of the endpoint. -/
def requests (base key : String) : IO Nat := Test.OpenAI.count base key

def serverSuite : T Unit := Test.Http.withServer fun base => do
  let fresh (tag : String) : String := s!"ask-{tag}"
  -- a call: the reply is printed, the entry is added, spentUsd grows by the cost
  do
    let s ← setup base (fresh "ok") (budgetJson "10.00" "0.5")
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "ok: status" o.code 0
    checkEq "ok: the reply is printed" o.out "1:hello"
    check "ok: the usage line" (contains o.err "prompt_tokens=10 cached_tokens=4 completion_tokens=20 cost_usd=0.000048 finish_reason=stop")
    checkEq "ok: requests" (← requests base (fresh "ok")) 1
    let b ← parsedBudget s
    checkEq "ok: spentUsd" b.spent (usd "0.500048")
    checkEq "ok: one entry" b.runs.size 1
    let e := (b.runs[0]?.getD Json.null)
    checkEq "ok: entry cost" (jc (e.getObjValD "costUsd")) (jc (usd defaultCost).toJson)
    checkEq "ok: entry model" (jc (e.getObjValD "model")) (jc (toJson "m1"))
    checkEq "ok: entry finish reason" (jc (e.getObjValD "finishReason")) (jc (toJson "stop"))
    checkEq "ok: entry tokens"
      (jc (e.getObjValD "promptTokens"), jc (e.getObjValD "cachedTokens"), jc (e.getObjValD "completionTokens"))
      ("10", "4", "20")
    check "ok: entry prompt hash" (((e.getObjValD "promptSha256").getStr?.toOption.map (·.length)) == some 64)
    check "ok: entry time" ((e.getObjValD "time").getStr?.toOption.any (!·.isEmpty))
    checkEq "ok: the note is kept" ((← parsedBudget s).rest.map (·.1)) ["note"]
    checkEq "ok: budgetUsd is kept" (← parsedBudget s).total (usd "10")
    -- the record of the call and the files hold no credential
    let runDir := s.dir / ".leantools" / "runs"
    let nRuns ← if ← runDir.pathExists then pure (← runDir.readDir).size else pure 0
    checkEq "ok: one run record" nRuns 1
    let text := (← allText (s.dir / ".leantools")) ++ (← IO.FS.readFile s.budget)
    check "ok: no key in the record or the budget file" (!contains text secret)
    check "ok: no config secret in the record or the budget file" (!contains text configSecret)
    check "ok: the record has the events" (contains text "request-attempt" && contains text "run-start")
    check "ok: no temporary file is left" ((← s.dir.readDir).all fun e => !contains e.fileName ".tmp")
    cleanup s
  -- the system prompt is a message
  do
    let s ← setup base (fresh "system") (budgetJson "10.00" "0")
    IO.FS.writeFile (s.dir / "sys.txt") "SYSTEM"
    let o ← Ask.run (env s) { args s "1" with system := some (s.dir / "sys.txt").toString } (pure "")
    checkEq "system: two messages" o.out "2:hello"
    cleanup s
  -- the prompt from stdin
  do
    let s ← setup base (fresh "stdin") (budgetJson "10.00" "0")
    let o ← Ask.run (env s) { args s "1" with prompt := .stdin } (pure "from stdin")
    checkEq "stdin: the reply" o.out "1:from stdin"
    cleanup s
  -- `max_tokens` of the config replaces that of `extra`; the bound uses it
  do
    let s ← setup base (fresh "bound") (budgetJson "10.00" "0")
    let o ← Ask.run (env s) (args s "1" (dry := true)) (pure "")
    check "dry-run: max_tokens of the config" (contains o.out "\"max_tokens\": 100" && !contains o.out "\"max_tokens\": 7")
    check "dry-run: the bound" (contains o.out s!"cost_bound_usd: {defaultBound}")
    cleanup s
  -- the boundary: spent + bound equal to the budget is permitted; one pico-USD more is refused
  do
    let s ← setup base (fresh "eq") (budgetJson "1.000221" "1")
    let o ← Ask.run (env s) (args s defaultBound) (pure "")
    checkEq "boundary: exactly equal is permitted" o.code 0
    cleanup s
  do
    let s ← setup base (fresh "over") (budgetJson "1.000220999999" "1")
    let before ← IO.FS.readFile s.budget
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "boundary: one pico-USD more is refused: status" o.code 1
    check "boundary: the message has the three numbers"
      (contains o.err "1" && contains o.err defaultBound && contains o.err "1.000220999999")
    checkEq "boundary: no request" (← requests base (fresh "over")) 0
    checkEq "boundary: the budget file is unchanged" (← IO.FS.readFile s.budget) before
    checkEq "boundary: nothing is printed" o.out ""
    checkEq "boundary: no run record" (← (s.dir / ".leantools").pathExists) false
    cleanup s
  -- --max-usd: equal to the bound is permitted; one pico-USD below is refused
  do
    let s ← setup base (fresh "maxeq") (budgetJson "10" "0")
    let o ← Ask.run (env s) (args s defaultBound) (pure "")
    checkEq "max-usd: equal to the bound is permitted" o.code 0
    cleanup s
  do
    let s ← setup base (fresh "maxlow") (budgetJson "10" "0")
    let before ← IO.FS.readFile s.budget
    let o ← Ask.run (env s) (args s "0.000220999999") (pure "")
    checkEq "max-usd: below the bound: status" o.code 1
    check "max-usd: the message" (contains o.err "--max-usd" && contains o.err defaultBound)
    checkEq "max-usd: no request" (← requests base (fresh "maxlow")) 0
    checkEq "max-usd: the budget file is unchanged" (← IO.FS.readFile s.budget) before
    cleanup s
  -- a broken budget file names the file; no request; the file is not changed
  for (name, text) in [("junk", "not json"), ("empty", ""), ("nofield", "{\"budgetUsd\": 1, \"runs\": []}"),
      ("negative", "{\"budgetUsd\": 1, \"spentUsd\": -1, \"runs\": []}"),
      ("runs", "{\"budgetUsd\": 1, \"spentUsd\": 0, \"runs\": 3}"),
      ("string", "{\"budgetUsd\": \"1\", \"spentUsd\": 0, \"runs\": []}")] do
    let s ← setup base (fresh s!"broken-{name}") text
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq s!"broken budget ({name}): status" o.code 2
    check s!"broken budget ({name}): the message names the file" (contains o.err s.budget.toString)
    checkEq s!"broken budget ({name}): no request" (← requests base (fresh s!"broken-{name}")) 0
    checkEq s!"broken budget ({name}): the file is unchanged" (← IO.FS.readFile s.budget) text
    cleanup s
  -- a missing budget file
  do
    let s ← setup base (fresh "nobudget") ""
    IO.FS.removeFile s.budget
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "missing budget file: status" o.code 2
    check "missing budget file: names the file" (contains o.err s.budget.toString)
    checkEq "missing budget file: no request" (← requests base (fresh "nobudget")) 0
    checkEq "missing budget file: no lock file" (← (System.FilePath.mk s!"{s.budget}.lock").pathExists) false
    cleanup s
  -- a missing key variable
  do
    let s ← setup base (fresh "nokey") (budgetJson "10" "0")
    let before ← IO.FS.readFile s.budget
    let o ← Ask.run (env s (key := none)) (args s "1") (pure "")
    checkEq "no key: status" o.code 2
    check "no key: the message names the variable" (contains o.err "ASK_KEY")
    checkEq "no key: no request" (← requests base (fresh "nokey")) 0
    checkEq "no key: the budget file is unchanged" (← IO.FS.readFile s.budget) before
    cleanup s
  -- a broken config
  do
    let s ← setup base (fresh "badconfig") (budgetJson "10" "0")
    IO.FS.writeFile s.config "{\"model\": \"m\"}"
    let before ← IO.FS.readFile s.budget
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "broken config: status" o.code 2
    check "broken config: names the file" (contains o.err s.config.toString)
    checkEq "broken config: the budget file is unchanged" (← IO.FS.readFile s.budget) before
    cleanup s
  -- --dry-run: no request, no key in the output, no change
  do
    let s ← setup base (fresh "dry") (budgetJson "10" "0.5")
    let before ← IO.FS.readFile s.budget
    let o ← Ask.run (env s) (args s "1" (dry := true)) (pure "")
    checkEq "dry-run: status" o.code 0
    checkEq "dry-run: no request" (← requests base (fresh "dry")) 0
    check "dry-run: no key" (!contains (o.out ++ o.err) secret)
    check "dry-run: no config secret" (!contains (o.out ++ o.err) configSecret)
    check "dry-run: the body has the model and the prompt"
      (contains o.out "\"model\": \"m1\"" && contains o.out "\"content\": \"hello\"")
    check "dry-run: the check" (contains o.out "check: ok")
    checkEq "dry-run: the budget file is unchanged" (← IO.FS.readFile s.budget) before
    checkEq "dry-run: no run record, no lock" (← (s.dir / ".leantools").pathExists) false
    cleanup s
  -- --dry-run needs no key, and tells that the call would be refused
  do
    let s ← setup base (fresh "dryref") (budgetJson "0.0001" "0")
    let o ← Ask.run (env s (key := none)) (args s "1" (dry := true)) (pure "")
    checkEq "dry-run, no key, over budget: status" o.code 0
    check "dry-run: would refuse" (contains o.out "would refuse")
    cleanup s
  -- a request that fails after the retries
  do
    let s ← setup base (fresh "fail") (budgetJson "10" "0.5") (usage := "0/0/0/fail") (retries := 2)
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "failure: status" o.code 1
    checkEq "failure: no reply text" o.out ""
    check "failure: the message" (contains o.err "ask failed")
    checkEq "failure: requests (1 and 2 retries)" (← requests base (fresh "fail")) 3
    let b ← parsedBudget s
    checkEq "failure: spentUsd is unchanged" b.spent (usd "0.5")
    checkEq "failure: one entry" b.runs.size 1
    checkEq "failure: the entry" (jc ((b.runs[0]?.getD Json.null).getObjValD "finishReason"), jc ((b.runs[0]?.getD Json.null).getObjValD "costUsd"))
      (jc (toJson "error"), jc (usd "0").toJson)
    check "failure: no key in the files" (!contains (← allText s.dir) secret)
    cleanup s
  -- finish_reason=length: the reply is printed, a distinct status, the cost is recorded
  do
    let s ← setup base (fresh "length") (budgetJson "10" "0") (usage := "10/4/20/length")
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "length: status" o.code 3
    checkEq "length: the reply is printed" o.out "1:hello"
    let b ← parsedBudget s
    checkEq "length: spentUsd" b.spent (usd defaultCost)
    checkEq "length: the entry" (jc ((b.runs[0]?.getD Json.null).getObjValD "finishReason")) (jc (toJson "length"))
    cleanup s
  -- finish_reason=error: the call fails (status 1), the cost is recorded, the reply is not a result
  do
    let s ← setup base (fresh "finerr") (budgetJson "10" "0") (usage := "10/4/20/error")
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "error finish: status" o.code 1
    check "error finish: stderr names the finish reason" (contains o.err "finish_reason=error")
    let b ← parsedBudget s
    checkEq "error finish: the cost is recorded" b.spent (usd defaultCost)
    checkEq "error finish: one entry" b.runs.size 1
    checkEq "error finish: the outcome of the summary" (← summaryOutcome s) (some "error")
    cleanup s
  -- the reasoning text goes to the reply event of the run record
  do
    let s ← setup base (fresh "reasoning") (budgetJson "10" "0")
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "reasoning: status" o.code 0
    checkEq "reasoning: the reply event" ((← replyEvents s).map fun e => (jc (e.getObjValD "reasoning"), jc (e.getObjValD "text")))
      [(jc (toJson "think-1"), jc (toJson "1:hello"))]
    cleanup s
  -- an endpoint with no usage is charged the bound
  do
    let s ← setup base (fresh "nousage") (budgetJson "10" "0") (usage := "nousage/0/0/stop")
    let o ← Ask.run (env s) (args s "1") (pure "")
    checkEq "no usage: status" o.code 0
    let b ← parsedBudget s
    checkEq "no usage: the bound is charged" b.spent (usd defaultBound)
    checkEq "no usage: marked" (jc ((b.runs[0]?.getD Json.null).getObjValD "usageKnown")) "false"
    cleanup s
  -- two calls in sequence: the second sees the spend of the first
  do
    -- the bound is 0.000221 and the cost 0.000048: the budget 0.0003 is enough for two calls
    let s ← setup base (fresh "seq") (budgetJson "0.0003" "0")
    let o1 ← Ask.run (env s) (args s "1") (pure "")
    let o2 ← Ask.run (env s) (args s "1") (pure "")
    let o3 ← Ask.run (env s) (args s "1") (pure "")
    checkEq "sequence: statuses" [o1.code, o2.code, o3.code] [0, 0, 1]
    check "sequence: the third message names the spend of the first two" (contains o3.err "0.000096")
    checkEq "sequence: requests" (← requests base (fresh "seq")) 2
    let b ← parsedBudget s
    checkEq "sequence: spentUsd" b.spent (usd "0.000096")
    checkEq "sequence: entries" b.runs.size 2
    cleanup s
  -- two calls at the same time: both entries are present
  do
    let s ← setup base (fresh "conc") (budgetJson "10" "0") (delay := 300)
    let t1 ← IO.asTask (prio := .dedicated) (Ask.run (env s) (args s "1") (pure ""))
    let t2 ← IO.asTask (prio := .dedicated) (Ask.run (env s) (args s "1") (pure ""))
    let o1 ← IO.ofExcept (← IO.wait t1)
    let o2 ← IO.ofExcept (← IO.wait t2)
    checkEq "concurrent: statuses" [o1.code, o2.code] [0, 0]
    let b ← parsedBudget s
    checkEq "concurrent: both entries" b.runs.size 2
    checkEq "concurrent: spentUsd" b.spent (usd "0.000096")
    checkEq "concurrent: requests" (← requests base (fresh "conc")) 2
    cleanup s
  -- two calls at the same time with budget for one: the second sees the spend of the first
  do
    let s ← setup base (fresh "concref") (budgetJson "0.00025" "0") (delay := 300)
    let t1 ← IO.asTask (prio := .dedicated) (Ask.run (env s) (args s "1") (pure ""))
    let t2 ← IO.asTask (prio := .dedicated) (Ask.run (env s) (args s "1") (pure ""))
    let o1 ← IO.ofExcept (← IO.wait t1)
    let o2 ← IO.ofExcept (← IO.wait t2)
    checkEq "concurrent, budget for one: statuses" ([o1.code, o2.code].toArray.qsort (· < ·)).toList [0, 1]
    checkEq "concurrent, budget for one: requests" (← requests base (fresh "concref")) 1
    checkEq "concurrent, budget for one: entries" (← parsedBudget s).runs.size 1
    cleanup s
  -- property: for random usage and prices, spentUsd after = spentUsd before + cost (an expected
  -- value computed here, in whole pico-USD), and spentUsd stays within budgetUsd
  let mut g := mkStdGen 7
  for i in [0:25] do
    let (p, g1) := Test.below 21 g       -- prompt tokens up to the bound of 21
    let (ca, g2) := Test.below (p + 1) g1
    let (co, g3) := Test.below 101 g2    -- reply tokens up to maxTokens 100
    let (pi, g4) := Test.below 20000000 g3   -- prices of 0 to 20 USD for a million tokens
    let (pc, g5) := Test.below 20000000 g4
    let (po, g6) := Test.below 20000000 g5
    let (sp, g7) := Test.below 10000000000 g6 -- spent up to 0.01 USD, the budget
    g := g7
    let key := fresh s!"prop{i}"
    let total := "0.01"
    let s ← setup base key (budgetJson total (pico12 sp)) (usage := s!"{p}/{ca}/{co}/stop")
      (prices := (priceText pi, priceText pc, priceText po))
    let bound := 21 * max pi pc + 100 * po
    let o ← Ask.run (env s) (args s "1") (pure "")
    let b ← parsedBudget s
    if sp + bound ≤ 10000000000 then
      let cost := (p - ca) * pi + ca * pc + co * po
      checkEq s!"property {i}: status" o.code 0
      checkEq s!"property {i}: spentUsd" b.spent ⟨sp + cost⟩
      check s!"property {i}: within the budget" (b.spent ≤ usd total)
      checkEq s!"property {i}: one entry" b.runs.size 1
    else
      checkEq s!"property {i}: refused" o.code 1
      checkEq s!"property {i}: spentUsd" b.spent ⟨sp⟩
      checkEq s!"property {i}: no entry" b.runs.size 0
    cleanup s

/-- Calls at the same time: the lock is held for the check and the record only. -/
def parallelSuite : T Unit := Test.Http.withServer fun base => do
  let fresh (tag : String) : String := s!"ask-{tag}"
  -- the lock is held for the check and for the record, not across the request: two requests of
  -- 1.5 s overlap (one after the other they need 3 s)
  do
    let s ← setup base (fresh "par") (budgetJson "10" "0") (delay := 1500)
    let t0 ← IO.monoMsNow
    let t1 ← IO.asTask (prio := .dedicated) (Ask.run (env s) (args s "1") (pure ""))
    let t2 ← IO.asTask (prio := .dedicated) (Ask.run (env s) (args s "1") (pure ""))
    let o1 ← IO.ofExcept (← IO.wait t1)
    let o2 ← IO.ofExcept (← IO.wait t2)
    let ms := (← IO.monoMsNow) - t0
    checkEq "parallel: statuses" [o1.code, o2.code] [0, 0]
    check "parallel: the requests overlap" (ms < 2800) s!"{ms} ms"
    checkEq "parallel: requests" (← requests base (fresh "par")) 2
    checkEq "parallel: spentUsd" (← parsedBudget s).spent (usd "0.000096")
    cleanup s
  -- during the request the budget file holds the bound as a reservation; the record replaces it
  -- by the cost
  do
    let s ← setup base (fresh "resv") (budgetJson "10" "0.5") (delay := 1500)
    let t1 ← IO.asTask (prio := .dedicated) (Ask.run (env s) (args s "1") (pure ""))
    IO.sleep 700
    let mid ← IO.ofExcept ((Json.parse (← IO.FS.readFile s.budget)).mapError IO.userError)
    let reservations : Array Json := (fromJson? (mid.getObjValD "reservations")).toOption.getD #[]
    checkEq "reservation: one during the request" reservations.size 1
    checkEq "reservation: the bound" (jc ((reservations[0]?.getD Json.null).getObjValD "boundUsd")) (jc (usd defaultBound).toJson)
    checkEq "reservation: spentUsd is unchanged during the request" (jc (mid.getObjValD "spentUsd")) (jc (usd "0.5").toJson)
    let o1 ← IO.ofExcept (← IO.wait t1)
    checkEq "reservation: status" o1.code 0
    let after ← IO.ofExcept ((Json.parse (← IO.FS.readFile s.budget)).mapError IO.userError)
    check "reservation: none after the record" ((after.getObjValD "reservations").getArr?.toOption.all (·.isEmpty))
    checkEq "reservation: spentUsd after" (← parsedBudget s).spent (usd "0.500048")
    cleanup s
  -- three calls at the same time, with budget for the bound of two: exactly one is refused, and
  -- the spend does not pass the budget
  do
    let s ← setup base (fresh "par3") (budgetJson "0.0005" "0") (delay := 800)
    let ts ← (List.range 3).mapM fun _ => IO.asTask (prio := .dedicated) (Ask.run (env s) (args s "1") (pure ""))
    let os ← ts.mapM fun t => do IO.ofExcept (← IO.wait t)
    checkEq "parallel, budget for two: statuses" ((os.map (·.code)).toArray.qsort (· < ·)).toList [0, 0, 1]
    checkEq "parallel, budget for two: requests" (← requests base (fresh "par3")) 2
    let b ← parsedBudget s
    checkEq "parallel, budget for two: entries" b.runs.size 2
    check "parallel, budget for two: within the budget" (b.spent ≤ usd "0.0005")
    cleanup s

def suite : T Unit := do
  pureSuite
  serverSuite
  parallelSuite

end Test.Ask
