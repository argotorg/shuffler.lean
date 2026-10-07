import Lean
import Shuffler
import Shuffler.BuildMapping
import Shuffler.Optimality.Replay
import Shuffler.Optimality.ValueGraph
import Shuffler.Optimality.Schedule.Theorems
import Shuffler.Optimality.ShortGrowth.Build
import Shuffler.Optimality.Baseline
import Shuffler.Optimality.Approximation.Build
import Shuffler.Optimality.SwapRuns.Theorems
import Shuffler.Optimality.BirthPlacement.Improve
import Shuffler.Optimality.BirthPlacement.SourceRealize
import Shuffler.Optimality.BirthPlacement.SourceCheapest

/-!
JSONL bridge for offline benchmarks. Every accepted operation list is checked
by production replayExact. Reduced-cap oracle cases are replayed as witnesses
under the real limits, but are not compared to production planners.
-/

open Lean Shuffler.Optimality

set_option maxRecDepth 16384

namespace OptimalityBench

structure Problem where
  id : String
  source : Stack
  target : Stack
  missing : Stack
  spills : SpillSet
  weights : Weights
  loadWidths : List (Nat × Nat)
  cppEstimate : Bool
  actualCaps : Bool
  mapping : Option (List Nat)
  reference : Option (List Op)
  algorithms : Option (List String)

private def optional [FromJson α] (json : Json) (key : String) (fallback : α) : Except String α :=
  match json.getObjVal? key with
  | .ok value => fromJson? value
  | .error _ => .ok fallback

private def parseValue (encoded : String) : Except String Value := do
  if encoded == "wildcard" then return .Wildcard
  if encoded == "return" then return .FunctionReturnLabel
  let parts := encoded.splitOn ":"
  match parts with
  | [kind, digits] =>
    let some number := digits.toNat? | throw "invalid value number"
    if kind == "v" then return .Var ⟨number⟩
    else if kind == "l" then
      if h : number < 2 ^ 256 then return .Lit ⟨number, h⟩
      else throw "literal exceeds 256 bits"
    else throw "unknown value kind"
  | _ => throw "invalid value encoding"

private def parseStack (json : Json) : Except String Stack := do
  let values : List String ← fromJson? json
  values.mapM parseValue

private def parseOp (json : Json) : Except String Op := do
  let args ← json.getArr?
  let some opcode := args[0]? | throw "empty operation"
  let name ← opcode.getStr?
  if name == "pop" && args.size == 1 then return .pop
  if args.size != 2 then throw "operation needs one argument"
  let some argument := args[1]? | throw "missing operation argument"
  match name with
  | "swap" => return .swap (← argument.getNat?)
  | "dup" => return .dup (← argument.getNat?)
  | "load" => return .load ⟨← argument.getNat?⟩
  | "push" => return .push (← parseValue (← argument.getStr?))
  | _ => throw "unknown operation"

private def algorithmNames : List String :=
  ["old-bbu", "complete", "value-graph", "value-graph-certified", "short-growth", "append-only", "schedule-balanced", "schedule-eager", "schedule-preserve", "schedule-relaxed-balanced", "schedule-relaxed-eager", "schedule-relaxed-preserve", "schedule-chains-balanced", "schedule-chains-eager", "schedule-chains-preserve", "schedule-chain", "schedule"]

private def parseProblem (json : Json) : Except String Problem := do
  let id ← optional json "id" "unnamed"
  let source ← parseStack (← json.getObjVal? "source")
  let target ← parseStack (← json.getObjVal? "target")
  let missing ← match json.getObjVal? "missing" with
    | .ok value => parseStack value
    | .error _ => pure (target.diff source)
  let spillIds : List Nat ← optional json "spills" []
  let weightsJson ← optional json "weights" (Json.mkObj [("gas", toJson (1 : Nat)), ("bytes", toJson (1 : Nat))])
  let gas ← weightsJson.getObjValAs? Nat "gas"
  let bytes ← weightsJson.getObjValAs? Nat "bytes"
  let weights ← if h : 0 < gas ∨ 0 < bytes then pure (Weights.mk gas bytes h)
    else throw "both weights are zero"
  let widths : List (List Nat) ← optional json "loadWidths" []
  let loadWidths ← widths.mapM fun pair => match pair with
    | [id, width] => if width ≤ 32 then pure (id, width) else throw "LOAD width exceeds 32"
    | _ => throw "LOAD width needs id and width"
  let gasModel ← optional json "gasModel" "cpp"
  if gasModel != "cpp" && gasModel != "evm" then throw "unknown gas model"
  let caps ← optional json "caps" (Json.mkObj [("swap", toJson (16 : Nat)), ("dup", toJson (16 : Nat))])
  let swapCap ← caps.getObjValAs? Nat "swap"
  let dupCap ← caps.getObjValAs? Nat "dup"
  if swapCap < 1 || swapCap > 16 || dupCap != swapCap then throw "unsupported cap pair"
  let mapping : Option (List Nat) ← match json.getObjVal? "mapping" with
    | .ok value => (fromJson? value : Except String (List Nat)).map some
    | .error _ => pure none
  let reference : Option (List Op) ← match json.getObjVal? "referenceOps" with
    | .ok value => value.getArr? >>= fun values => (values.toList.mapM parseOp).map some
    | .error _ => pure none
  let algorithms : Option (List String) ← optional json "algorithms" none
  let allowedAlgorithms := algorithmNames ++ ["normalize-reference", "normalize-reference-twice",
    "birth-reference", "source-reference", "source-cheapest-reference", "postpass-reference"]
  if !(algorithms.getD []).all allowedAlgorithms.contains then throw "unknown algorithm selection"
  return {
    id := id
    source := source
    target := target
    missing := missing
    weights := weights
    loadWidths := loadWidths
    mapping := mapping
    reference := reference
    algorithms := algorithms
    spills := (spillIds.map VarId.mk).toFinset
    cppEstimate := gasModel == "cpp"
    actualCaps := swapCap == 16 }

private def encodeValue : Value → String
  | .Lit word => "l:" ++ toString word.val
  | .Var id => "v:" ++ toString id.val
  | .Wildcard => "wildcard"
  | .FunctionReturnLabel => "return"

private def opJson : Op → Json
  | .swap depth => toJson ([toJson "swap", toJson depth] : List Json)
  | .dup index => toJson ([toJson "dup", toJson index] : List Json)
  | .load id => toJson ([toJson "load", toJson id.val] : List Json)
  | .push value => toJson ([toJson "push", toJson (encodeValue value)] : List Json)
  | .pop => toJson ([toJson "pop"] : List Json)

private def costJson (cost : Cost) : Json := Json.mkObj [
  ("gas", toJson cost.gas), ("bytes", toJson cost.bytes)]

private def pushEncoding : Value → PushEncoding
  | .Lit word =>
    if word.val == 0 then .push0
    else
      let widthMinusOne := word.val.log2 / 8
      if h : widthMinusOne < 32 then .push ⟨widthMinusOne, h⟩ else .push ⟨31, by decide⟩
  | _ => .push0

private def addressEncoding (problem : Problem) (id : VarId) : PushEncoding :=
  let width := ((problem.loadWidths.find? (fun pair => pair.1 == id.val)).map Prod.snd).getD 1
  if width == 0 then .push0
  else if h : width - 1 < 32 then .push ⟨width - 1, h⟩ else .push ⟨31, by decide⟩

private def costs (problem : Problem) : PrimitiveCosts :=
  if problem.cppEstimate then PrimitiveCosts.cppEstimate pushEncoding (addressEncoding problem)
  else PrimitiveCosts.evm pushEncoding (addressEncoding problem)

private def observed (problem : Problem) (ops : List Op) (certificate : Option String := none) : Json :=
  match replayExact problem.spills problem.source problem.target
      (problem.missing : Multiset Value) ops with
  | none => Json.mkObj [("status", toJson "invalid"), ("ops", toJson (ops.map opJson))]
  | some built =>
    let cost := traceCost (costs problem) built.trace
    let base := baseline (costs problem) problem.weights problem.spills
      problem.source (problem.missing : Multiset Value)
    let excess := lineageBound (costs problem) problem.weights problem.spills
      problem.source problem.target (problem.missing : Multiset Value)
    let staticExcess := (staticExcessLowerBound (costs problem) problem.weights problem.spills
      problem.source problem.target (problem.missing : Multiset Value)).excess
    let certificates := Json.mkObj [
      ("exactBaseline", toJson (cost.score problem.weights == base)),
      ("exactLineage", toJson (cost.score problem.weights == base + excess)),
      ("exactStatic", toJson (cost.score problem.weights == base + staticExcess)),
      ("exactNoGrowth", toJson (certificate == some "no-growth-weighted-optimality")),
      ("twiceLineage", toJson ((certifyTwiceLineage (costs problem) problem.weights built).isSome)),
      ("twiceStatic", toJson ((certifyTwiceStatic (costs problem) problem.weights built).isSome))]
    Json.mkObj [("status", toJson "ok"), ("cost", costJson cost),
      ("score", toJson (cost.score problem.weights)), ("instructions", toJson ops.length),
      ("certificate", toJson certificate),
      ("certificates", certificates),
      ("ops", toJson (ops.map opJson))]

private def noneResult : Json := Json.mkObj [("status", toJson "none")]

private def assignedMapping (source target : Stack) (destinations : List Nat) :
    Except String (Mapping source.length target.length) := do
  if destinations.length != source.length then throw "mapping has wrong length"
  (List.finRange source.length).foldlM (fun mapping sourceIndex => do
    let some destination := destinations[sourceIndex.val]? | throw "mapping lacks source"
    if hd : destination < target.length then
      let targetIndex : Fin target.length := ⟨destination, hd⟩
      if source[sourceIndex] != target[targetIndex] then throw "mapping changes a value"
      if hs : mapping sourceIndex = none then
        if ht : mapping.symm targetIndex = none then return mapping.bind sourceIndex targetIndex hs ht
        else throw "mapping is not injective"
      else throw "source is already mapped"
    else throw "mapping target index is out of range") (⊥ : Mapping source.length target.length)

private def defaultMapping (source target : Stack) : Mapping source.length target.length :=
  let builder := MappingBuilder.buildMapping source target (List.replicate source.length 0)
    .Leave (by simp)
  builder.mapping

private def runOld (problem : Problem) : Json :=
  let mappingResult := match problem.mapping with
    | some destinations => assignedMapping problem.source problem.target destinations
    | none => .ok (defaultMapping problem.source problem.target)
  match mappingResult with
  | .error reason => Json.mkObj [("status", toJson "invalid-input"), ("reason", toJson reason)]
  | .ok mapping =>
    let state : State problem.source problem.target problem.spills := {
      planned_mapping := mapping, stack := problem.source, trace := .Lit problem.source,
      mapping, pending_generations := problem.missing.length }
    let valid := decide (state.stack.length + state.pending_generations = problem.target.length ∧
      state.mapping.unmapped_target_slots = state.pending_generations ∧ ∀ i, state.isAvailable i)
    if !valid then Json.mkObj [("status", toJson "invalid-state")]
    else match Shuffler.BuildBottomUp.buildBottomUp state with
      | .error error => Json.mkObj [("status", toJson "error"), ("reason", toJson (reprStr error))]
      | .ok result => observed problem (flatten result.2)

private def runComplete (problem : Problem) : Json :=
  match Shuffler.Placement.build problem.spills problem.source problem.target
      (problem.missing : Multiset Value) with
  | none => noneResult
  | some built => observed problem (flatten built.trace)

private def runValueGraph (problem : Problem) : Json :=
  if problem.missing.isEmpty then
    match Shuffler.Optimality.ValueGraph.build problem.spills problem.source problem.target with
    | none => noneResult
    | some built => observed problem (flatten built.trace)
  else Json.mkObj [("status", toJson "not-applicable")]

private def runValueGraphCertified (problem : Problem) : Json :=
  if problem.missing.isEmpty then
    match Shuffler.Optimality.ValueGraph.buildCertified problem.spills problem.source problem.target with
    | none => noneResult
    | some result => observed problem (flatten result.built.trace) (some "no-growth-weighted-optimality")
  else Json.mkObj [("status", toJson "not-applicable")]

private def runShortGrowth (problem : Problem) : Json :=
  let fixed := problem.target.length - (MAX_SWAP_DEPTH + 1)
  if fixed ≤ problem.source.length ∧ problem.target.take fixed = problem.source.take fixed then
    match ShortGrowth.build (costs problem) problem.weights problem.spills
        problem.source problem.target (problem.missing : Multiset Value) with
    | none => noneResult
    | some built => observed problem (flatten built.trace)
  else Json.mkObj [("status", toJson "not-applicable")]

private def runScheduleCandidate (strategy : Schedule.Strategy) (problem : Problem) : Json :=
  match Schedule.plan strategy (costs problem) problem.weights problem.spills
      problem.source problem.target (problem.missing : Multiset Value) with
  | none => noneResult
  | some ops => observed problem ops

private def runAppendOnly (problem : Problem) : Json :=
  if problem.target.take problem.source.length = problem.source then
    match Schedule.appendCandidate (costs problem) problem.weights problem.spills
        problem.source problem.target (problem.missing : Multiset Value) with
    | none => noneResult
    | some built => observed problem (flatten built.trace)
  else Json.mkObj [("status", toJson "not-applicable")]

private def runSchedule (problem : Problem) : Json :=
  match Schedule.build (costs problem) problem.weights problem.spills problem.source
      problem.target (problem.missing : Multiset Value) with
  | none => noneResult
  | some built => observed problem (flatten built.trace)

private def runNormalizeReference (twice : Bool) (problem : Problem) : Json :=
  match problem.reference with
  | none => Json.mkObj [("status", toJson "not-applicable")]
  | some ops =>
    match replayExact problem.spills problem.source problem.target
        (problem.missing : Multiset Value) ops with
    | none => Json.mkObj [("status", toJson "invalid-reference")]
    | some built =>
      let normalized := SwapRuns.normalizeBuilt built
      let result := if twice then SwapRuns.normalizeBuilt normalized else normalized
      observed problem (flatten result.trace)

-- These benchmark modes consume saved traces. They do not run a portfolio.
private def runBirthReference (problem : Problem) : Json :=
  if hs : problem.source = [] then
    match problem.reference with
    | none => Json.mkObj [("status", toJson "not-applicable")]
    | some ops =>
      match replayExact problem.spills problem.source problem.target
          (problem.missing : Multiset Value) ops with
      | none => Json.mkObj [("status", toJson "invalid-reference")]
      | some built =>
        let empty := built.cast hs rfl rfl
        let improved := BirthPlacement.improveTraceWord (costs problem) problem.weights
          empty.trace empty.noPop
        observed problem (flatten improved)
  else Json.mkObj [("status", toJson "not-applicable")]

private def runSourceReference (problem : Problem) : Json :=
  match problem.reference with
  | none => Json.mkObj [("status", toJson "not-applicable")]
  | some ops =>
    match replayExact problem.spills problem.source problem.target
        (problem.missing : Multiset Value) ops with
    | none => Json.mkObj [("status", toJson "invalid-reference")]
    | some built =>
      let candidate := BirthPlacement.canonicalizeTraceAssignment built.trace built.noPop
      observed problem (flatten candidate.built.trace)

private def runSourceCheapestReference (problem : Problem) : Json :=
  match problem.reference with
  | none => Json.mkObj [("status", toJson "not-applicable")]
  | some ops =>
    match replayExact problem.spills problem.source problem.target
        (problem.missing : Multiset Value) ops with
    | none => Json.mkObj [("status", toJson "invalid-reference")]
    | some built =>
      let candidate := BirthPlacement.optimizeTraceAssignment (costs problem) problem.weights
        built.trace built.noPop
      observed problem (flatten candidate.built.trace)

private def runPostpassReference (problem : Problem) : Json :=
  match problem.reference with
  | none => Json.mkObj [("status", toJson "not-applicable")]
  | some ops =>
    match replayExact problem.spills problem.source problem.target
        (problem.missing : Multiset Value) ops with
    | none => Json.mkObj [("status", toJson "invalid-reference")]
    | some built =>
      observed problem (flatten (Schedule.postPass (costs problem) problem.weights built).trace)

private def runProblem (problem : Problem) : IO Json := do
  let start ← IO.monoNanosNow
  let actualReserve := decide (Shuffler.Placement.Reserve problem.spills problem.source problem.target
    (problem.missing : Multiset Value))
  let tasks : List (String × (Unit → Json)) := [
      ("old-bbu", fun _ => runOld problem), ("complete", fun _ => runComplete problem), ("value-graph", fun _ => runValueGraph problem),
      ("value-graph-certified", fun _ => runValueGraphCertified problem),
      ("short-growth", fun _ => runShortGrowth problem),
      ("append-only", fun _ => runAppendOnly problem),
      ("schedule-balanced", fun _ => runScheduleCandidate .balanced problem),
      ("schedule-eager", fun _ => runScheduleCandidate .eager problem),
      ("schedule-preserve", fun _ => runScheduleCandidate .preserve problem),
      ("schedule-relaxed-balanced", fun _ => runScheduleCandidate (Schedule.Strategy.balanced.withMode .relaxed) problem),
      ("schedule-relaxed-eager", fun _ => runScheduleCandidate (Schedule.Strategy.eager.withMode .relaxed) problem),
      ("schedule-relaxed-preserve", fun _ => runScheduleCandidate (Schedule.Strategy.preserve.withMode .relaxed) problem),
      ("schedule-chains-balanced", fun _ => runScheduleCandidate (Schedule.Strategy.balanced.withMode .chains) problem),
      ("schedule-chains-eager", fun _ => runScheduleCandidate (Schedule.Strategy.eager.withMode .chains) problem),
      ("schedule-chains-preserve", fun _ => runScheduleCandidate (Schedule.Strategy.preserve.withMode .chains) problem),
      ("schedule-chain", fun _ => runScheduleCandidate .chain problem),
      ("schedule", fun _ => runSchedule problem),
      ("normalize-reference", fun _ => runNormalizeReference false problem),
      ("normalize-reference-twice", fun _ => runNormalizeReference true problem),
      ("birth-reference", fun _ => runBirthReference problem),
      ("source-reference", fun _ => runSourceReference problem),
      ("source-cheapest-reference", fun _ => runSourceCheapestReference problem),
      ("postpass-reference", fun _ => runPostpassReference problem)]
  let algorithms := if problem.actualCaps then Json.mkObj (tasks.filterMap fun (name, run) =>
      if (problem.algorithms.map (fun selected => selected.contains name)).getD
          (algorithmNames.contains name) then some (name, run ()) else none)
    else Json.mkObj []
  let reference := problem.reference.map (observed problem)
  let result := Json.mkObj [
    ("id", toJson problem.id), ("actualReserve", toJson actualReserve),
    ("generationBaseline", toJson (baseline (costs problem) problem.weights problem.spills
      problem.source (problem.missing : Multiset Value))),
    ("lineageExcess", toJson (lineageBound (costs problem) problem.weights problem.spills
      problem.source problem.target (problem.missing : Multiset Value))),
    ("staticExcess", toJson ((staticExcessLowerBound (costs problem) problem.weights problem.spills
      problem.source problem.target (problem.missing : Multiset Value)).excess)),
    ("actualCaps", toJson problem.actualCaps), ("algorithms", algorithms),
    ("reference", toJson reference)]
  -- Force serialization inside the measured interval. This includes replay.
  let serialized := result.compress
  let count := serialized.utf8ByteSize
  let stop ← IO.monoNanosNow
  return Json.mkObj [("result", result), ("elapsedNanos", toJson (stop - start)),
    ("jsonBytes", toJson count)]

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    if line.trimAscii.toString.isEmpty then continue
    let parsed := Json.parse line >>= parseProblem
    let result ← match parsed with
      | .error reason => pure (Json.mkObj [("error", toJson reason)])
      | .ok problem => runProblem problem
    stdout.putStrLn result.compress
    stdout.flush

end OptimalityBench

def main : IO Unit := OptimalityBench.main
