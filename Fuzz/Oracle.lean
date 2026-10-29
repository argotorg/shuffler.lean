import Shuffler.BuildMapping.Defs
import Shuffler.RemoveSurplus.Defs
import Shuffler.PermuteAtLowestHeight.Defs
import Shuffler.BuildBottomUp.Defs
import Shuffler.Emission.Run.Defs
import Shuffler.Planner.Run.Defs

/-
The Lean side of the differential fuzzer in Fuzz/fuzz.cpp. A case and its result are each one line of
text, so that both implementations parse the same input and print the same output.

  case   := "map;" strategy ";" stack ";" stack ";" bytes      buildMapping of source, target, dropped
          | "surplus;" state                                   removeSurplus
          | "lowest;" state                                    permuteAtLowestHeight
          | "bottomup;" state                                  buildBottomUp
          | "emit;" state                                      Emission.run
          | "permute;" stack ";" offsets                       permute, with the destination of each offset
          | "plan;" strategy ";" bit ";" stack ";" stack ";" vars
                                                               Planner.run of spillingAllowed, source, target, spills
  state  := stack ";" stack ";" dests ";" vars                 stack, target, mapping and spilled variables
  dests  := per stack offset a target offset or "-"
  slot   := "v" n | "l" n | "_" | "R"                          Var, Lit, Wildcard, FunctionReturnLabel

  result := "ok " bit ";" sources                              buildMapping: sawWildcardCopy, per target offset a
                                                               source offset or "-"
          | status ";" stack ";" ops ";" dests                 the state steps, also when blocked
          | "ok " bit ";" bit ";" vars ";" bytes [";" stack ";" ops ";" sources]
                                                               Planner.run: success, sawWildcardCopy, spills, dropped,
                                                               and on success the emitted stack and the plan
          | "err"
          | "invalid"                                          the buildBottomUp state is not `Valid`
  status := "ok" | "blocked " offset " " excess
  op     := "SWAP" n | "DUP" n | "POP" | "PUSH:" slot | "LOAD:" slot
-/

open Shuffler Shuffler.Emission

namespace Oracle

--- Parsing ----------------------------------------------------------------------------------------

def words (s : String) : List String :=
  (s.splitOn " ").filter (· ≠ "")

def parseNat (s : String) : Except String ℕ :=
  s.toNat?.elim (.error s!"not a number: {s}") .ok

def parseSlot (s : String) : Except String Value :=
  match s.toList with
  | ['_'] => .ok .Wildcard
  | ['R'] => .ok .FunctionReturnLabel
  | 'v' :: n => return .Var ⟨← parseNat (String.ofList n)⟩
  | 'l' :: n => return .Lit (Fin.ofNat _ (← parseNat (String.ofList n)))
  | _ => .error s!"not a slot: {s}"

def parseStack (s : String) : Except String Stack :=
  (words s).mapM parseSlot

def parseByte (s : String) : Except String Byte := do
  let n ← parseNat s
  if h : n < 2 ^ 8 then return ⟨n, h⟩ else .error s!"not a byte: {s}"

def parseStrategy : String → Except String BuildMapping.WildcardSlotsStrategy
  | "L" => .ok .Leave
  | "T" => .ok .Take
  | s => .error s!"not a strategy: {s}"

def parseDest (s : String) : Except String (Option ℕ) :=
  if s = "-" then .ok none else some <$> parseNat s

-- Binds stack offset i to dests[i]; fails unless dests has one entry per stack offset and binds every
-- target offset at most once.
def parseMapping (n m : ℕ) (s : String) : Except String (Mapping n m) := do
  let dests ← (words s).mapM parseDest
  unless dests.length = n do throw s!"not one destination per offset: {s}"
  (List.finRange n).foldlM (init := ⊥) fun mapping i => do
    let some j := dests[i.val]?.join | return mapping
    if hj : j < m then
      if hi : mapping i = none then
        if hu : mapping.symm ⟨j, hj⟩ = none then return mapping.bind i ⟨j, hj⟩ hi hu
      throw s!"destination bound twice: {j}"
    else throw s!"destination out of range: {j}"

--- Printing ---------------------------------------------------------------------------------------

def showSlot : Value → String
  | .Var id => s!"v{id.val}"
  | .Lit word => s!"l{word.val}"
  | .Wildcard => "_"
  | .FunctionReturnLabel => "R"

def showStack (stack : Stack) : String :=
  " ".intercalate (stack.map showSlot)

def showOffset : Option (Fin n) → String
  | some i => toString i.val
  | none => "-"

def showBit (b : Bool) : String := if b then "1" else "0"

def ops : Trace spills source result → List String
  | .Lit _ => []
  | .Swap idx _ _ _ trace => ops trace ++ [s!"SWAP{idx}"]
  | .Dup idx _ _ _ _ trace => ops trace ++ [s!"DUP{idx}"]
  | .Pop _ trace => ops trace ++ ["POP"]
  | .Push value _ trace => ops trace ++ [s!"PUSH:{showSlot value}"]
  | .Load id _ trace => ops trace ++ [s!"LOAD:{showSlot (.Var id)}"]

def showErr : ShuffleErr → String
  | .Blocked b => s!"blocked {b.offset} {b.excess}"
  | .assertion _ => "err"

def showResult : Except ShuffleErr (Result source target spills) → String
  | .ok ⟨blocked, s⟩ =>
    let status := match blocked with
      | none => "ok"
      | some b => s!"blocked {b.offset} {b.excess}"
    let dests := (List.finRange s.stack.length).map fun i => showOffset (s.mapping.destinationOf i)
    s!"{status};{showStack s.stack};{" ".intercalate (ops s.trace)};{" ".intercalate dests}"
  | .error e => showErr e

--- Runners ----------------------------------------------------------------------------------------

def initial (stack target : Stack) (spills : SpillSet) (mapping : Mapping stack.length target.length) :
    State stack target spills where
  planned_mapping := mapping
  stack := stack
  trace := .Lit stack
  mapping := mapping
  pending_generations := (List.finRange target.length).countP (mapping.symm · = none)

instance (state : State source target spills) : Decidable state.Valid :=
  decidable_of_iff
    (state.stack.length + state.pending_generations = target.length ∧
      state.mapping.unmapped_target_slots = state.pending_generations ∧
      (∀ j, state.isAvailable j) ∧
      ∀ j, target[j].isFunctionReturnLabel → (state.mapping.symm j).isSome)
    ⟨fun ⟨hs, hp, ha, hl⟩ => ⟨hs, hp, ha, hl⟩,
      fun h => ⟨h.size, h.pending, h.available, h.labels_bound⟩⟩

def parseSpills (s : String) : Except String SpillSet := do
  return ((← (words s).mapM parseNat).map VarId.mk).toFinset

def runBuildMapping : List String → Except String String
  | [strategy, source, target, dropped] => do
    let source ← parseStack source
    let target ← parseStack target
    let result := BuildMapping.buildMapping source target (← (words dropped).mapM parseByte)
      (← parseStrategy strategy)
    return match result with
      | .ok r =>
        let sources := (List.finRange target.length).map fun j => showOffset (r.mapping.symm j)
        s!"ok {showBit r.sawWildcardCopy};{" ".intercalate sources}"
      | .error _ => "err"
  | _ => .error "not a buildMapping case"

def runBuildBottomUp (state : State source target spills) : String :=
  if h : state.Valid then showResult (buildBottomUp state h) else "invalid"

def runOnState (run : ∀ {source target : Stack} {spills : SpillSet}, State source target spills → String) :
    List String → Except String String
  | [stack, target, dests, vars] => do
    let stack ← parseStack stack
    let target ← parseStack target
    let mapping ← parseMapping stack.length target.length dests
    return run (initial stack target (← parseSpills vars) mapping)
  | _ => .error "not a state"

def runPermute : List String → Except String String
  | [stack, dests] => do
    let stack ← parseStack stack
    let mapping ← parseMapping stack.length stack.length dests
    if h : ∀ i, (mapping i).isSome then
      let perm := mapping.toPermutation rfl h
      -- the target is the permuted stack, so that the mapping binds every slot to its destination
      let target := Permute.apply_permutation stack perm
      let state := initial stack target ∅ (by simpa [target, Permute.apply_permutation] using mapping)
      return showResult (Permute.permute state perm)
    else .error s!"not a permutation: {dests}"
  | _ => .error "not a permute case"

def runPlanner : List String → Except String String
  | [strategy, allowed, source, target, vars] => do
    let source ← parseStack source
    let target ← parseStack target
    let inputSpills ← (words vars).mapM parseNat
    let allowed ← match allowed with
      | "0" => pure false
      | "1" => pure true
      | s => throw s!"not a bit: {s}"
    let result := Planner.run source target ((inputSpills.map VarId.mk).toFinset) allowed
      (← parseStrategy strategy)
    return match result with
      | .ok r =>
        -- the planner only spills source values, so every spilled id is in the case
        let ids := (source ++ target).filterMap (fun | .Var id => some id.val | _ => none) ++ inputSpills
        let spilled := (ids.dedup.mergeSort (· ≤ ·)).filter (VarId.mk · ∈ r.state.spills)
        let dropped := r.state.dropped.toList.map (toString ·.val)
        let head := s!"ok {showBit r.result.isSome};{showBit r.sawWildcardCopy};" ++
          s!"{" ".intercalate (spilled.map toString)};{" ".intercalate dropped}"
        match r.result with
        | none => head
        | some s =>
          let sources := (List.finRange target.length).map fun j => showOffset (s.planned_mapping.symm j)
          s!"{head};{showStack s.stack};{" ".intercalate (ops s.trace)};{" ".intercalate sources}"
      | .error _ => "err"
  | _ => .error "not a planner case"

def run (line : String) : Except String String :=
  match line.splitOn ";" with
  | "map" :: fields => runBuildMapping fields
  | "surplus" :: fields => runOnState (showResult <| removeSurplus ·) fields
  | "lowest" :: fields =>
    runOnState (showResult <| Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight ·) fields
  | "bottomup" :: fields => runOnState runBuildBottomUp fields
  | "emit" :: fields =>
    runOnState (fun {source target spills} (s : State source target spills) =>
      showResult (Emission.run source target s.planned_mapping spills)) fields
  | "permute" :: fields => runPermute fields
  | "plan" :: fields => runPlanner fields
  | _ => .error s!"not a case: {line}"

end Oracle

-- Runs one case line. Fuzz/fuzz.cpp calls this through the C FFI.
@[export shuffler_lean_run]
def runLine (line : String) : String :=
  match Oracle.run line with
  | .ok result => result
  | .error e => s!"parse error: {e}"
