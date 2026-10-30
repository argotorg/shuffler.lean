import Shuffler.BuildBottomUp.Defs

/-!
Run `Shuffler.Emission.buildBottomUp` on lines "m n s1 .. sm t1 .. tn d1 .. dm k v1 .. vk" and print
one line for each:

- "assertion" for an error,
- "ok OPS | STACK | DESTS" for a result that is not blocked,
- "blocked OFFSET EXCESS OPS | STACK | DESTS" for a blocked result.

`s`, `t` are the source and target values, `d` the destination of each source slot and `v` the
spilled variable ids. A value is a number: 0 is a wildcard, 1 a function return label, 2 + 2 id a
variable and 3 + 2 id a literal. An operation is "s depth", "d depth" or "p value". STACK is the
values of the final stack and DESTS the destination of each of its slots, or "-". The root project
builds it as `bbu_pr31`:

  lake exe bbu_pr31 < states.txt

The states need not be `Valid`: `run` is `buildBottomUp` without its proof argument (`run_eq`).
-/

open Shuffler Shuffler.Emission

def value (k : Nat) : Value :=
  if k = 0 then .Wildcard
  else if k = 1 then .FunctionReturnLabel
  else if k % 2 = 0 then .Var ⟨(k - 2) / 2⟩
  else .Lit (Fin.ofNat _ ((k - 3) / 2))

def number : Value → Nat
  | .Wildcard => 0
  | .FunctionReturnLabel => 1
  | .Var id => 2 + 2 * id.val
  | .Lit w => 3 + 2 * w.val

-- The operations of the trace, oldest first, followed by `acc`.
def opsOnto {spills : SpillSet} {s r : Stack} : Trace spills s r → List String → List String
  | .Lit _, acc => acc
  | .Swap idx _ _ _ t, acc => opsOnto t (s!"s {idx}" :: acc)
  | .Dup idx _ _ _ _ t, acc => opsOnto t (s!"d {idx}" :: acc)
  | .Push v _ t, acc => opsOnto t (s!"p {number v}" :: acc)
  | .Load id _ t, acc => opsOnto t (s!"p {number (.Var id)}" :: acc)
  | .Pop _ t, acc => opsOnto t ("pop" :: acc)

-- Bind each source position to its destination; none if a destination is out of range or bound twice.
def mapping? (m n : Nat) (dests : List Nat) : Option (Mapping m n) :=
  (List.finRange m).foldlM (fun mapping src => do
    let d ← dests[src.val]?
    if hd : d < n then
      if hs : mapping src = none then
        if hb : mapping.symm ⟨d, hd⟩ = none then some (mapping.bind src ⟨d, hd⟩ hs hb)
        else none
      else none
    else none) ⊥

variable {source target : Stack} {spills : SpillSet}

-- `buildBottomUp` without the proof that `initial` is valid.
def run (initial : State source target spills) : Except ShuffleErr (Result source target spills) := do
  let result ← buildBottomUp.loop 0 initial
  if result.blocked.isSome then return result
  _ ← requires (result.state.stack.length = target.length) "stack and target sizes differ"
  return result

theorem run_eq (initial : State source target spills) (h : initial.Valid) :
    run initial = buildBottomUp initial h := rfl

def render : Except ShuffleErr (Result source target spills) → String
  | .error (.assertion _) => "assertion"
  -- `buildBottomUp` returns a blocked state as a result, so this line must not occur.
  | .error (.Blocked b) => s!"error blocked {b.offset} {b.excess}"
  | .ok ⟨blocked, state⟩ =>
    let status := match blocked with
      | none => ["ok"]
      | some b => ["blocked", toString b.offset, toString b.excess]
    let stack := state.stack.map (toString ∘ number)
    let dests := (List.finRange state.stack.length).map fun i =>
      match state.mapping.destinationOf i with
      | some d => toString d.val
      | none => "-"
    " ".intercalate (status ++ opsOnto state.trace [] ++ "|" :: stack ++ "|" :: dests)

def runLine (m n : Nat) (rest : List Nat) : String :=
  let source := (rest.take m).map value
  let target := (rest.drop m |>.take n).map value
  let dests := rest.drop (m + n) |>.take m
  let k := (rest.drop (2 * m + n)).headD 0
  let spills : SpillSet :=
    (((rest.drop (2 * m + n + 1)).take k).map (fun i => (⟨i⟩ : VarId))).toFinset
  if hs : source.length = m then
    if ht : target.length = n then
      match mapping? m n dests with
      | none => "bad input"
      | some mapping =>
        render (run (source := source) (target := target) (spills := spills) {
          planned_mapping := hs ▸ ht ▸ mapping
          stack := source
          trace := .Lit source
          mapping := hs ▸ ht ▸ mapping
          pending_generations := target.length - source.length
        })
    else "bad input"
  else "bad input"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ").filterMap String.toNat? with
  | m :: n :: rest => stdout.putStrLn (runLine m n rest)
  | _ => throw <| IO.userError s!"bad line: {line}"
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
