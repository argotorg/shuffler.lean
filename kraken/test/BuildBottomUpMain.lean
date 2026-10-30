import Shuffler.BuildBottomUp.Defs

/-!
Run the original `Shuffler.Emission.buildBottomUp` on lines
"m n s1 .. sm t1 .. tn d1 .. dm k v1 .. vk" and print the operations as
"ok op1 .. opj", "blocked offset excess", "assertion" or "invalid". `s`, `t` are
the source and target values, `d` the destination of each source slot and `v`
the spilled variable ids. A function return label in the target must be bound
(`State.Valid.labels_bound`); else the line is "invalid". A value is a number: 0 is a wildcard, 1 a function
return label, 2 + 2 id a variable and 3 + 2 id a literal. An operation is
"s depth", "d depth" or "p value". The root project builds it as `bbu_original`:

  lake exe bbu_original < states.txt
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

def ops {spills : SpillSet} {s r : Stack} : Trace spills s r → List String
  | .Lit _ => []
  | .Swap idx _ _ _ t => ops t ++ [s!"s {idx}"]
  | .Dup idx _ _ _ _ t => ops t ++ [s!"d {idx}"]
  | .Push v _ t => ops t ++ [s!"p {number v}"]
  | .Load id _ t => ops t ++ [s!"p {number (.Var id)}"]
  | .Pop _ t => ops t ++ ["pop"]

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

def render {source target : Stack} {spills : SpillSet} :
    Except ShuffleErr (Result source target spills) → String
  | .ok ⟨none, state⟩ => " ".intercalate ("ok" :: ops state.trace)
  | .ok ⟨some b, _⟩ => s!"blocked {b.offset} {b.excess}"
  | .error (.Blocked b) => s!"blocked {b.offset} {b.excess}"
  | .error (.assertion _) => "assertion"

def run (m n : Nat) (rest : List Nat) : String :=
  let source := (rest.take m).map value
  let target := (rest.drop m |>.take n).map value
  let dests := rest.drop (m + n) |>.take m
  let spills : SpillSet := ((rest.drop (2 * m + n)).drop 1).map (fun i => (⟨i⟩ : VarId)) |>.toFinset
  if hs : source.length = m then
    if ht : target.length = n then
      match mapping? m n dests with
      | none => "invalid"
      | some mapping =>
        let state : State source target spills := {
          planned_mapping := hs ▸ ht ▸ mapping
          stack := source
          trace := .Lit source
          mapping := hs ▸ ht ▸ mapping
          pending_generations := target.length - source.length
        }
        if hsize : state.stack.length + state.pending_generations = target.length then
          if hpending : state.mapping.unmapped_target_slots = state.pending_generations then
            if havailable : ∀ i, state.isAvailable i then
              if hlabels : ∀ j, target[j].isFunctionReturnLabel → (state.mapping.symm j).isSome then
                render (buildBottomUp state ⟨hsize, hpending, havailable, hlabels⟩)
              else "invalid"
            else "invalid"
          else "invalid"
        else "invalid"
    else "invalid"
  else "invalid"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ").filterMap String.toNat? with
  | m :: n :: rest => stdout.putStrLn (run m n rest)
  | _ => throw <| IO.userError s!"bad line: {line}"
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
