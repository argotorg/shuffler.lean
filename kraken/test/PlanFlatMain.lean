import FlatShuffler.FlatPlan

/-!
Run the "plan" cases of `Fuzz/Oracle.lean` ("plan;STRATEGY;ALLOWED;SOURCE;TARGET;VARS", one per
line, as from `Fuzz/plan_cases.sh`) on the flat model `FlatShuffler.Flat.planEntry`, and print one line for
each in the format of the oracle: "ok SUCCESS;SAW;VARS;DROPPED[;STACK;OPS;SOURCES]" or "err" (see
`runPlan` of `Fuzz/port.cpp`). `idCount` is one more than the largest variable id of the case, as
in `Fuzz/port.cpp`. It prints "bad input" for a line that it cannot read, and "invalid ..." for a
result that the C++ cannot give. The kraken project builds it as `plan_flat`:

  lake exe plan_flat < cases.txt
-/

open FlatShuffler FlatShuffler.Flat

def slotOf? (w : String) : Option StackSlot :=
  match w.toList with
  | ['_'] => some .junk
  | ['R'] => some ⟨0, FunctionReturnLabel, Unreachable⟩
  | 'v' :: d => (String.ofList d).toNat?.map fun i => ⟨.ofNat 32 i, Value, 1⟩
  | 'l' :: d => (String.ofList d).toNat?.map fun i => ⟨.ofNat 32 i, Value, Const⟩
  | _ => none

def slotText (s : StackSlot) : String :=
  if s.kind = Junk then "_"
  else if s.kind = FunctionReturnLabel then "R"
  else s!"{if s.valueOpcode = Const then "l" else "v"}{s.payload.toNat}"

def opText (o : Op) : String :=
  match o.kind.toNat with
  | 0 => s!"SWAP{o.depth.toNat}"
  | 1 => s!"DUP{o.depth.toNat}"
  | 2 => "POP"
  | 3 => s!"PUSH:{slotText o.slot}"
  | 4 => s!"LOAD:{slotText o.slot}"
  | k => s!"? {k}"

def offsetText (w : Word) : String := if w = NONE then "-" else toString w.toNat

def words (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

-- `l` from offset 0, and `d` above it.
def vecOf {α : Type} (l : List α) (d : α) : Vector α maxStackSize := Vector.ofFn fun i => l[i.val]?.getD d

-- Content for the caller's buffers and for the locals of each attempt, which the C++ does not
-- initialize. The content differs from attempt to attempt.
def junkSlot : StackSlot := ⟨0xdeadbeef, 0xee, 0xee⟩
def uninit (k : Nat) : RunU :=
  let w (x : Nat) : Vector Word maxStackSize := Vector.replicate maxStackSize (.ofNat 64 (x + k))
  ⟨⟨w 7, w 9⟩, ⟨w 11, w 13, .ofNat 64 (77 + k), .ofNat 64 (99 + k)⟩, ⟨w 5, w 6, w 8⟩,
    ⟨Vector.replicate maxStackSize (.ofNat 8 (1 + k)), w 3⟩⟩

def below (k : Word) : List Word := (List.range k.toNat).map (BitVec.ofNat 64)

def run (take allowed : Bool) (source target : List StackSlot) (vars : List Nat) : String :=
  let ids := vars ++ (source ++ target).filterMap fun s =>
    if s.kind = Value ∧ s.valueOpcode = 1 then some s.payload.toNat else none
  let idCount := ids.foldl max 0 + 1
  let spilled (i : BitVec 32) : BitVec 8 := if vars.contains i.toNat then 1 else 0
  let m : Word := .ofNat 64 source.length
  let n : Word := .ofNat 64 target.length
  match planEntry m n (vecOf source .junk) (vecOf target .junk) spilled (.ofNat 64 idCount)
      (if allowed then 1 else 0) (if take then 1 else 0) (Vector.replicate maxStackSize 0xee)
      (Vector.replicate maxStackSize junkSlot) (Vector.replicate maxStackSize 0xeeee) uninit with
  | (r, some (status, s)) =>
    let spilledIds := (List.range idCount).filter fun i => s.spills (.ofNat 32 i) ≠ 0
    if r = -2 then "err"
    else if spilledIds.any fun i => s.spills (.ofNat 32 i) ≠ 1 then "invalid: a spilled byte"
    else
      let head := s!"ok {if r = -1 then 0 else 1};{if s.saw then 1 else 0};" ++
        s!"{" ".intercalate (spilledIds.map toString)};" ++
        " ".intercalate ((below m).map fun i => toString (get s.dropped i).toNat)
      match status with
      | .blocked => if r = -1 then head else s!"invalid: blocked with the result {r.toInt}"
      | .done =>
        if r ≠ .ofNat 64 s.trace.length then s!"invalid: the result is {r.toInt}"
        else
          s!"{head};{" ".intercalate ((below n).map (slotText ∘ get s.data))};" ++
            s!"{" ".intercalate (s.trace.map opText)};" ++
            " ".intercalate ((below n).map (offsetText ∘ get s.sources))
      | .assertionExit => s!"invalid: failed with the result {r.toInt}"
  | (r, none) => if r = -2 then "err" else s!"invalid: no state, the result is {r.toInt}"

def runLine (line : String) : Option String := do
  let [tag, strategy, allowed, source, target, vars] := line.splitOn ";" | none
  guard (tag = "plan")
  let take ← match strategy with | "L" => some false | "T" => some true | _ => none
  let allowed ← match allowed with | "0" => some false | "1" => some true | _ => none
  let source ← (words source).mapM slotOf?
  let target ← (words target).mapM slotOf?
  let vars ← (words vars).mapM String.toNat?
  guard (source.length ≤ maxStackSize ∧ target.length ≤ maxStackSize)
  return run take allowed source target vars

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn ((runLine (line.trimAscii.toString)).getD "bad input")
  loop stdin stdout

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)
