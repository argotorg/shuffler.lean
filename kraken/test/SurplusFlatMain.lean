import FlatShuffler.FlatSurplus

/-!
Run the "surplus" cases of `Fuzz/Oracle.lean` ("surplus;STACK;TARGET;DESTS;VARS", one per line,
as from `Fuzz/surplus_cases.sh`) on the flat model `FlatShuffler.Flat.remove_surplus`, or with the argument
`list` on the list model `FlatShuffler.Map.State.removeSurplus` of `Map.State.init` of `Map.plan`, and print
one line for each in the format of the oracle: "ok;STACK;OPS;DESTS",
"blocked OFFSET EXCESS;STACK;OPS;DESTS" or "err" (see `c/surplus_harness.c`). It prints
"bad input" for a line that it cannot read. The kraken project builds it as `surplus_flat`:

  lake exe surplus_flat [list] < cases.txt

The functions that read and print slots are those of `PopFlatMain.lean`.
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
  if o = Op.pop then "POP"
  else if o.kind = Swap ∧ o.slot = .junk then s!"SWAP{o.depth.toNat}"
  else s!"? {o.kind.toNat}"

def offsetText : Option Nat → String
  | some d => toString d
  | none => "-"

def words (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

def destOf? (w : String) : Option (Option Nat) := if w = "-" then some none else w.toNat?.map some

-- `l` from offset 0, and `d` above it.
def vecOf {α : Type} (l : List α) (d : α) : Vector α maxStackSize := Vector.ofFn fun i => l[i.val]?.getD d

-- Content for the members that the constructor does not initialize, and for the arrays of the
-- planned mapping.
def uninit : Uninit := ⟨Vector.replicate maxStackSize 7, Vector.replicate maxStackSize 7, 77, 99⟩
def uninitMapping : Mapping := ⟨Vector.replicate maxStackSize 9, Vector.replicate maxStackSize 9⟩

def word? (d : Option Nat) : Word := match d with
  | some d => .ofNat 64 d
  | none => NONE

def opt (w : Word) : Option Nat := if w = NONE then none else some w.toNat

def render (blocked : Option (Nat × Nat)) (stack : List StackSlot) (trace : List Op)
    (dests : List (Option Nat)) : String :=
  let status := match blocked with
    | some (o, e) => s!"blocked {o} {e}"
    | none => "ok"
  ";".intercalate [status, " ".intercalate (stack.map slotText), " ".intercalate (trace.map opText),
    " ".intercalate (dests.map offsetText)]

def runFlat (stack target : List StackSlot) (ds : List (Option Nat)) (vars : List Nat) : String :=
  let m : Word := .ofNat 64 stack.length
  let n : Word := .ofNat 64 target.length
  let spills (i : BitVec 32) : BitVec 8 := if vars.contains i.toNat then 1 else 0
  match remove_surplus m n (vecOf stack .junk) (vecOf target .junk) (vecOf (ds.map word?) 0) spills
      uninit uninitMapping with
  | (r, some (status, st)) =>
    if r = -2 then "err"
    else if r ≠ .ofNat 64 st.trace.length then s!"invalid: the result is {r.toInt}"
    else
      let below (k : Word) := (List.range k.toNat).map (BitVec.ofNat 64)
      let blocked := match status with
        | .blocked => some (st.blockedOffset.toNat, st.blockedExcess.toNat)
        | _ => none
      render blocked ((below st.size).map (get st.data)) st.trace
        ((below st.size).map (opt ∘ get st.dest))
  | (r, none) => if r = -2 then "err" else s!"invalid: no state, the result is {r.toInt}"

def runList (stack target : List StackSlot) (ds : List (Option Nat)) : String :=
  match (Map.State.init stack (Map.plan stack.length target.length ds)).removeSurplus with
  | .ok (blocked, s) => render blocked s.stack s.trace s.mapping.dest
  | .error _ => "err"

-- The line, or none if it is not a case with destinations below `n` that are distinct.
def runLine (list : Bool) (line : String) : Option String := do
  let [tag, stack, target, ds, vars] := line.splitOn ";" | none
  guard (tag = "surplus")
  let stack ← (words stack).mapM slotOf?
  let target ← (words target).mapM slotOf?
  let ds ← (words ds).mapM destOf?
  let vars ← (words vars).mapM String.toNat?
  guard (ds.length = stack.length ∧ stack.length ≤ maxStackSize ∧ target.length ≤ maxStackSize)
  let bound := ds.filterMap id
  guard (bound.all (· < target.length) ∧ bound.eraseDups.length = bound.length)
  return if list then runList stack target ds else runFlat stack target ds vars

partial def loop (list : Bool) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn ((runLine list (line.trimAscii.toString)).getD "bad input")
  loop list stdin stdout

def main (args : List String) : IO Unit := do
  match args with
  | [] => loop false (← IO.getStdin) (← IO.getStdout)
  | ["list"] => loop true (← IO.getStdin) (← IO.getStdout)
  | _ => throw <| IO.userError "usage: surplus_flat [list]"
