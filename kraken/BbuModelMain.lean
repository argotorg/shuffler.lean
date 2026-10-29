import BbuKraken.Model

/-!
Run `Bbu.buildBottomUp` on the lines of `bbu_harness gen` and print the result
in the format of `bbu_harness run`. As `bbu_harness run`, check that the final
stack is the source after the operations.
-/

open Bbu

-- `slot_of` of `bbu_harness.c`, without the padding.
def slotOf (v : Nat) : StackSlot :=
  ⟨.ofNat 32 (if v < 2 then 0 else (v - 2) / 2),
    if v = 0 then Junk else if v = 1 then FunctionReturnLabel else Value,
    if v < 2 then Unreachable else if v % 2 = 1 then Const else 1⟩

-- `code_of` of `bbu_harness.c`
def codeOf (s : StackSlot) : Nat :=
  if s.kind = Junk then 0
  else if s.kind = FunctionReturnLabel then 1
  else 2 + 2 * s.payload.toNat + (if s.valueOpcode = Const then 1 else 0)

-- `replay` of `bbu_harness.c`: the stack after `op`, or none if `op` does not apply.
def apply (stack : List StackSlot) (op : Op) : Option (List StackSlot) :=
  let d := op.depth.toNat
  let top := stack.length - 1
  if op.kind = Swap then
    if 1 ≤ d ∧ d < stack.length then
      some ((stack.set (top - d) stack[top]!).set top stack[top - d]!)
    else none
  else if op.kind = Dup then
    if 1 ≤ d ∧ d ≤ stack.length then some (stack ++ [stack[stack.length - d]!]) else none
  else some (stack ++ [op.slot])

def render (source : List StackSlot) : M St → String
  | .ok st =>
    if st.trace.foldlM apply source = some (st.slots.map Slot.val) then
      " ".intercalate ("ok" :: st.trace.flatMap fun op =>
        if op.kind = Swap then ["s", toString op.depth.toNat]
        else if op.kind = Dup then ["d", toString op.depth.toNat]
        else ["p", toString (codeOf op.slot)])
    else "invalid: the final stack is not the source after the operations"
  | .error (.blocked pos excess) => s!"blocked {pos} {excess}"
  | .error .assertion => "assertion"

def run (m n : Nat) (rest : List Nat) : String :=
  let source := (rest.take m).map slotOf
  let target := (rest.drop m |>.take n).map slotOf
  let dests := rest.drop (m + n) |>.take m
  let spills := (rest.drop (2 * m + n)).drop 1
  let spilled := fun i => if spills.contains i then (1 : UInt8) else 0
  render source (buildBottomUp ⟨target, spilled⟩ source dests)

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ").filterMap String.toNat? with
  | m :: n :: rest => stdout.putStrLn (run m n rest)
  | _ => throw <| IO.userError s!"bad line: {line}"
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
