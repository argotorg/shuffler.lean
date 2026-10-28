import BbuKraken.Model

/-!
Run `Bbu.buildBottomUp` on the lines of `bbu_harness gen` and print the result
in the format of `bbu_harness run`.
-/

open Bbu

def render : M (List Op) → String
  | .ok ops => " ".intercalate ("ok" :: ops.flatMap fun op =>
      [(["s", "d", "p"][op.kind.toNat]?).getD "?", toString op.arg.toNat])
  | .error (.blocked pos excess) => s!"blocked {pos} {excess}"
  | .error .assertion => "assertion"

def run (m n : Nat) (rest : List Nat) : String :=
  let source := (rest.take m).map (BitVec.ofNat 64)
  let target := (rest.drop m |>.take n).map (BitVec.ofNat 64)
  let dests := rest.drop (m + n) |>.take m
  let spills := (rest.drop (2 * m + n)).drop 1
  let spilled := fun i => if spills.contains i then (1 : UInt8) else 0
  render (buildBottomUp ⟨target, spilled⟩ source dests)

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ").filterMap String.toNat? with
  | m :: n :: rest => stdout.putStrLn (run m n rest)
  | _ => throw <| IO.userError s!"bad line: {line}"
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
