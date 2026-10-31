import Fuzz.Oracle

/-!
Run each case line of stdin on the PR31 model through `runLine` of `Fuzz/Oracle.lean` and print the
result, one line for each. `test/lowest_diff.sh` runs it on the "lowest" cases
(`Fuzz/lowest_cases.sh`). The root project builds it as `lowest_pr31`:

  lake exe lowest_pr31 < cases.txt
-/

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (runLine (line.trimAscii.toString))
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
