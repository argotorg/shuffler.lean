import PermuteKraken.Model

/-! Read lines "n p0 .. p(n-1)" and print the result of the model for each,
as "ok d1 .. dk" or "blocked offset excess". -/

open PermuteKraken
def Perm.ofList? (l : List Nat) : Option Perm :=
  if h : (∀ i : Fin l.length, l[i] < l.length) ∧ ∀ i j : Fin l.length, l[i] = l[j] → i = j
  then some ⟨l, fun i hi => h.1 ⟨i, hi⟩,
    fun i j hi hj he => congrArg Fin.val (h.2 ⟨i, hi⟩ ⟨j, hj⟩ he)⟩
  else none


def render : Except Blocked (List Nat) → String
  | .ok ds => " ".intercalate ("ok" :: ds.map toString)
  | .error b => s!"blocked {b.offset} {b.excess}"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let nums := (line.trimAscii.toString.splitOn " ").filterMap String.toNat?
  match nums with
  | [] => throw <| IO.userError s!"bad line: {line}"
  | _ :: l =>
    match Perm.ofList? l with
    | none => throw <| IO.userError s!"not a permutation: {line}"
    | some p => stdout.putStrLn (render (permute p))
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
