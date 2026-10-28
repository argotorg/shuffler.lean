import Shuffler.Permute.Defs

/-!
Run the original `Shuffler.Permute.permute` on lines "n p0 .. p(n-1)" and print
the swap depths as "ok d1 .. dk" or "blocked offset excess". This file belongs to
the root project, not to `PermuteKraken`:

  lake env lean --run kraken/test/OriginalMain.lean < perms.txt
-/

open Shuffler Shuffler.Permute

def swaps {spills : SpillSet} {s r : Stack} : Trace spills s r → List Nat
  | .Lit _ => []
  | .Swap idx _ _ _ t => swaps t ++ [idx]
  | _ => [999]  -- `permute` makes only swaps

def ofList? (n : Nat) (l : List Nat) : Option (Equiv.Perm (Fin n)) :=
  if hl : l.length = n then
    if hlt : ∀ i : Fin n, l[i.val]'(by omega) < n then
      let f : Fin n → Fin n := fun i => ⟨l[i.val]'(by omega), hlt i⟩
      let g : Fin n → Fin n := fun j => ((List.finRange n).find? (f · = j)).getD j
      if h : (∀ i, g (f i) = i) ∧ ∀ j, f (g j) = j then some ⟨f, g, h.1, h.2⟩ else none
    else none
  else none

def render {spills : SpillSet} {source : Stack} :
    Except ShuffleErr ((result : Stack) × Trace spills source result) → String
  | .ok ⟨_, t⟩ => " ".intercalate ("ok" :: (swaps t).map toString)
  | .error (.Blocked b) => s!"blocked {b.offset} {b.excess}"
  | .error (.assertion r) => s!"assertion {r}"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ").filterMap String.toNat? with
  | n :: l =>
    let source : Stack := (List.range n).map (fun i => .Var ⟨i⟩)
    match ofList? source.length l with
    | some perm => stdout.putStrLn (render (permute ∅ source perm))
    | none => throw <| IO.userError s!"not a permutation: {line}"
  | [] => throw <| IO.userError s!"bad line: {line}"
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
