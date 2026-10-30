import Shuffler.Permute.Defs

/-!
Run the original `Shuffler.Permute.permute` on lines "n p0 .. p(n-1)" and print
the swap depths as "ok d1 .. dk" or "blocked offset excess". The values of the
stack are distinct, so the regroup and the retag of `permute` do nothing. The root project, not
`PermuteKraken`, builds it as `original`:

  lake exe original < perms.txt
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

def render {source target : Stack} {spills : SpillSet} :
    Except ShuffleErr (Emission.Result source target spills) → String
  | .ok ⟨none, state⟩ => " ".intercalate ("ok" :: (swaps state.trace).map toString)
  | .ok ⟨some b, _⟩ => s!"blocked {b.offset} {b.excess}"
  | .error (.Blocked b) => s!"blocked {b.offset} {b.excess}"
  | .error (.assertion r) => s!"assertion {r}"

-- The state of `permute`: the stack `source` with an empty mapping. `permute`
-- reads the mapping only to update it.
def initial (source : Stack) : Emission.State source source ∅ :=
  { planned_mapping := ⊥, stack := source, trace := .Lit source, mapping := ⊥,
    pending_generations := 0 }

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ").filterMap String.toNat? with
  | n :: l =>
    let source : Stack := (List.range n).map (fun i => .Var ⟨i⟩)
    match ofList? source.length l with
    | some perm => stdout.putStrLn (render (permute (initial source) perm))
    | none => throw <| IO.userError s!"not a permutation: {line}"
  | [] => throw <| IO.userError s!"bad line: {line}"
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
