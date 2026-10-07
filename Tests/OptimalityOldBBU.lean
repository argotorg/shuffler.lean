import Shuffler.Optimality.OldBBU.CostBounds
import Shuffler.Optimality.Replay

open Shuffler.Optimality

namespace OptimalityOldBBUTests

private def zero : Value := .Lit 0
private def wide : Value := .Lit (2 ^ 248)

-- Use the production mapping builder and the production BBU call. A failed
-- call keeps its Error value so it cannot appear to have zero operations.
private def run (source target : Stack) : Except Error (List Op) :=
  let mapping := (MappingBuilder.buildMapping source target
    (List.replicate source.length 0) .Leave (by simp)).mapping
  let state : State source target ∅ := {
    planned_mapping := mapping
    stack := source
    trace := .Lit source
    mapping
    pending_generations := target.length - source.length
  }
  (Shuffler.BuildBottomUp.buildBottomUp state).map fun result => flatten result.2

private def swaps (ops : List Op) : Nat :=
  (ops.filter fun op => match op with | .swap _ => true | _ => false).length

#guard run [zero] [zero,zero] = .ok [.dup 1]
#guard run [zero,zero] [zero,zero] = .ok []

-- Final Permute needs three swaps for each of eight disjoint lower pairs.
private def distinct17 : Stack := (List.range 17).map (fun i => .Var ⟨i⟩)
private def paired17 : Stack :=
  (List.range 17).map (fun i => .Var ⟨if i = 16 then i else i ^^^ 1⟩)

#guard (run distinct17 paired17).map swaps = .ok 24

-- This includes the final Permute and refutes the proposed 2k+24 bound.
private def rotated18 : Stack := distinct17.drop 1 ++ [.Lit 99, .Var ⟨0⟩]

#guard (run distinct17 rotated18).map swaps = .ok 31
#guard (run distinct17 rotated18).map List.length = .ok 32

-- The first DUP puts the old wide literal outside DUP reach.
private def wideSource : Stack := [wide] ++ List.replicate 15 zero

#guard run wideSource (wideSource ++ [zero,wide]) = .ok [.dup 1,.push wide]

-- Changed values below SWAP reach cause an explicit error.
private def blockedSource : Stack := [.Var ⟨0⟩] ++ List.replicate 17 zero
private def blockedTarget : Stack := List.replicate 17 zero ++ [.Var ⟨0⟩]

#guard match run blockedSource blockedTarget with
  | .error (.blocked _) => true
  | _ => false

end OptimalityOldBBUTests
