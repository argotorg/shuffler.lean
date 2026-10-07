import Shuffler.Optimality.BirthPlacement.RawWord.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityRawWord

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Lit 0
private def b : Value := .Lit 1
private def x : Value := .Var ⟨42⟩
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push ⟨0, by decide⟩) (fun _ => .push ⟨0, by decide⟩)

private def check (spills : SpillSet) (target births : Stack) : Bool :=
  match RawWord.parse spills target births with
  | none => false
  | some parsed =>
    let built := realize (parsed.plan.cheapest costs .gasOnly)
    decide (SwapRuns.births built.built.trace = births) &&
      ((replay spills [] (flatten built.built.trace)).map (·.target) == some target)

#guard check ∅ [] []
#guard check ∅ [a, b, a, b] [b, a, b, a]
#guard check ∅ [.Wildcard, a] [a, .Wildcard]
#guard check {⟨42⟩} [x, x, a] [a, x, x]
#guard check ∅ ([b] ++ List.replicate 16 a) (List.replicate 16 a ++ [b])
#guard check ∅ (List.replicate 20 a) (List.replicate 20 a)

-- Counts, lengths, deadlines, and birth availability have distinct failures.
#guard (RawWord.parse ∅ [a, b] [a, a]).isNone
#guard (RawWord.parse ∅ [a] [a, a]).isNone
#guard (RawWord.parse ∅ ([b] ++ List.replicate 17 a) (List.replicate 17 a ++ [b])).isNone
#guard (RawWord.parse ∅ [x] [x]).isNone
#guard (RawWord.parse ∅ [] [a]).isNone
#guard (RawWord.parse ∅ [a] []).isNone

private def words (length : Nat) : List Stack :=
  match length with
  | 0 => [[]]
  | length + 1 => (words length).flatMap fun rest => [a :: rest, b :: rest]

-- Every pair of length-four literal words has a trace exactly when its counts agree.
#guard (words 4).all fun target => (words 4).all fun births =>
  check ∅ target births == decide (births.Perm target)

example : RawWord.Feasible spills target births ↔
    ∃ trace : Trace spills [] target, trace.noPop ∧ SwapRuns.births trace = births :=
  RawWord.feasible_iff_trace

end Tests.OptimalityRawWord
