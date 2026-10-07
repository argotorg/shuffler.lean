import Shuffler.Optimality.PrefixIntroduction.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityPrefixIntroduction

open Shuffler.Optimality

set_option maxRecDepth 8192

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩, ⟨43⟩}
private def initial : Stack := List.replicate 16 zero
private def targetRun (n : Nat) : Stack := List.replicate n a ++ initial
private def required (n : Nat) := PrefixIntroduction.requiredDirect a initial (targetRun n)
private def runBuilt := (replayExact spills initial (targetRun 3) (Multiset.replicate 3 a)
  [.load ⟨42⟩, .swap 16, .load ⟨42⟩, .swap 16, .load ⟨42⟩, .swap 16]).get (by decide)
private def shortBuilt := (replayExact spills (List.replicate 15 zero)
  ([a, a] ++ List.replicate 15 zero) {a, a}
  [.load ⟨42⟩, .dup 1, .swap 16, .swap 1, .swap 15]).get (by decide)

#guard required 0 = 0
#guard required 1 = 1
#guard required 2 = 2
#guard required 3 = 3
#guard required 8 = 8
#guard required 17 = 17
#guard required 33 = 33
#guard Lineage.directCount a runBuilt.trace = 3
#guard PrefixIntroduction.requiredDirect a initial (a :: initial ++ [a]) = 2
#guard PrefixIntroduction.requiredDirect a initial (List.replicate 8 a ++ initial ++ [a]) = 9

-- The count includes one independent seed for each remaining demanded kind.
#guard PrefixIntroduction.requiredDirect a initial ([a, b, a] ++ initial ++ [a, b]) = 3
#guard PrefixIntroduction.requiredDirect b initial ([a, b, a] ++ initial ++ [a, b]) = 2
#guard PrefixIntroduction.requiredDirect a (a :: initial) ([a, a] ++ initial ++ [a]) = 2
#guard PrefixIntroduction.requiredDirect a ([a, a] ++ initial) ([a, a, a] ++ initial) = 1
#guard PrefixIntroduction.requiredDirect a (a :: List.replicate 17 zero)
  (a :: List.replicate 17 zero ++ [a]) = 1

-- Fifteen protected copies leave room for a DUP before the prefix freezes.
#guard PrefixIntroduction.requiredDirect a (List.replicate 15 zero)
  ([a, a] ++ List.replicate 15 zero) = 0
#guard Lineage.directCount a shortBuilt.trace = 1
#guard PrefixIntroduction.requiredDirect a (List.replicate 33 a) (List.replicate 34 a) = 0
#guard PrefixIntroduction.requiredDirect a [] [a, a] = 0
#guard PrefixIntroduction.requiredDirect a initial initial = 0

example (trace : Trace spills initial (targetRun 3)) (hpop : trace.noPop) :
    3 ≤ Lineage.directCount a trace := by
  have h := PrefixIntroduction.requiredDirect_le_directCount a trace hpop
  have he : PrefixIntroduction.requiredDirect a initial (targetRun 3) = 3 := by decide
  rwa [he] at h

example (old : Stack) (value : Value) (trace : Trace spills source target) (hpop : trace.noPop)
    (hlarge : 16 ≤ PrefixIntroduction.oldCount old source) (hnot : value ∉ old)
    (hbound : PrefixIntroduction.oldCount old (target.take cut) ≤
      PrefixIntroduction.oldCount old source - 16) :
    PrefixIntroduction.prefixDemand value target cut ≤ source.count value + Lineage.directCount value trace :=
  PrefixIntroduction.prefixDemand_le_count_add_directCount old value trace hpop hlarge hnot hbound

end Tests.OptimalityPrefixIntroduction
