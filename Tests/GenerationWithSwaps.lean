import Shuffler.Feasibility.Theorems

open Shuffler.Generate.WithSwaps

namespace GenerationWithSwapsTests

private def a : Value := .Var ⟨42⟩
private def kinds (n : Nat) : Stack := (List.range n).map (fun i => .Var ⟨i⟩)

-- Empty demand needs no operation, even when the source is empty.
example : CanGenerate ∅ [] 0 :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

-- Free values and spills need no initial source.
example : CanGenerate ∅ [] ([Value.Lit 0, Value.Wildcard, Value.Lit 7] : Multiset Value) :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)
example : CanGenerate {⟨42⟩} [] {a, a} :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)
example : ¬CanGenerate ∅ [] {a} := by
  rw [canGenerate_iff_ready]
  decide

-- SWAP16 reaches one slot beyond DUP16.
private def atDepth16 : Stack := [a] ++ List.replicate 16 (.Lit 0)
private def moved : Stack := List.replicate 16 (.Lit 0) ++ [a]
private def copied : Stack := List.replicate 16 (.Lit 0) ++ [a, a]

example : ¬Shuffler.Generate.Ready ∅ atDepth16 [a] := by decide
example : Ready ∅ atDepth16 {a} := by decide
example : CanGenerate ∅ atDepth16 {a} :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

private def moveSeed : Trace ∅ atDepth16 moved :=
  .Swap 16 (by decide) (by decide) (by decide) (.Lit atDepth16)

private def copySeed : Trace ∅ atDepth16 copied :=
  .Dup 1 (by decide) (by decide) (by decide) moveSeed

-- This witness executes the production SWAP16 and DUP1 constructors.
example : CanGenerate ∅ atDepth16 {a} :=
  ⟨copied, copySeed, True.intro, rfl⟩

-- A sole source at depth 17 is outside both regions.
private def atDepth17 : Stack := [a] ++ List.replicate 17 (.Lit 0)

example : ¬CanGenerate ∅ atDepth17 {a} := by
  rw [canGenerate_iff_ready]
  decide

-- Sixteen distinct needed kinds fit; the seventeenth source is expendable.
example : Ready ∅ (kinds 17) (kinds 16 : Multiset Value) := by decide
example : CanGenerate ∅ (kinds 17) (kinds 16 : Multiset Value) :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

-- All seventeen kinds are present, but they exceed the retained-source limit.
example : Shuffler.Placement.seeds ∅ (kinds 17 : Multiset Value) ≤
    (Shuffler.Placement.window (kinds 17) : Multiset Value) := by decide
example : ¬CanGenerate ∅ (kinds 17) (kinds 17 : Multiset Value) := by
  rw [canGenerate_iff_ready]
  decide

-- Spilling one kind removes its seed requirement and restores capacity.
example : CanGenerate {⟨16⟩} (kinds 17) (kinds 17 : Multiset Value) :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

-- Repeated requests need one retained source, not one source per request.
example : CanGenerate ∅ atDepth16 (List.replicate 40 a : Multiset Value) :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

end GenerationWithSwapsTests
