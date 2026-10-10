import Shuffler.BuildBottomUp.Theorems.Feasibility.Defs
import Shuffler.BuildBottomUp.Defs

/-!
Examples where the current BBU fails although a trace exists

Stacks below are written bottom first. `0×n` means n literal zeros. Indices
are zero-based, and the spill set is empty. These are constructed valid
occurrence mappings; no claim is made that the mapping builder selects them.
All four exact problems satisfy Reserve. The checks follow below: BBU blocks,
Reserve holds, and the stated trace reaches the exact target without POP.

1. Fix an existing value before growth.
   Source: [0×16, 1]. Target: [1, 0×16, 1]. Missing: [1].
   Map source i to target i+1, leaving target 0 unbound.
   BBU returns `.blocked 1`: it first uses DUP1 for the unbound target 0.
   Growth puts the bottom zero beyond SWAP reach, so that position cannot
   then become 1. A valid trace is `SWAP16; PUSH 1`. It assigns the existing
   1 to target 0 and the new 1 to the top instead.

2. Move a source into DUP reach before using it.
   Let x be an unspilled variable.
   Source: [x, 0×16]. Target: [0×16, x, x]. Missing: [x].
   Map source 0 to target 16, source 16 to target 0, and each source i to
   target i for 1≤i≤15. Target 17 is unbound.
   BBU returns `.blocked 1`: its initial scan rejects the sole x at depth
   16 before trying a swap. A valid trace is `SWAP16; DUP1`. This trace also
   respects the original occurrence assignments.

3. Avoid moving equal values only to satisfy occurrence assignments.
   Source and target: [0×18]. Missing: [].
   Map source 0 to target 17 and source 17 to target 0; leave other indices
   fixed. BBU returns `.blocked 1` while trying to realize that permutation.
   The bottom occurrence is outside SWAP reach. The empty trace already
   reaches the exact target because every value is zero.

4. Keep an initially reachable source available during growth.
   Source: [0, x, 0×15]. Target: [0, x, 0, x, 0×15]. Missing: [0, x].
   Map source i to target i+2, leaving targets 0 and 1 unbound.
   The sole x starts at depth 15, within DUP reach. BBU fills the earlier
   free hole first, then returns `.blocked 1` after x leaves DUP reach.
   A valid trace is `DUP16; PUSH 0; SWAP1; SWAP15`.
-/

open Shuffler.Placement Shuffler.BuildBottomUp

set_option maxRecDepth 16384

namespace Shuffler.Feasibility.Counterexamples

private instance (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Decidable (Reserve spills source target missing) := by
  unfold Reserve
  infer_instance

private def a : Value := .Var ⟨42⟩
private def zero : Value := .Lit 0
private def one : Value := .Lit 1

private def shiftedMapping (n gap : Nat) : Mapping n (n + gap) where
  toFun i := some ⟨i.val + gap, by have := i.isLt; omega⟩
  invFun j := if h : gap ≤ j.val then some ⟨j.val - gap, by have := j.isLt; omega⟩ else none
  inv i j := by
    have := i.isLt
    have := j.isLt
    split_ifs with h
    · simp only [Option.some.injEq, Fin.ext_iff]
      omega
    · simp only [false_iff, Option.some.injEq, Fin.ext_iff]
      omega

private def prefixBinding : Mapping 17 18 where
  toFun i := some i.castSucc
  invFun j := if h : j.val < 17 then some ⟨j.val, h⟩ else none
  inv i j := by
    have := i.isLt
    have := j.isLt
    split_ifs with h
    · simp only [Option.some.injEq, Fin.ext_iff, Fin.val_castSucc, eq_comm]
    · simp only [false_iff, Option.some.injEq, Fin.ext_iff, Fin.val_castSucc]
      omega

-- 1. Filling the first literal hole before SWAP16 freezes the wrong output.
private def literalSource : Stack := List.replicate 16 zero ++ [one]
private def literalTarget : Stack := [one] ++ List.replicate 16 zero ++ [one]
private def literalState : State literalSource literalTarget ∅ where
  planned_mapping := by simpa [literalSource, literalTarget] using shiftedMapping 17 1
  stack := literalSource
  trace := .Lit literalSource
  mapping := by simpa [literalSource, literalTarget] using shiftedMapping 17 1
  pending_generations := 1

private theorem literalState_valid : literalState.Valid := ⟨by decide, by decide, by decide⟩
example : ∀ i j, literalState.mapping i = some j → literalState.stack[i] = literalTarget[j] := by decide
#guard decide ((buildBottomUp literalState literalState_valid).map (fun result => result.1) =
    .error (.blocked 1))
example : Reserve ∅ literalSource literalTarget {one} := by decide

private def literalSwapped : Trace ∅ literalSource ([one] ++ List.replicate 16 zero) :=
  .Swap 16 (by decide) (by decide) (by decide) (.Lit literalSource)
private def literalTrace : Trace ∅ literalSource literalTarget :=
  .Push one (by decide) literalSwapped
example : literalTrace.noPop := trivial
example : literalTrace.additions = {one} := rfl

-- 2. SWAP16 can recover a nonfree source that the initial DUP scan rejects.
private def seedSource : Stack := [a] ++ List.replicate 16 zero
private def seedTarget : Stack := List.replicate 16 zero ++ [a, a]
private def seedBinding : Mapping 17 18 := prefixBinding.swapDestinations 0 16
private def seedState : State seedSource seedTarget ∅ where
  planned_mapping := by simpa [seedSource, seedTarget] using seedBinding
  stack := seedSource
  trace := .Lit seedSource
  mapping := by simpa [seedSource, seedTarget] using seedBinding
  pending_generations := 1

private theorem seedState_valid : seedState.Valid := ⟨by decide, by decide, by decide⟩
example : ∀ i j, seedState.mapping i = some j → seedState.stack[i] = seedTarget[j] := by decide
#guard decide ((buildBottomUp seedState seedState_valid).map (fun result => result.1) =
    .error (.blocked 1))
example : Reserve ∅ seedSource seedTarget {a} := by decide

private def seedSwapped : Trace ∅ seedSource (List.replicate 16 zero ++ [a]) :=
  .Swap 16 (by decide) (by decide) (by decide) (.Lit seedSource)
private def seedTrace : Trace ∅ seedSource seedTarget :=
  .Dup 1 (by decide) (by decide) (by decide) seedSwapped
example : seedTrace.noPop := trivial
example : seedTrace.additions = {a} := rfl

-- 3. Equal values permit a new occurrence assignment without moving a deep slot.
private def equalSource : Stack := List.replicate 18 zero
private def equalBinding : Mapping 18 18 := (Equiv.swap 0 17).toPEquiv
private def equalState : State equalSource equalSource ∅ where
  planned_mapping := by simpa [equalSource] using equalBinding
  stack := equalSource
  trace := .Lit equalSource
  mapping := by simpa [equalSource] using equalBinding
  pending_generations := 0

private theorem equalState_valid : equalState.Valid := ⟨by decide, by decide, by decide⟩
#guard decide ((buildBottomUp equalState equalState_valid).map (fun result => result.1) =
    .error (.blocked 1))
example : Reserve ∅ equalSource equalSource 0 := by decide

private def equalTrace : Trace ∅ equalSource equalSource := .Lit equalSource
example : equalTrace.noPop := trivial
example : equalTrace.additions = 0 := rfl

-- 4. A source already at depth 15 becomes unreachable after the wrong addition.
private def hiddenSource : Stack := [zero, a] ++ List.replicate 15 zero
private def hiddenTarget : Stack := [zero, a, zero, a] ++ List.replicate 15 zero
private def hiddenState : State hiddenSource hiddenTarget ∅ where
  planned_mapping := by simpa [hiddenSource, hiddenTarget] using shiftedMapping 17 2
  stack := hiddenSource
  trace := .Lit hiddenSource
  mapping := by simpa [hiddenSource, hiddenTarget] using shiftedMapping 17 2
  pending_generations := 2

private theorem hiddenState_valid : hiddenState.Valid := ⟨by decide, by decide, by decide⟩
example : ∀ i j, hiddenState.mapping i = some j → hiddenState.stack[i] = hiddenTarget[j] := by decide
example : Shuffler.Generate.Ready ∅ hiddenSource [zero, a] := by decide
#guard decide ((buildBottomUp hiddenState hiddenState_valid).map (fun result => result.1) =
    .error (.blocked 1))
example : Reserve ∅ hiddenSource hiddenTarget ({zero} + {a}) := by decide

private def hiddenDuped : Trace ∅ hiddenSource (hiddenSource ++ [a]) :=
  .Dup 16 (by decide) (by decide) (by decide) (.Lit hiddenSource)
private def hiddenPushed : Trace ∅ hiddenSource (hiddenSource ++ [a, zero]) :=
  .Push zero (by decide) hiddenDuped
private def hiddenRaised : Trace ∅ hiddenSource (hiddenSource ++ [zero, a]) :=
  .Swap 1 (by decide) (by decide) (by decide) hiddenPushed
private def hiddenTrace : Trace ∅ hiddenSource hiddenTarget :=
  .Swap 15 (by decide) (by decide) (by decide) hiddenRaised
example : hiddenTrace.noPop := trivial
example : hiddenTrace.additions = {a, zero} := rfl

end Shuffler.Feasibility.Counterexamples
