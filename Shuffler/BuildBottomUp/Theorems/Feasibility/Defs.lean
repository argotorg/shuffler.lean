import Shuffler.Trace

/-!
Definitions for the feasibility statements in `Theorems.lean`. The instruction
model and the trace restrictions are in `Shuffler/Trace.lean`. `StackMatches`
is in `Shuffler/Stack.lean`. `MAX_DUP_DEPTH = 15` and `MAX_SWAP_DEPTH = 16`
are zero-based depths from `Shuffler/Basic.lean`.
-/

namespace Shuffler.Placement

def Free (spills : SpillSet) (value : Value) : Prop :=
  value.can_be_freely_generated ∨ spills.is_spilled value

instance (spills : SpillSet) (value : Value) : Decidable (Free spills value) := by
  unfold Free
  infer_instance

-- One copy of each distinct missing value that needs an existing source.
def seeds (spills : SpillSet) (missing : Multiset Value) : Multiset Value :=
  (missing.toFinset.filter fun value => ¬Free spills value).val

def frozen (source : Stack) : Nat := source.length - (MAX_SWAP_DEPTH + 1)

def window (source : Stack) : Stack := source.drop (frozen source)

def boundary (source target : Stack) (missing : Multiset Value) : Multiset Value :=
  if missing ≠ 0 ∧ MAX_SWAP_DEPTH + 1 ≤ source.length then
    ((target[frozen source]?).toList : Multiset Value)
  else 0

-- Exact counts, an unchanged frozen prefix, and enough separate occurrences
-- for the next fixed output and all required sources. All data are initial.
-- If the boundary value also occurs in seeds, their sum requires two copies:
-- one for that output position and another to supply later DUP operations.
def Reserve (spills : SpillSet) (source target : Stack) (missing : Multiset Value) : Prop :=
  (target : Multiset Value) = (source : Multiset Value) + missing ∧
    target.take (frozen source) = source.take (frozen source) ∧
    boundary source target missing + seeds spills missing ≤ (window source : Multiset Value)

-- The witness is a production trace with exactly the requested additions.
def CanPlace (spills : SpillSet) (source target : Stack) (missing : Multiset Value) : Prop :=
  ∃ trace : Trace spills source target, trace.noPop ∧ trace.additions = missing

-- Counts determine the additions when POP is forbidden. Reserve also checks
-- that target counts include all source counts; subtraction alone does not.
def NoPopNeeded (spills : SpillSet) (source target : Stack) : Prop :=
  Reserve spills source target ((target : Multiset Value) - (source : Multiset Value))

end Shuffler.Placement

namespace Shuffler.Generate

def Available (spills : SpillSet) (source : Stack) (value : Value) : Prop :=
  value.can_be_freely_generated ∨ spills.is_spilled value ∨
    ∃ pos : Fin source.length, source[pos] = value ∧ source.isDupReachable pos

instance (spills : SpillSet) (source : Stack) (value : Value) :
    Decidable (Available spills source value) := by
  unfold Available
  infer_instance

def Ready (spills : SpillSet) (source missing : Stack) : Prop :=
  ∀ value ∈ missing, Available spills source value

instance (spills : SpillSet) (source missing : Stack) : Decidable (Ready spills source missing) := by
  unfold Ready
  infer_instance

-- Each requested value is added once. The order of additions is free.
def CanGenerate (spills : SpillSet) (source missing : Stack) : Prop :=
  ∃ added, added.Perm missing ∧
    ∃ trace : Trace spills source (source ++ added), trace.onlyGenerates

end Shuffler.Generate

namespace Shuffler.Generate.WithSwaps

open Shuffler.Placement

-- Final order is unrestricted. The trace adds exactly missing and has no POP.
def CanGenerate (spills : SpillSet) (source : Stack) (missing : Multiset Value) : Prop :=
  ∃ target, CanPlace spills source target missing

-- Required kinds have initial top-17 sources and need at most 16 slots.
def Ready (spills : SpillSet) (source : Stack) (missing : Multiset Value) : Prop :=
  seeds spills missing ≤ (window source : Multiset Value) ∧
    (seeds spills missing).card ≤ MAX_DUP_DEPTH + 1

instance (spills : SpillSet) (source : Stack) (missing : Multiset Value) :
    Decidable (Ready spills source missing) := by
  unfold Ready
  infer_instance

end Shuffler.Generate.WithSwaps
