import Shuffler.Trace
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.List.Forall2

/-!
Review the trace restrictions, then the finite conditions, then the four
statements at the end of this file. The instruction model is in
`Shuffler/Trace.lean`; `MAX_DUP_DEPTH = 15` and `MAX_SWAP_DEPTH = 16` are
zero-based depths from `Shuffler/Basic.lean`.

All four statements ask whether some trace exists in the current `Trace`
model. All exclude POP. They do not claim that BBU will find that trace for
its supplied mapping and choices.

`ExactPlacement` is the central result: it fixes the concrete target and the
exact additions. `WildcardPlacement` applies it to a chosen result matching
a pattern, and also chooses the additions. `GenerationWithSwaps` keeps the
exact additions but allows any final order. `AppendOnlyGeneration` restricts
the operations further: it forbids SWAP and keeps the original source prefix.

The statements are propositions, not assumptions. Their proofs are in the
modules named beside them. Import `Shuffler.Feasibility.Theorems` to load all
four proofs. Keeping the proofs downstream avoids circular imports.
-/

-- The trace adds values without changing or removing existing positions.
def Trace.onlyGenerates : Trace spills source result → Prop
  | .Lit _ => True
  | .Swap _ _ _ _ _ => False
  | .Dup _ _ _ _ trace => trace.onlyGenerates
  | .Pop _ _ => False
  | .Push _ _ trace => trace.onlyGenerates
  | .Load _ _ trace => trace.onlyGenerates

def Trace.noPop : Trace spills source result → Prop
  | .Lit _ => True
  | .Swap _ _ _ _ trace => trace.noPop
  | .Dup _ _ _ _ trace => trace.noPop
  | .Pop _ _ => False
  | .Push _ _ trace => trace.noPop
  | .Load _ _ trace => trace.noPop

-- Record the values actually added by DUP, PUSH, and LOAD.
def Trace.additions : Trace spills source result → Multiset Value
  | .Lit _ => 0
  | .Swap _ _ _ _ trace => trace.additions
  | @Dup _ _ prev idx hlen hlo _ trace =>
      trace.additions + {prev[prev.length - idx]'(by omega)}
  | .Pop _ trace => trace.additions
  | .Push value _ trace => trace.additions + {value}
  | .Load id _ trace => trace.additions + {.Var id}

-- A wildcard in the target accepts any source value.
def SlotMatches (actual target : Value) : Prop :=
  target.is_junk ∨ actual = target

instance (actual target : Value) : Decidable (SlotMatches actual target) := by
  unfold SlotMatches
  infer_instance

def StackMatches (actual target : Stack) : Prop :=
  List.Forall₂ SlotMatches actual target

instance (actual target : Stack) : Decidable (StackMatches actual target) := by
  unfold StackMatches
  infer_instance

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

namespace Shuffler.Feasibility

/-- The central equivalence: Reserve holds exactly when a production trace
reaches this fixed concrete target with exactly the fixed missing multiset.
The trace may use SWAP, DUP, PUSH, and LOAD, but no POP or extra additions.

Proved by Placement.canPlace_iff_reserve in Shuffler/Placement/Theorems.lean. -/
abbrev ExactPlacement (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) : Prop :=
  Placement.CanPlace spills source target missing ↔ Placement.Reserve spills source target missing

/-- Apply exact placement to some concrete result E that matches the pattern.
A wildcard accepts any value; other positions must equal the pattern value.
Both E and its exact additions H are chosen by the existential quantifiers.

Proved by Placement.exists_matching_trace_iff_reserve in
Shuffler/Placement/Compatibility.lean. -/
abbrev WildcardPlacement (spills : SpillSet) (source pattern : Stack) : Prop :=
  (∃ result : Stack, ∃ trace : Trace spills source result,
    trace.noPop ∧ StackMatches result pattern) ↔
  ∃ result : Stack, ∃ missing : Multiset Value,
    StackMatches result pattern ∧ Placement.Reserve spills source result missing

/-- Permit only DUP, PUSH, and LOAD. The original source remains a prefix,
followed by exactly the missing values in any order. Each requested value
must initially be within DUP reach, or be available through PUSH or LOAD.
General placement permits SWAP, so it does not guarantee success under this
stricter operation constraint.

Proved by Generate.canGenerate_iff_ready in Shuffler/Generate/Theorems.lean. -/
abbrev AppendOnlyGeneration (spills : SpillSet) (source missing : Stack) : Prop :=
  Generate.CanGenerate spills source missing ↔ Generate.Ready spills source missing

/-- A consequence of exact placement with no required final order. SWAP,
DUP, PUSH, and LOAD may add exactly the missing multiset. Each distinct
needed nonfree kind must occur in the initial top 17 slots, and there must
be at most 16 such kinds. Repeated demand for one kind needs only one seed.

Proved by Generate.WithSwaps.canGenerate_iff_ready in
Shuffler/Generate/WithSwaps.lean. -/
abbrev GenerationWithSwaps (spills : SpillSet) (source : Stack) (missing : Multiset Value) : Prop :=
  Generate.WithSwaps.CanGenerate spills source missing ↔ Generate.WithSwaps.Ready spills source missing

end Shuffler.Feasibility
