import Shuffler.BuildBottomUp.Lemmas.Placement.Necessity
import Shuffler.BuildBottomUp.Lemmas.Placement.Sufficiency
import Shuffler.BuildBottomUp.Lemmas.Generate.Necessity
import Shuffler.BuildBottomUp.Lemmas.Generate.Sufficiency
import Shuffler.BuildBottomUp.Lemmas.Generate.WithSwaps
import Shuffler.Stack

/-!
The definitions are in `Defs.lean`.

All five statements ask whether some trace exists in the current `Trace`
model. All exclude POP. They do not claim that BBU will find that trace for
its supplied mapping and choices. `Counterexamples.lean` has problems where
BBU fails although a trace exists.

`canPlace_iff_reserve` is the central result: it fixes the concrete target
and the exact additions. `exists_matching_trace_iff_reserve` applies it to a
chosen result matching a pattern, and also chooses the additions.
`WithSwaps.canGenerate_iff_ready` keeps the exact additions but allows any
final order. `Generate.canGenerate_iff_ready` restricts the operations
further: it forbids SWAP and keeps the original source prefix.
`noPopNeeded_iff_exists_trace` is a corollary of the central result.
-/

namespace Shuffler.Placement

/-- The central equivalence: Reserve holds exactly when a production trace
reaches this fixed concrete target with exactly the fixed missing multiset.
The trace may use SWAP, DUP, PUSH, and LOAD, but no POP or extra additions. -/
theorem canPlace_iff_reserve (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) :
    CanPlace spills source target missing ↔ Reserve spills source target missing :=
  ⟨CanPlace.reserve, Reserve.canPlace⟩

/-- Apply exact placement to some concrete result E that matches the pattern.
A wildcard accepts any value; other positions must equal the pattern value.
Both E and its exact additions H are chosen by the existential quantifiers. -/
theorem exists_matching_trace_iff_reserve (spills : SpillSet) (source pattern : Stack) :
    (∃ result : Stack, ∃ trace : Trace spills source result,
      trace.noPop ∧ StackMatches result pattern) ↔
    ∃ result : Stack, ∃ missing : Multiset Value,
      StackMatches result pattern ∧ Reserve spills source result missing := by
  constructor
  · rintro ⟨result, trace, hnoPop, hmatches⟩
    exact ⟨result, trace.additions, hmatches, CanPlace.reserve ⟨trace, hnoPop, rfl⟩⟩
  · rintro ⟨result, missing, hmatches, hreserve⟩
    obtain ⟨trace, hnoPop, _⟩ := hreserve.canPlace
    exact ⟨result, trace, hnoPop, hmatches⟩

/-- An exact test for whether this concrete target has a trace without POP.
The additions are the target counts minus the source counts. This does not
assert that allowing POP leaves all feasible problems unchanged. -/
theorem noPopNeeded_iff_exists_trace (spills : SpillSet) (source target : Stack) :
    NoPopNeeded spills source target ↔ ∃ trace : Trace spills source target, trace.noPop := by
  constructor
  · intro h
    obtain ⟨trace, hnoPop, _⟩ := h.canPlace
    exact ⟨trace, hnoPop⟩
  · rintro ⟨trace, hnoPop⟩
    have hmissing : (target : Multiset Value) - (source : Multiset Value) =
        trace.additions := by
      rw [trace.noPop_balance hnoPop,
        add_comm (source : Multiset Value) trace.additions,
        Multiset.add_sub_cancel_right]
    exact CanPlace.reserve ⟨trace, hnoPop, hmissing.symm⟩

end Shuffler.Placement

namespace Shuffler.Generate

/-- Permit only DUP, PUSH, and LOAD. The original source remains a prefix,
followed by exactly the missing values in any order. Each requested value
must initially be within DUP reach, or be available through PUSH or LOAD.
General placement permits SWAP, so it does not guarantee success under this
stricter operation constraint. -/
theorem canGenerate_iff_ready (spills : SpillSet) (source missing : Stack) :
    CanGenerate spills source missing ↔ Ready spills source missing :=
  ⟨CanGenerate.ready, Ready.canGenerate⟩

end Shuffler.Generate

namespace Shuffler.Generate.WithSwaps

/-- A consequence of exact placement with no required final order. SWAP,
DUP, PUSH, and LOAD may add exactly the missing multiset. Each distinct
needed nonfree kind must occur in the initial top 17 slots, and there must
be at most 16 such kinds. Repeated demand for one kind needs only one seed. -/
theorem canGenerate_iff_ready (spills : SpillSet) (source : Stack) (missing : Multiset Value) :
    CanGenerate spills source missing ↔ Ready spills source missing :=
  ⟨CanGenerate.ready, Ready.canGenerate⟩

end Shuffler.Generate.WithSwaps
