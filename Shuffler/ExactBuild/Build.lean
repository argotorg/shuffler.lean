import Shuffler.ExactBuild.Prepare
import Shuffler.BuildBottomUp.Theorems.Feasibility.Theorems

namespace Shuffler.ExactBuild

open Shuffler.Placement

-- Fix value with step, then follow it with next on the rest of the target.
def PlacementStep.andThen (step : PlacementStep spills fixed working value added)
    (next : BuiltTrace spills ((fixed ++ [value]) ++ step.remaining)
      ((fixed ++ [value]) ++ tail) rest)
    (hmissing : added + rest = missing) :
    BuiltTrace spills (fixed ++ working) (fixed ++ value :: tail) missing :=
  (step.built.trans next).cast rfl (by simp only [List.append_assoc, List.singleton_append])
    hmissing

theorem Working.nil (h : Working spills working [] missing) : working = [] ∧ missing = 0 := by
  have hc := congrArg Multiset.card h.balance
  simp only [Multiset.coe_nil, Multiset.card_zero, Multiset.card_add, Multiset.coe_card] at hc
  exact ⟨List.length_eq_zero_iff.mp (by omega), Multiset.card_eq_zero.mp (by omega)⟩

theorem Working.room (h : Working spills working target missing) (hv : value ∈ missing) :
    working.length ≤ MAX_DUP_DEPTH + 1 :=
  h.space fun he => by simp [he] at hv

theorem Working.available (h : Working spills working target missing) (hv : value ∈ missing) :
    Free spills value ∨ value ∈ working := by
  by_cases hf : Free spills value
  · exact Or.inl hf
  · exact Or.inr ((seeds_le_iff _ _ _).mp h.seeds value hv hf)

theorem Working.generate (h : Working spills working (value :: tail) missing)
    (hv : value ∈ missing) (step : PlacementStep spills fixed working value {value}) :
    Working spills step.remaining tail (missing.erase value) := by
  have hremaining : (step.remaining : Multiset Value) = (working : Multiset Value) := by
    apply add_left_cancel (a := ({value} : Multiset Value))
    exact step.balance.trans (add_comm _ _)
  have hlen : step.remaining.length = working.length := by
    simpa only [Multiset.coe_card] using congrArg Multiset.card hremaining
  refine ⟨hlen ▸ h.small, fun _ => hlen ▸ h.room hv, ?_, ?_⟩
  · rw [hremaining]
    exact balance_erase_missing h.balance hv
  · rw [hremaining]
    exact (seeds_mono (Multiset.erase_le _ _)).trans h.seeds

theorem Working.source (h : Working spills working (value :: tail) missing)
    (hv : value ∉ missing) : value ∈ working :=
  (balance_erase_source h.balance hv).1

theorem Working.place (h : Working spills working (value :: tail) missing)
    (hv : value ∉ missing) (step : PlacementStep spills fixed working value 0) :
    Working spills step.remaining tail missing := by
  have hremaining : {value} + (step.remaining : Multiset Value) =
      (working : Multiset Value) := by simpa only [add_zero] using step.balance
  have hlen : step.remaining.length + 1 = working.length := by
    simpa only [Multiset.card_add, Multiset.card_singleton, Multiset.coe_card,
      Nat.add_comm] using congrArg Multiset.card hremaining
  have hsmall := h.small
  refine ⟨by omega, fun _ => by unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *; omega, ?_, ?_⟩
  · apply add_left_cancel (a := ({value} : Multiset Value))
    calc
      {value} + (tail : Multiset Value) = (working : Multiset Value) + missing := by
        simpa only [Multiset.singleton_add, Multiset.cons_coe] using h.balance
      _ = {value} + ((step.remaining : Multiset Value) + missing) := by
        rw [← hremaining, add_assoc]
  · have hvseed : value ∉ Placement.seeds spills missing := fun hm => hv ((mem_seeds _ _ _).mp hm).1
    have hseeds := h.seeds
    rw [← hremaining] at hseeds
    exact (Multiset.le_cons_of_notMem hvseed).mp hseeds

-- Each recursive call fixes one target value. With growth, every retained
-- source stays in a working suffix of at most sixteen slots.
def buildWorking (spills : SpillSet) (fixed working : Stack) :
    (target : Stack) → (missing : Multiset Value) → Working spills working target missing →
      BuiltTrace spills (fixed ++ working) (fixed ++ target) missing
  | [], _, h => (BuiltTrace.lit spills _).cast rfl (by rw [h.nil.1]) h.nil.2.symm
  | value :: tail, missing, h =>
    if hv : value ∈ missing then
      let step := generateAndPlace spills fixed working value (h.room hv) (h.available hv)
      step.andThen
        (buildWorking spills (fixed ++ [value]) step.remaining tail (missing.erase value)
          (h.generate hv step))
        ((Multiset.singleton_add _ _).trans (Multiset.cons_erase hv))
    else
      let step := placeExisting spills fixed working value h.small (h.source hv)
      step.andThen
        (buildWorking spills (fixed ++ [value]) step.remaining tail missing (h.place hv step))
        (zero_add _)

-- This constructor returns data in Type. It executes finite searches and
-- instruction constructors; it does not extract a trace from an existence proof.
/-
Informal complexity estimates for this constructor and the checked `build`:
EVM reach is fixed at 16. Let n include source, target, missing, and spill input
sizes, and assume O(1) value comparisons. `prepare` runs once. Each
`buildWorking` step consumes one target slot, searches at most 17 working
values, and emits at most two operations.

An implementation with arrays, dense value ids, count tables, and an operation
buffer takes O(n) time and O(n) space, including output. Comparison maps give
O(n log n) time and O(n) space. The current linked-list checked `build` takes
O(n²) time and can use O(n²) space: it scans and erases lists, copies growing
prefixes, concatenates recursive traces, and retains intermediate stack lists.

The `BuildBottomUp.buildComplete` wrapper also constructs `expectedStack`.
Its linear estimate assumes O(1) mapping queries. The arbitrary `PEquiv`
functions in a State have no evaluation-time bound from their type.
-/
def buildOfReserve (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (h : Reserve spills source target missing) : BuiltTrace spills source target missing :=
  let prepared := prepare spills source target missing h
  let rest := buildWorking spills prepared.fixed prepared.working prepared.tail missing
    prepared.valid
  (prepared.built.trans rest).cast rfl prepared.target_eq.symm (zero_add _)

instance (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Decidable (Reserve spills source target missing) := by
  unfold Reserve
  infer_instance

def build (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Option (BuiltTrace spills source target missing) :=
  if h : Reserve spills source target missing then some (buildOfReserve spills source target missing h)
  else none

theorem build_succeeds_iff_reserve (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) :
    (build spills source target missing).isSome ↔ Reserve spills source target missing := by
  simp only [build]
  split <;> simp_all

-- build returns a trace whenever a trace without POP and with these additions exists.
theorem build_succeeds_iff_canPlace (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) :
    (build spills source target missing).isSome ↔ CanPlace spills source target missing :=
  (build_succeeds_iff_reserve spills source target missing).trans
    (canPlace_iff_reserve spills source target missing).symm

theorem build_sound {result : BuiltTrace spills source target missing}
    (_h : build spills source target missing = some result) :
    result.trace.noPop ∧ result.trace.additions = missing :=
  ⟨result.noPop, result.additions⟩

end Shuffler.ExactBuild
