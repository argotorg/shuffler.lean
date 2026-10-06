import Shuffler.Placement.BuildPrepare

namespace Shuffler.Placement

structure BuiltTrace (spills : SpillSet) (source target : Stack) (missing : Multiset Value) where
  trace : Trace spills source target
  noPop : trace.noPop
  additions : trace.additions = missing

def BuiltTrace.cast {otherSource otherTarget : Stack} {otherMissing : Multiset Value}
    (result : BuiltTrace spills source target missing)
    (hs : source = otherSource) (ht : target = otherTarget) (hm : missing = otherMissing) :
    BuiltTrace spills otherSource otherTarget otherMissing := by
  subst otherSource otherTarget otherMissing
  exact result

def BuiltTrace.trans (first : BuiltTrace spills source middle firstMissing)
    (second : BuiltTrace spills middle target secondMissing) :
    BuiltTrace spills source target (firstMissing + secondMissing) where
  trace := first.trace.concat second.trace
  noPop := first.trace.noPop_concat second.trace first.noPop second.noPop
  additions := by rw [Trace.additions_concat, first.additions, second.additions]

def PlacementStep.toBuiltTrace (step : PlacementStep spills fixed working value added) :
    BuiltTrace spills (fixed ++ working) ((fixed ++ [value]) ++ step.remaining) added :=
  ⟨step.trace, step.noPop, step.additions⟩

private theorem remaining_balance {working tail remaining : Stack}
    {value : Value} {missing : Multiset Value}
    (hbalance : ((value :: tail : Stack) : Multiset Value) = (working : Multiset Value) + missing)
    (hstep : {value} + (remaining : Multiset Value) = (working : Multiset Value)) :
    (tail : Multiset Value) = (remaining : Multiset Value) + missing := by
  apply add_left_cancel (a := ({value} : Multiset Value))
  calc
    {value} + (tail : Multiset Value) = (working : Multiset Value) + missing := by
      simpa only [Multiset.singleton_add, Multiset.cons_coe] using hbalance
    _ = {value} + ((remaining : Multiset Value) + missing) := by rw [← hstep, add_assoc]

-- Each recursive call fixes one target value. With growth, every retained
-- source stays in a working suffix of at most sixteen slots.
def buildWorking (spills : SpillSet) (fixed working target : Stack) (missing : Multiset Value)
    (hsmall : working.length ≤ MAX_SWAP_DEPTH + 1)
    (hspace : missing ≠ 0 → working.length ≤ MAX_DUP_DEPTH + 1)
    (hbalance : (target : Multiset Value) = (working : Multiset Value) + missing)
    (hseeds : seeds spills missing ≤ (working : Multiset Value)) :
    BuiltTrace spills (fixed ++ working) (fixed ++ target) missing := by
  cases target with
  | nil =>
    have hc := congrArg Multiset.card hbalance
    simp only [Multiset.coe_nil, Multiset.card_zero, Multiset.card_add, Multiset.coe_card] at hc
    have hw : working = [] := List.length_eq_zero_iff.mp (by omega)
    have hm : missing = 0 := Multiset.card_eq_zero.mp (by omega)
    subst working missing
    exact ⟨.Lit _, trivial, rfl⟩
  | cons value tail =>
    if hv : value ∈ missing then
      have hn : missing ≠ 0 := by intro he; simp [he] at hv
      have havailable : Free spills value ∨ value ∈ working := by
        by_cases hf : Free spills value
        · exact Or.inl hf
        · exact Or.inr ((seeds_le_iff _ _ _).mp hseeds value hv hf)
      let step := generateAndPlace spills fixed working value (hspace hn) havailable
      have hremaining : (step.remaining : Multiset Value) = (working : Multiset Value) := by
        apply add_left_cancel (a := ({value} : Multiset Value))
        exact step.balance.trans (add_comm _ _)
      have hlen : step.remaining.length = working.length := by
        simpa only [Multiset.coe_card] using congrArg Multiset.card hremaining
      have hnextBalance : (tail : Multiset Value) =
          (step.remaining : Multiset Value) + missing.erase value := by
        rw [hremaining]
        exact balance_erase_missing hbalance hv
      have hnextSeeds : seeds spills (missing.erase value) ≤
          (step.remaining : Multiset Value) := by
        rw [hremaining]
        exact (seeds_mono (Multiset.erase_le _ _)).trans hseeds
      let next := buildWorking spills (fixed ++ [value]) step.remaining tail
        (missing.erase value) (by omega) (by intro _; rw [hlen]; exact hspace hn)
        hnextBalance hnextSeeds
      exact (step.toBuiltTrace.trans next).cast rfl
        (by simp only [List.append_assoc, List.singleton_append])
        (by simp only [Multiset.singleton_add, Multiset.cons_erase hv])
    else
      have hvalue : value ∈ working := (balance_erase_source hbalance hv).1
      let step := placeExisting spills fixed working value hsmall hvalue
      have hremaining : {value} + (step.remaining : Multiset Value) =
          (working : Multiset Value) := by simpa only [add_zero] using step.balance
      have hlen : step.remaining.length + 1 = working.length := by
        simpa only [Multiset.card_add, Multiset.card_singleton, Multiset.coe_card,
          Nat.add_comm] using congrArg Multiset.card hremaining
      have hnextSeeds : seeds spills missing ≤ (step.remaining : Multiset Value) := by
        have hvseed : value ∉ seeds spills missing := by
          intro hm
          exact hv ((mem_seeds _ _ _).mp hm).1
        rw [← hremaining] at hseeds
        exact (Multiset.le_cons_of_notMem hvseed).mp hseeds
      let next := buildWorking spills (fixed ++ [value]) step.remaining tail missing
        (by omega) (by intro _; unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *; omega)
        (remaining_balance hbalance hremaining) hnextSeeds
      exact (step.toBuiltTrace.trans next).cast rfl
        (by simp only [List.append_assoc, List.singleton_append]) (zero_add _)
termination_by target.length
decreasing_by
  all_goals
    simp_all only [List.length_cons]
    omega

-- This constructor returns data in Type. It executes finite searches and
-- instruction constructors; it does not extract a trace from an existence proof.
def buildOfReserve (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (h : Reserve spills source target missing) : BuiltTrace spills source target missing := by
  let prepared := prepare spills source target missing h
  let first : BuiltTrace spills source (prepared.fixed ++ prepared.working) 0 :=
    ⟨prepared.trace, prepared.noPop, prepared.additions⟩
  let rest := buildWorking spills prepared.fixed prepared.working prepared.tail missing
    prepared.small prepared.space prepared.balance prepared.seeds
  exact (first.trans rest).cast rfl prepared.target_eq.symm (zero_add _)

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

theorem build_sound {result : BuiltTrace spills source target missing}
    (_h : build spills source target missing = some result) :
    result.trace.noPop ∧ result.trace.additions = missing :=
  ⟨result.noPop, result.additions⟩

end Shuffler.Placement
