import Shuffler.ExactBuild.Build

-- The implementation before the refactor, and the proof that both return the same trace.
namespace Shuffler.ExactBuild.Old

open Shuffler.Placement

structure PlacementStep (spills : SpillSet) (fixed working : Stack)
    (value : Value) (added : Multiset Value) where
  remaining : Stack
  trace : Trace spills (fixed ++ working) ((fixed ++ [value]) ++ remaining)
  noPop : trace.noPop
  additions : trace.additions = added
  balance : {value} + (remaining : Multiset Value) = (working : Multiset Value) + added

private theorem swap_after_prefix (fixed working : Stack) (a b : Nat) :
    (fixed ++ working).swap (fixed.length + a) (fixed.length + b) =
      fixed ++ working.swap a b := by
  induction fixed with
  | nil => simp
  | cons value fixed ih =>
    simpa only [List.cons_append, List.length_cons, Nat.add_right_comm,
      List.swap_cons] using congrArg (value :: ·) ih

-- A reachable suffix position can be exchanged with the top. A top-to-top
-- exchange emits no instruction.
private def swapSuffix (spills : SpillSet) (fixed working : Stack) (pos : Nat)
    (hpos : pos < working.length) (hsmall : working.length ≤ MAX_SWAP_DEPTH + 1) :
    { trace : Trace spills (fixed ++ working)
        (fixed ++ working.swap (working.length - 1) pos) //
      trace.noPop ∧ trace.additions = 0 } := by
  if he : pos = working.length - 1 then
    have ht : fixed ++ working = fixed ++ working.swap (working.length - 1) pos := by
      simp [he]
    exact ⟨ht ▸ .Lit (fixed ++ working),
      (Trace.noPop_cast _ _).mpr trivial, by rw [Trace.additions_cast]; rfl⟩
  else
    let depth := working.length - 1 - pos
    have hlen : depth < (fixed ++ working).length := by
      simp only [List.length_append]
      dsimp [depth]
      omega
    have hlo : 1 ≤ depth := by dsimp [depth]; omega
    have hhi : depth ≤ MAX_SWAP_DEPTH := by dsimp [depth]; omega
    let trace := Trace.Swap depth hlen hlo hhi (Trace.Lit (spills := spills) (fixed ++ working))
    have htop : (fixed ++ working).length - 1 = fixed.length + (working.length - 1) := by
      simp only [List.length_append]
      omega
    have hindex : (fixed ++ working).length - 1 - depth = fixed.length + pos := by
      simp only [List.length_append]
      dsimp [depth]
      omega
    have ht : (fixed ++ working).swap ((fixed ++ working).length - 1)
        ((fixed ++ working).length - 1 - depth) =
        fixed ++ working.swap (working.length - 1) pos := by
      rw [hindex, htop, swap_after_prefix]
    exact ⟨ht ▸ trace, (Trace.noPop_cast _ _).mpr trivial,
      by rw [Trace.additions_cast]; rfl⟩

private theorem list_eq_head_drop (values : Stack) (value : Value)
    (hlen : 0 < values.length) (hvalue : values[0] = value) :
    values = value :: values.drop 1 := by
  simpa only [hvalue, Nat.zero_add, List.drop_zero] using
    (List.getElem_cons_drop hlen).symm

-- Select a physical occurrence by a finite search, then place it with at
-- most two top swaps. The order of the remaining values is unrestricted.
def placeExisting (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_SWAP_DEPTH + 1) (hvalue : value ∈ working) :
    PlacementStep spills fixed working value 0 := by
  let pos := working.idxOf value
  have hpos : pos < working.length := List.idxOf_lt_length_iff.mpr hvalue
  have hlen : 0 < working.length := by omega
  let raised := working.swap (working.length - 1) pos
  let placed := raised.swap (raised.length - 1) 0
  have hraised : raised.length = working.length := List.length_swap
  have hplaced : placed.length = working.length := by simp only [placed, List.length_swap, hraised]
  have hhead : placed[0]'(by omega) = value := by
    dsimp [placed]
    rw [List.getElem_swap_right_of_lt (by omega)]
    simp only [raised, List.length_swap, List.getElem_swap_left_of_lt hpos]
    exact List.getElem_idxOf hpos
  have hcons : placed = value :: placed.drop 1 := list_eq_head_drop _ _ (by omega) hhead
  let first := swapSuffix spills fixed working pos hpos hsmall
  let second := swapSuffix spills fixed raised 0 (by omega) (by omega)
  let trace := first.val.concat second.val
  have ht : fixed ++ placed = (fixed ++ [value]) ++ placed.drop 1 := by
    calc
      fixed ++ placed = fixed ++ value :: placed.drop 1 := congrArg (fixed ++ ·) hcons
      _ = (fixed ++ [value]) ++ placed.drop 1 := by
        simp only [List.append_assoc, List.singleton_append]
  refine ⟨placed.drop 1, ht ▸ trace, ?_, ?_, ?_⟩
  · exact (Trace.noPop_cast _ _).mpr (first.val.noPop_concat second.val first.property.1 second.property.1)
  · rw [Trace.additions_cast]
    change (first.val.concat second.val).additions = 0
    rw [Trace.additions_concat, first.property.2, second.property.2, add_zero]
  · have hp : placed.Perm working :=
      (List.swap_perm raised _ _).trans (List.swap_perm working _ _)
    have hb := Multiset.coe_eq_coe.mpr hp
    rw [hcons] at hb
    simpa only [Multiset.cons_coe, Multiset.singleton_add, add_zero] using hb

private def appendValue (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_DUP_DEPTH + 1)
    (havailable : Free spills value ∨ value ∈ working) :
    { trace : Trace spills (fixed ++ working) ((fixed ++ working) ++ [value]) //
      trace.noPop ∧ trace.additions = {value} } := by
  if hpush : value.can_be_freely_generated then
    exact ⟨.Push value hpush (.Lit _), trivial, rfl⟩
  else if hload : spills.is_spilled value then
    match value with
    | .Var id => exact ⟨.Load id hload (.Lit _), trivial, rfl⟩
    | .Lit _ | .Wildcard | .FunctionReturnLabel => simp [SpillSet.is_spilled] at hload
  else
    have hvalue : value ∈ working := by
      rcases havailable with hf | hm
      · exact False.elim (hf.elim hpush hload)
      · exact hm
    let pos := working.idxOf value
    have hpos : pos < working.length := List.idxOf_lt_length_iff.mpr hvalue
    let index := working.length - pos
    have hlen : index ≤ (fixed ++ working).length := by
      simp only [List.length_append]
      dsimp [index]
      omega
    have hlo : 1 ≤ index := by dsimp [index]; omega
    have hhi : index ≤ MAX_DUP_DEPTH + 1 := by dsimp [index]; omega
    have hoffset : (fixed ++ working).length - index = fixed.length + pos := by
      simp only [List.length_append]
      dsimp [index]
      omega
    have hcopy : (fixed ++ working)[(fixed ++ working).length - index] = value := by
      simp only [hoffset]
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      exact List.getElem_idxOf hpos
    let trace := Trace.Dup index hlen hlo hhi (Trace.Lit (spills := spills) (fixed ++ working))
    have ht : (fixed ++ working) ++ [(fixed ++ working)[(fixed ++ working).length - index]] =
        (fixed ++ working) ++ [value] := by rw [hcopy]
    refine ⟨ht ▸ trace, (Trace.noPop_cast _ _).mpr trivial, ?_⟩
    rw [Trace.additions_cast]
    simp only [trace, Trace.additions, hcopy, zero_add]

-- Generate the next output before fixing it. The working region keeps its
-- entire previous multiset, so all remaining DUP sources are retained.
def generateAndPlace (spills : SpillSet) (fixed working : Stack) (value : Value)
    (hsmall : working.length ≤ MAX_DUP_DEPTH + 1)
    (havailable : Free spills value ∨ value ∈ working) :
    PlacementStep spills fixed working value {value} := by
  let grown := working ++ [value]
  have hlen : 0 < grown.length := by simp [grown]
  have hbound : grown.length ≤ MAX_SWAP_DEPTH + 1 := by
    simp only [grown, List.length_append, List.length_singleton]
    unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
    omega
  let placed := grown.swap (grown.length - 1) 0
  have hplaced : placed.length = grown.length := List.length_swap
  have hhead : placed[0]'(by omega) = value := by
    rw [List.getElem_swap_right_of_lt (by omega)]
    simp [grown]
  have hcons : placed = value :: placed.drop 1 := list_eq_head_drop _ _ (by omega) hhead
  let first := appendValue spills fixed working value hsmall havailable
  let second := swapSuffix spills fixed grown 0 hlen hbound
  have hassoc : (fixed ++ working) ++ [value] = fixed ++ grown := List.append_assoc _ _ _
  let firstTrace := hassoc ▸ first.val
  let trace := firstTrace.concat second.val
  have ht : fixed ++ placed = (fixed ++ [value]) ++ placed.drop 1 := by
    calc
      fixed ++ placed = fixed ++ value :: placed.drop 1 := congrArg (fixed ++ ·) hcons
      _ = (fixed ++ [value]) ++ placed.drop 1 := by
        simp only [List.append_assoc, List.singleton_append]
  refine ⟨placed.drop 1, ht ▸ trace, ?_, ?_, ?_⟩
  · exact (Trace.noPop_cast _ _).mpr
      (firstTrace.noPop_concat second.val ((Trace.noPop_cast _ _).mpr first.property.1) second.property.1)
  · rw [Trace.additions_cast]
    change (firstTrace.concat second.val).additions = {value}
    rw [Trace.additions_concat, second.property.2, add_zero]
    exact (Trace.additions_cast _ _).trans first.property.2
  · have hp : placed.Perm grown := List.swap_perm grown _ _
    have hb := Multiset.coe_eq_coe.mpr hp
    rw [hcons] at hb
    simpa only [grown, Multiset.cons_coe, Multiset.singleton_add,
      ← Multiset.coe_add, Multiset.coe_singleton] using hb


structure PreparedProblem (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) where
  fixed : Stack
  working : Stack
  tail : Stack
  trace : Trace spills source (fixed ++ working)
  noPop : trace.noPop
  additions : trace.additions = 0
  target_eq : target = fixed ++ tail
  small : working.length ≤ MAX_SWAP_DEPTH + 1
  space : missing ≠ 0 → working.length ≤ MAX_DUP_DEPTH + 1
  balance : (tail : Multiset Value) = (working : Multiset Value) + missing
  seeds : Shuffler.Placement.seeds spills missing ≤ (working : Multiset Value)

private theorem noPop_cast_source (h : source = other)
    (trace : Trace spills source target) :
    (h ▸ trace).noPop ↔ trace.noPop := by cases h; rfl

private theorem additions_cast_source (h : source = other)
    (trace : Trace spills source target) :
    (h ▸ trace).additions = trace.additions := by cases h; rfl

-- Keep the initially frozen prefix. Before any required growth from a full
-- seventeen-slot window, place its reserved output and retain all seeds.
def prepare (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (h : Reserve spills source target missing) :
    PreparedProblem spills source target missing := by
  let count := frozen source
  let fixed := source.take count
  let working := source.drop count
  let tail := target.drop count
  have hsource : fixed ++ working = source := List.take_append_drop _ _
  have htarget : target = fixed ++ tail := by
    calc
      target = target.take count ++ target.drop count := (List.take_append_drop _ _).symm
      _ = fixed ++ tail := by rw [h.2.1]
  have hsmall : working.length ≤ MAX_SWAP_DEPTH + 1 := by
    simp only [working, List.length_drop, count, frozen]
    omega
  have hbalance : (tail : Multiset Value) = (working : Multiset Value) + missing := by
    have hb := h.1
    rw [htarget, ← hsource] at hb
    simp only [← Multiset.coe_add, add_assoc] at hb
    exact add_left_cancel hb
  have hseeds : seeds spills missing ≤ (working : Multiset Value) :=
    (Multiset.le_add_left _ _).trans h.2.2
  let initialTrace : Trace spills source (fixed ++ working) := hsource.symm ▸ .Lit source
  let unchanged (hspace : missing ≠ 0 → working.length ≤ MAX_DUP_DEPTH + 1) :
      PreparedProblem spills source target missing := {
    fixed := fixed
    working := working
    tail := tail
    trace := initialTrace
    noPop := (Trace.noPop_cast _ _).mpr trivial
    additions := by rw [Trace.additions_cast]; rfl
    target_eq := htarget
    small := hsmall
    space := hspace
    balance := hbalance
    seeds := hseeds
  }
  if hzero : missing = 0 then
    exact unchanged (fun hne => False.elim (hne hzero))
  else if hspace : working.length ≤ MAX_DUP_DEPTH + 1 then
    exact unchanged (fun _ => hspace)
  else
    have hlarge : MAX_SWAP_DEPTH + 1 ≤ source.length := by
      have hw : working.length ≤ source.length := by
        simp only [working, List.length_drop]
        omega
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    have hcard := congrArg Multiset.card h.1
    simp only [Multiset.card_add, Multiset.coe_card] at hcard
    have hindex : count < target.length := by
      dsimp [count, frozen]
      unfold MAX_SWAP_DEPTH at hlarge ⊢
      omega
    let value := target[count]'hindex
    let rest := target.drop (count + 1)
    have hboundary : boundary source target missing = {value} := by
      simp [boundary, hzero, hlarge, count, value, List.getElem?_eq_getElem hindex]
    have hreserve : {value} + seeds spills missing ≤ (working : Multiset Value) := by
      simpa only [hboundary, working, count, window] using h.2.2
    have hvalue : value ∈ working := Multiset.mem_of_le hreserve (by simp)
    let step := placeExisting spills fixed working value hsmall hvalue
    have hstepBalance : {value} + (step.remaining : Multiset Value) =
        (working : Multiset Value) := by simpa only [add_zero] using step.balance
    have hstepCard := congrArg Multiset.card hstepBalance
    simp only [Multiset.card_add, Multiset.card_singleton, Multiset.coe_card] at hstepCard
    have hremaining : step.remaining.length ≤ MAX_DUP_DEPTH + 1 := by
      unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
      omega
    have htail : tail = value :: rest := List.drop_eq_getElem_cons hindex
    refine {
      fixed := fixed ++ [value]
      working := step.remaining
      tail := rest
      trace := hsource ▸ step.trace
      noPop := (noPop_cast_source _ _).mpr step.noPop
      additions := (additions_cast_source _ _).trans step.additions
      target_eq := ?_
      small := ?_
      space := fun _ => hremaining
      balance := ?_
      seeds := ?_
    }
    · rw [htarget, htail]
      simp only [List.append_assoc, List.singleton_append]
    · unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
      omega
    · rw [htail] at hbalance
      change {value} + (rest : Multiset Value) = (working : Multiset Value) + missing at hbalance
      rw [← hstepBalance, add_assoc] at hbalance
      exact add_left_cancel hbalance
    · rw [← hstepBalance] at hreserve
      exact (add_le_add_iff_left ({value} : Multiset Value)).mp hreserve


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

def buildOfReserve (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (h : Reserve spills source target missing) : BuiltTrace spills source target missing := by
  let prepared := prepare spills source target missing h
  let first : BuiltTrace spills source (prepared.fixed ++ prepared.working) 0 :=
    ⟨prepared.trace, prepared.noPop, prepared.additions⟩
  let rest := buildWorking spills prepared.fixed prepared.working prepared.tail missing
    prepared.small prepared.space prepared.balance prepared.seeds
  exact (first.trans rest).cast rfl prepared.target_eq.symm (zero_add _)

def build (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Option (BuiltTrace spills source target missing) :=
  if h : Reserve spills source target missing then some (buildOfReserve spills source target missing h)
  else none


theorem swapSuffix_trace (spills fixed working pos hpos hsmall) :
    (ExactBuild.swapSuffix spills fixed working pos hpos hsmall).trace =
      (swapSuffix spills fixed working pos hpos hsmall).val := by
  unfold ExactBuild.swapSuffix swapSuffix
  split <;> rfl

theorem placeExisting_trace (spills fixed working value hsmall hvalue) :
    (ExactBuild.placeExisting spills fixed working value hsmall hvalue).built.trace =
      (placeExisting spills fixed working value hsmall hvalue).trace := by
  unfold ExactBuild.placeExisting placeExisting
  simp only [PlacementStep.ofPlaced, BuiltTrace.castTarget, ExactBuild.BuiltTrace.trans,
    swapSuffix_trace]

theorem appendValue_trace (spills fixed working value hsmall havailable) :
    (ExactBuild.appendValue spills fixed working value hsmall havailable).trace =
      (appendValue spills fixed working value hsmall havailable).val := by
  unfold ExactBuild.appendValue appendValue
  split
  · rfl
  split
  · cases value <;> first | rfl | (exfalso; assumption)
  · rfl

theorem generateAndPlace_trace (spills fixed working value hsmall havailable) :
    (ExactBuild.generateAndPlace spills fixed working value hsmall havailable).built.trace =
      (generateAndPlace spills fixed working value hsmall havailable).trace := by
  unfold ExactBuild.generateAndPlace generateAndPlace
  simp only [PlacementStep.ofPlaced, BuiltTrace.castTarget, ExactBuild.BuiltTrace.trans,
    swapSuffix_trace, appendValue_trace]

theorem new_cast_trace (result : ExactBuild.BuiltTrace spills source target missing)
    (ht : target = other) (hm : missing = otherMissing) :
    (result.cast rfl ht hm).trace = ht ▸ result.trace := by
  subst ht hm
  rfl

theorem old_cast_trace (result : BuiltTrace spills source target missing)
    (ht : target = other) (hm : missing = otherMissing) :
    (result.cast rfl ht hm).trace = ht ▸ result.trace := by
  subst ht hm
  rfl

theorem buildWorking_trace (spills : SpillSet) (fixed working target : Stack)
    (missing : Multiset Value) (h : Working spills working target missing) :
    (ExactBuild.buildWorking spills fixed working target missing h).trace =
      (buildWorking spills fixed working target missing h.small h.space h.balance h.seeds).trace := by
  induction target generalizing fixed working missing with
  | nil =>
    obtain ⟨hw, hm⟩ := h.nil
    subst hw hm
    rw [ExactBuild.buildWorking, buildWorking]
    rfl
  | cons value tail ih =>
    rw [ExactBuild.buildWorking, buildWorking]
    by_cases hv : value ∈ missing
    · simp only [hv, ↓reduceDIte, PlacementStep.andThen, new_cast_trace, old_cast_trace,
        BuiltTrace.trans, ExactBuild.BuiltTrace.trans, PlacementStep.toBuiltTrace,
        generateAndPlace_trace, ih]
      rfl
    · simp only [hv, ↓reduceDIte, PlacementStep.andThen, new_cast_trace, old_cast_trace,
        BuiltTrace.trans, ExactBuild.BuiltTrace.trans, PlacementStep.toBuiltTrace,
        placeExisting_trace, ih]
      rfl


theorem new_cast_heq (result : ExactBuild.BuiltTrace spills source target missing)
    (hs : source = otherSource) (ht : target = other) (hm : missing = otherMissing) :
    HEq (result.cast hs ht hm).trace result.trace := by
  subst hs ht hm
  rfl

theorem old_source_heq (h : source = other) (trace : Trace spills source target) :
    HEq (h ▸ trace) trace := by
  subst h
  rfl

def Related (prepared : ExactBuild.PreparedProblem spills source target missing)
    (old : PreparedProblem spills source target missing) : Prop :=
  prepared.fixed = old.fixed ∧ prepared.working = old.working ∧ prepared.tail = old.tail ∧
    HEq prepared.built.trace old.trace

theorem prepare_trace (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (h : Reserve spills source target missing) :
    Related (ExactBuild.prepare spills source target missing h)
      (prepare spills source target missing h) := by
  unfold ExactBuild.prepare prepare
  dsimp only
  split_ifs with hzero hspace
  · exact ⟨rfl, rfl, rfl, HEq.rfl⟩
  · exact ⟨rfl, rfl, rfl, HEq.rfl⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    dsimp only
    refine (new_cast_heq _ _ _ _).trans ?_
    rw [placeExisting_trace]
    exact (old_source_heq _ _).symm

theorem compose_trace (prepared : ExactBuild.PreparedProblem spills source target missing)
    (old : PreparedProblem spills source target missing) (hr : Related prepared old) :
    ((prepared.built.trans (ExactBuild.buildWorking spills prepared.fixed prepared.working
        prepared.tail missing prepared.valid)).cast rfl prepared.target_eq.symm (zero_add _)).trace =
      (((BuiltTrace.mk old.trace old.noPop old.additions).trans (buildWorking spills old.fixed
        old.working old.tail missing old.small old.space old.balance old.seeds)).cast rfl
        old.target_eq.symm (zero_add _)).trace := by
  obtain ⟨fixed, working, tail, built, _, _⟩ := prepared
  obtain ⟨_, _, _, trace, _, _, _, _, _, _, _⟩ := old
  obtain ⟨rfl, rfl, rfl, ht⟩ := hr
  have ht : built.trace = trace := eq_of_heq ht
  subst ht
  simp only [new_cast_trace, old_cast_trace, BuiltTrace.trans, ExactBuild.BuiltTrace.trans,
    buildWorking_trace]

theorem buildOfReserve_trace (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) (h : Reserve spills source target missing) :
    (ExactBuild.buildOfReserve spills source target missing h).trace =
      (buildOfReserve spills source target missing h).trace :=
  compose_trace _ _ (prepare_trace spills source target missing h)

theorem build_trace (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    (ExactBuild.build spills source target missing).map (·.trace) =
      (build spills source target missing).map (·.trace) := by
  unfold ExactBuild.build build
  by_cases h : Reserve spills source target missing
  · simp only [h, ↓reduceDIte, Option.map_some, buildOfReserve_trace]
  · simp only [h, ↓reduceDIte, Option.map_none]

end Shuffler.ExactBuild.Old
