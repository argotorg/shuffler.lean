import Shuffler.Optimality.Schedule.Defs
import Shuffler.Optimality.Replay.Theorems
import Shuffler.Optimality.Schedule.Simulation
import Shuffler.Optimality.GenerationChoice.Theorems
import Shuffler.Optimality.Schedule.Prefix
import Shuffler.Optimality.Schedule.Theorems

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

-- A boundary value that is not requested is not one of the hard seeds.
-- Its existing occurrence can be reserved without taking a seed away.
theorem reserve_existing_boundary (working missing : Multiset Value) (value : Value)
    (hseeds : seeds spills missing ≤ working) (hv : value ∈ working)
    (hnot : value ∉ missing) : {value} + seeds spills missing ≤ working := by
  have hnotseed : value ∉ seeds spills missing := by
    intro hs
    exact hnot ((mem_seeds _ _ _).mp hs).1
  have herase : seeds spills missing ≤ working.erase value := by
    rw [← Multiset.cons_erase hv] at hseeds
    exact (Multiset.le_cons_of_notMem hnotseed).mp hseeds
  simpa only [Multiset.singleton_add, Multiset.cons_erase hv] using
    Multiset.cons_le_cons value herase

-- Given readable seeds, one requested birth can reserve the next boundary.
-- Birth that boundary value when it is requested; otherwise any request works.
theorem exists_birth_preserving_boundary (working missing : Multiset Value) (boundary : Value)
    (hseeds : seeds spills missing ≤ working) (hne : missing ≠ 0)
    (hboundary : boundary ∈ working + missing) :
    ∃ value, value ∈ missing ∧ (value = boundary ∨ boundary ∉ missing) ∧
      (Free spills value ∨ value ∈ working) ∧
      {boundary} + seeds spills (missing.erase value) ≤ working + {value} := by
  have havailable (value : Value) (hv : value ∈ missing) :
      Free spills value ∨ value ∈ working := by
    by_cases hf : Free spills value
    · exact Or.inl hf
    · exact Or.inr ((seeds_le_iff _ _ _).mp hseeds value hv hf)
  by_cases hb : boundary ∈ missing
  · refine ⟨boundary, hb, Or.inl rfl, havailable boundary hb, ?_⟩
    have hs := (seeds_mono (spills := spills) (Multiset.erase_le boundary missing)).trans hseeds
    calc
      {boundary} + seeds spills (missing.erase boundary) ≤ {boundary} + working :=
        add_le_add (le_refl _) hs
      _ = working + {boundary} := add_comm _ _
  · obtain ⟨value, hv⟩ := Multiset.exists_mem_of_ne_zero hne
    have hw : boundary ∈ working := (Multiset.mem_add.mp hboundary).resolve_right hb
    have hr := reserve_existing_boundary working missing boundary hseeds hw hb
    refine ⟨value, hv, Or.inr hb, havailable value hv, ?_⟩
    exact ((add_le_add (le_refl ({boundary} : Multiset Value))
      (seeds_mono (Multiset.erase_le value missing))).trans hr).trans
        (Multiset.le_add_right _ _)

theorem birth_preserves_boundary (working missing : Multiset Value) (boundary value : Value)
    (hseeds : seeds spills missing ≤ working) (hv : value ∈ missing)
    (hboundary : boundary ∈ working + missing)
    (hchoice : value = boundary ∨ boundary ∉ missing) :
    {boundary} + seeds spills (missing.erase value) ≤ working + {value} := by
  rcases hchoice with he | hb
  · subst value
    calc
      {boundary} + seeds spills (missing.erase boundary) ≤ {boundary} + working :=
        add_le_add (le_refl _) ((seeds_mono (Multiset.erase_le boundary missing)).trans hseeds)
      _ = working + {boundary} := add_comm _ _
  · have hw : boundary ∈ working := (Multiset.mem_add.mp hboundary).resolve_right hb
    have hr := reserve_existing_boundary working missing boundary hseeds hw hb
    exact ((add_le_add (le_refl ({boundary} : Multiset Value))
      (seeds_mono (Multiset.erase_le value missing))).trans hr).trans
        (Multiset.le_add_right _ _)

theorem prepared_birth_reserve (fixed working tail : Stack) (missing : Multiset Value)
    (value : Value)
    (hsize : working.length ≤ MAX_DUP_DEPTH + 1)
    (hshape : fixed = [] ∨ working.length = MAX_DUP_DEPTH + 1)
    (hbalance : (tail : Multiset Value) = (working : Multiset Value) + missing)
    (hseeds : seeds spills missing ≤ (working : Multiset Value))
    (hv : value ∈ missing)
    (hchoice : ∀ boundary, tail[0]? = some boundary →
      boundary ∈ missing → value = boundary) :
    Reserve spills ((fixed ++ working) ++ [value]) (fixed ++ tail) (missing.erase value) := by
  have hb : (fixed ++ tail : Multiset Value) =
      (((fixed ++ working) ++ [value] : Stack) : Multiset Value) + missing.erase value := by
    simp only [← Multiset.coe_add, Multiset.coe_singleton, hbalance, add_assoc]
    rw [Multiset.singleton_add, Multiset.cons_erase hv]
  refine ⟨hb, ?_, ?_⟩
  · by_cases hfull : working.length = MAX_DUP_DEPTH + 1
    · have hf : frozen ((fixed ++ working) ++ [value]) = fixed.length := by
        simp only [frozen, List.length_append, List.length_singleton, hfull]
        unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH
        omega
      rw [hf]
      simp
    · have hfixed : fixed = [] := hshape.resolve_right hfull
      subst fixed
      have hf : frozen (([] ++ working) ++ [value]) = 0 := by
        simp only [frozen, List.nil_append, List.length_append, List.length_singleton]
        unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
        omega
      rw [hf]
      rfl
  · by_cases hfull : working.length = MAX_DUP_DEPTH + 1
    · have hf : frozen ((fixed ++ working) ++ [value]) = fixed.length := by
        simp only [frozen, List.length_append, List.length_singleton, hfull]
        unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH
        omega
      have hw : window ((fixed ++ working) ++ [value]) = working ++ [value] := by
        unfold window
        rw [hf, List.append_assoc]
        simp
      rw [hw]
      by_cases hz : missing.erase value = 0
      · simp [boundary, hz, seeds]
      · cases tail with
        | nil =>
            have hc := congrArg Multiset.card hbalance
            simp only [Multiset.coe_nil, Multiset.card_zero, Multiset.card_add,
              Multiset.coe_card] at hc
            unfold MAX_DUP_DEPTH at hfull
            omega
        | cons boundary rest =>
            have hm : boundary ∈ (working : Multiset Value) + missing := hbalance ▸ (by simp)
            have hc : value = boundary ∨ boundary ∉ missing := by
              by_cases hm : boundary ∈ missing
              · exact Or.inl (hchoice boundary rfl hm)
              · exact Or.inr hm
            have hr := birth_preserves_boundary (working : Multiset Value) missing boundary value
              hseeds hv hm hc
            have hlarge : MAX_SWAP_DEPTH + 1 ≤ ((fixed ++ working) ++ [value]).length := by
              simp only [List.length_append, List.length_singleton, hfull]
              unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH
              omega
            have hbound : Placement.boundary ((fixed ++ working) ++ [value])
                (fixed ++ boundary :: rest) (missing.erase value) = {boundary} := by
              unfold Placement.boundary
              rw [ite_eq_left ⟨hz, hlarge⟩, hf]
              simp
            rw [hbound]
            simpa only [← Multiset.coe_add, Multiset.coe_singleton] using hr
    · have hfixed : fixed = [] := hshape.resolve_right hfull
      subst fixed
      have hsmall : working.length + 1 < MAX_SWAP_DEPTH + 1 := by
        unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
        omega
      have hf : frozen (([] ++ working) ++ [value]) = 0 := by
        simp only [frozen, List.nil_append, List.length_append, List.length_singleton]
        omega
      have hs := (seeds_mono (spills := spills) (Multiset.erase_le value missing)).trans hseeds
      have hbound : boundary (([] ++ working) ++ [value]) ([] ++ tail)
          (missing.erase value) = 0 := by
        unfold boundary
        apply ite_eq_right
        simp only [List.nil_append, List.length_append, List.length_singleton]
        omega
      rw [hbound, zero_add]
      unfold window
      rw [hf]
      simpa only [List.nil_append, List.drop_zero, ← Multiset.coe_add, Multiset.coe_singleton] using
        hs.trans (Multiset.le_add_right (working : Multiset Value) {value})

theorem birthValues_first (stack target : Stack) (missing : Multiset Value)
    (hbalance : (target : Multiset Value) = (stack : Multiset Value) + missing)
    (hne : missing ≠ 0) : ∃ value, value ∈ missing ∧ value ∈ birthValues stack target missing := by
  obtain ⟨value, hv⟩ := Multiset.exists_mem_of_ne_zero hne
  have ht : value ∈ target := by
    change value ∈ (target : Multiset Value)
    rw [hbalance]
    exact Multiset.mem_add.mpr (Or.inr hv)
  have hs : (target.find? fun v => decide (v ∈ missing)).isSome :=
    List.find?_isSome.mpr ⟨value, ht, by simpa only [decide_eq_true_eq] using hv⟩
  obtain ⟨first, hfirst⟩ := Option.isSome_iff_exists.mp hs
  have hf : first ∈ missing := by simpa only [decide_eq_true_eq] using List.find?_some hfirst
  exact ⟨first, hf, by simp [birthValues, hfirst, hf]⟩

theorem birthValues_near (stack target : Stack) (missing : Multiset Value) (value : Value)
    (hv : value ∈ missing)
    (hn : value ∈ (target.drop (frozen stack)).take (MAX_SWAP_DEPTH + 1)) :
    value ∈ birthValues stack target missing := by
  simp [birthValues, hv, hn]

theorem birthValues_next_boundary (stack fixed tail : Stack) (missing : Multiset Value)
    (value : Value) (hv : value ∈ missing) (hhead : tail[0]? = some value)
    (hlo : frozen stack ≤ fixed.length) (hhi : fixed.length ≤ frozen stack + 1) :
    value ∈ birthValues stack (fixed ++ tail) missing := by
  apply birthValues_near _ _ _ _ hv
  have hget : (fixed ++ tail)[fixed.length]? = some value := by
    simpa [List.getElem?_append] using hhead
  obtain ⟨hpos, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
  apply List.mem_take_iff_getElem.mpr
  refine ⟨fixed.length - frozen stack, ?_, ?_⟩
  · simp only [List.length_drop]
    unfold MAX_SWAP_DEPTH
    omega
  · rw [List.getElem_drop]
    convert hvalue using 1
    congr 1
    omega

theorem readable_of_working (fixed working : Stack) (value : Value)
    (hsize : working.length ≤ MAX_DUP_DEPTH + 1) (hv : value ∈ working) :
    value ∈ (fixed ++ working).reverse.take (MAX_DUP_DEPTH + 1) := by
  rw [List.reverse_append, List.take_append,
    List.take_of_length_le (by simpa only [List.length_reverse] using hsize)]
  exact List.mem_append_left _ (List.mem_reverse.mpr hv)

theorem makeCandidate_isSome (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (stack target : Stack) (missing : Multiset Value) (before : List Op)
    (prepared : Stack) (value : Value)
    (hsim : simulate spills stack before = some prepared)
    (havailable : Free spills value ∨ value ∈ prepared.reverse.take (MAX_DUP_DEPTH + 1))
    (hreserve : Reserve spills (prepared ++ [value]) target (missing.erase value)) :
    (makeCandidate costs weights spills stack target missing before value).isSome := by
  have hs := cheapestGeneration_isSome costs weights spills prepared value
    (generationOps_nonempty spills prepared value havailable)
  obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp hs
  have hgen : simulate spills prepared [op] = some (prepared ++ [value]) := by
    rw [simulate_singleton]
    exact generationOp_target spills prepared value op
      (cheapestGeneration_mem costs weights spills prepared value op hop)
  have hafter : simulate spills stack (before ++ [op]) = some (prepared ++ [value]) := by
    rw [simulate_append, hsim, Option.bind_some, hgen]
  simp [makeCandidate, hsim, hop, hafter, hreserve]

private theorem choose_isSome_of_mem (strategy : Strategy) (candidates : List Candidate)
    (candidate : Candidate) (h : candidate ∈ candidates) : (choose strategy candidates).isSome := by
  cases candidates with
  | nil => simp at h
  | cons first rest => rfl

-- Ranking is free to choose any accepted candidate. At least one legal
-- candidate exists whenever Reserve holds and one requested birth remains.
theorem next_isSome (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack target : Stack) (missing : Multiset Value)
    (hreserve : Reserve spills stack target missing) (hne : missing ≠ 0) :
    (next strategy costs weights spills stack target missing).isSome := by
  obtain ⟨before, fixed, working, tail, hbefore, hsim, htarget, hsize, hshape,
      hbalance, hseeds, hlo, hhi⟩ := prefixes_prepare spills stack target missing hreserve hne
  obtain ⟨first, hfirst, hfirstMem⟩ := birthValues_first stack target missing hreserve.1 hne
  have hvalue : ∃ value, value ∈ missing ∧ value ∈ birthValues stack target missing ∧
      ∀ boundary, tail[0]? = some boundary → boundary ∈ missing → value = boundary := by
    cases hh : tail[0]? with
    | none => exact ⟨first, hfirst, hfirstMem, by intro boundary hb; simp at hb⟩
    | some boundary =>
        by_cases hb : boundary ∈ missing
        · refine ⟨boundary, hb, ?_, ?_⟩
          · rw [htarget]
            exact birthValues_next_boundary stack fixed tail missing boundary hb hh hlo hhi
          · intro other ho _
            exact Option.some.inj ho
        · refine ⟨first, hfirst, hfirstMem, ?_⟩
          intro other ho hm
          have he : boundary = other := Option.some.inj ho
          subst other
          exact False.elim (hb hm)
  obtain ⟨value, hv, hmem, hchoice⟩ := hvalue
  have havailable : Free spills value ∨
      value ∈ (fixed ++ working).reverse.take (MAX_DUP_DEPTH + 1) := by
    by_cases hf : Free spills value
    · exact Or.inl hf
    · exact Or.inr (readable_of_working fixed working value hsize
        ((seeds_le_iff _ _ _).mp hseeds value hv hf))
  have hnextReserve : Reserve spills ((fixed ++ working) ++ [value]) target (missing.erase value) := by
    rw [htarget]
    exact prepared_birth_reserve fixed working tail missing value hsize hshape hbalance hseeds hv hchoice
  have hsome := makeCandidate_isSome costs weights spills stack target missing before
    (fixed ++ working) value hsim havailable hnextReserve
  obtain ⟨candidate, hcandidate⟩ := Option.isSome_iff_exists.mp hsome
  apply choose_isSome_of_mem strategy _ candidate
  apply List.mem_flatMap.mpr
  refine ⟨before, ?_, ?_⟩
  · simp only [List.mem_dedup, List.mem_append]
    exact Or.inl (Or.inl hbefore)
  · exact List.mem_filterMap.mpr ⟨value, hmem, hcandidate⟩

theorem next_missing_card (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (stack target : Stack) (missing : Multiset Value) (result : Candidate)
    (h : next strategy costs weights spills stack target missing = some result) :
    result.missing.card + 1 = missing.card := by
  have hm := choose_mem strategy _ result h
  obtain ⟨before, _, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨value, hv, he⟩ := List.mem_filterMap.mp hm
  have hvalue : value ∈ missing := by
    simp only [birthValues, List.mem_dedup, List.mem_filter, decide_eq_true_eq] at hv
    exact hv.2
  rw [(makeCandidate_post costs weights spills stack target missing before value result he).2]
  simpa only [Multiset.card_cons] using congrArg Multiset.card (Multiset.cons_erase hvalue)

theorem rounds_isSome (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (target : Stack) (fuel : Nat) (stack : Stack)
    (missing : Multiset Value) (reversed : List Op)
    (hreserve : Reserve spills stack target missing) (hcard : fuel = missing.card) :
    (rounds strategy costs weights spills target fuel stack missing reversed).isSome := by
  induction fuel generalizing stack missing reversed with
  | zero =>
      have hz : missing = 0 := Multiset.card_eq_zero.mp hcard.symm
      have hs := ValueGraph.build_complete spills stack target (by simpa only [hz] using hreserve)
      obtain ⟨built, hb⟩ := Option.isSome_iff_exists.mp hs
      simp [rounds, hz, finish, hb]
  | succ fuel ih =>
      have hn : missing ≠ 0 := by intro hz; simp [hz] at hcard
      have hs := next_isSome strategy costs weights spills stack target missing hreserve hn
      obtain ⟨result, hr⟩ := Option.isSome_iff_exists.mp hs
      have hc := next_missing_card strategy costs weights spills stack target missing result hr
      have hi := ih result.stack result.missing (result.ops.reverse ++ reversed)
        (next_reserve strategy costs weights spills stack target missing result hr) (by omega)
      simpa [rounds, hr] using hi

-- This completeness result concerns the raw policy search itself. It does
-- not call the complete portfolio incumbent or use its fallback trace.
theorem plan_isSome (strategy : Strategy) (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (hreserve : Reserve spills source target missing) :
    (plan strategy costs weights spills source target missing).isSome :=
  rounds_isSome strategy costs weights spills target missing.card source missing [] hreserve rfl

end Shuffler.Optimality.Schedule
