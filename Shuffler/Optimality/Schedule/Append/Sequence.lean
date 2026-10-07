import Shuffler.Optimality.Schedule.Append
import Shuffler.Optimality.Schedule.Append.Steps

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

-- With no SWAP or POP, every legal generator has the same next stack.
-- Choosing the cheapest one therefore preserves every later legal step.
theorem appendFrom_le_births (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (target source : Stack) (missing : Multiset Value)
    (values : Stack) (ops : List Op)
    (hvalues : target = source ++ values)
    (hbalance : (target : Multiset Value) = (source : Multiset Value) + missing)
    (hbirths : ∀ op ∈ ops, BirthOp op)
    (hsim : simulate spills source ops = some target) :
    ∃ selected,
      appendFrom costs weights spills target source missing values = some selected ∧
      simulate spills source selected = some target ∧
      (opsCost costs selected).score weights ≤ (opsCost costs ops).score weights := by
  induction ops generalizing source missing values with
  | nil =>
      have ht : target = source := (Option.some.inj hsim).symm
      have hv : values = [] := by
        have hl := congrArg List.length hvalues
        simp only [ht, List.length_append] at hl
        exact List.length_eq_zero_iff.mp (by omega)
      have hm : missing = 0 := by
        apply add_left_cancel (a := (source : Multiset Value))
        simpa [ht] using hbalance.symm
      refine ⟨[], ?_, ?_, Nat.le_refl _⟩
      · simp [appendFrom, hv, hm, ht]
      · simp [ht]
  | cons op ops ih =>
      rw [simulate_cons] at hsim
      cases hr : replayStep spills source op with
      | none => simp [hr] at hsim
      | some step =>
          simp only [hr, Option.bind_some] at hsim
          obtain ⟨value, ht, offered, hmem, hcost⟩ :=
            birthOp_step costs spills source op step (hbirths op (by simp)) hr
          have hrest : simulate spills (source ++ [value]) ops = some target := by
            simpa [ht] using hsim
          have hrestBirths : ∀ other ∈ ops, BirthOp other :=
            fun other ho => hbirths other (by simp [ho])
          obtain ⟨rest, htarget⟩ := births_suffix costs spills (source ++ [value]) target ops hrestBirths hrest
          have hv : values = value :: rest := by
            apply List.append_cancel_left (as := source)
            calc
              source ++ values = target := hvalues.symm
              _ = source ++ (value :: rest) := by simpa [List.append_assoc] using htarget
          subst values
          obtain ⟨hmissing, hreserve⟩ := reserve_after_birth spills source target missing value ops hbalance hrest
          have hn : generationOps spills source value ≠ [] := by
            intro he
            simp [he] at hmem
          obtain ⟨chosen, hchosen⟩ := Option.isSome_iff_exists.mp
            (cheapestGeneration_isSome costs weights spills source value hn)
          have hmap := generationOp_target spills source value chosen
            (cheapestGeneration_mem costs weights spills source value chosen hchosen)
          have hprice := cheapestGeneration_le_mem costs weights spills source value chosen offered hchosen hmem
          rw [hcost] at hprice
          cases hc : replayStep spills source chosen with
          | none => simp [hc] at hmap
          | some chosenStep =>
              have htChosen : chosenStep.target = source ++ [value] := by
                simpa only [hc, Option.map_some, Option.some.injEq] using hmap
              obtain ⟨later, hlater, hsimLater, hpriceLater⟩ := ih (source ++ [value])
                (missing.erase value) rest htarget hreserve.1 hrestBirths hrest
              refine ⟨chosen :: later, ?_, ?_, ?_⟩
              · simp [appendFrom, hmissing, hchosen, hc, htChosen, hreserve, hlater]
              · rw [simulate_cons, hc, Option.bind_some, htChosen]
                exact hsimLater
              · simp only [opsCost, Cost.score_add]
                omega

theorem appendPlan_le_births (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) (ops : List Op)
    (hbalance : (target : Multiset Value) = (source : Multiset Value) + missing)
    (hbirths : ∀ op ∈ ops, BirthOp op)
    (hsim : simulate spills source ops = some target) :
    ∃ selected,
      appendPlan costs weights spills source target missing = some selected ∧
      simulate spills source selected = some target ∧
      (opsCost costs selected).score weights ≤ (opsCost costs ops).score weights := by
  obtain ⟨values, ht⟩ := births_suffix costs spills source target ops hbirths hsim
  obtain ⟨selected, hs, htSelected, hc⟩ :=
    appendFrom_le_births costs weights spills target source missing values ops ht hbalance hbirths hsim
  refine ⟨selected, ?_, htSelected, hc⟩
  simpa [appendPlan, ht] using hs

end Shuffler.Optimality.Schedule
