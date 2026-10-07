import Shuffler.Optimality.CoupledBound
import Shuffler.Optimality.Transport.Theorems
import Shuffler.Optimality.GapCount.Theorems
import Shuffler.Optimality.ForcedIntroduction.Theorems

namespace Shuffler.Optimality.Capped

inductive Select : List Choice → Nat → Nat → Prop where
  | nil : Select [] 0 0
  | retain (choice : Choice) (selection : Select rest premium required) :
      Select (choice :: rest) premium (choice.retain + required)
  | regenerate (choice : Choice) (h : choice.regenerate = some (p, r))
      (selection : Select rest premium required) :
      Select (choice :: rest) (p + premium) (r + required)

theorem sub_add_sub (a b c : Nat) : (a - c) + (b - (c - a)) = a + b - c := by omega

theorem table_le_selected (swapPrice K : Nat) (selected : Select choices premium required)
    (cap : Nat) (hcap : cap < K + 1) :
    (table swapPrice K choices)[cap] ≤ premium + swapPrice * (required - cap) := by
  induction selected generalizing cap with
  | nil => simp [table]
  | @retain rest premium required choice selected ih =>
      have hi := ih (cap - choice.retain) (by omega)
      have hr : swapPrice * (choice.retain - cap) +
          (table swapPrice K rest)[cap - choice.retain] ≤
            premium + swapPrice * (choice.retain + required - cap) := by
        rw [← sub_add_sub choice.retain required cap, Nat.mul_add]
        omega
      cases choice with
      | mk retain regenerate =>
          cases regenerate with
          | none => simpa only [table, List.foldr_cons, extend, Vector.getElem_ofFn] using hr
          | some pair =>
              rcases pair with ⟨p, r⟩
              simp only [table, List.foldr_cons, extend, Vector.getElem_ofFn]
              exact (Nat.min_le_left _ _).trans hr
  | @regenerate p r rest premium required choice h selected ih =>
      have hi := ih (cap - r) (by omega)
      simp only [table, List.foldr_cons, extend, Vector.getElem_ofFn, h]
      apply (Nat.min_le_right _ _).trans
      change p + swapPrice * (r - cap) + (table swapPrice K rest)[cap - r] ≤ _
      rw [← sub_add_sub r required cap, Nat.mul_add]
      omega


theorem bound_le_selected (swapPrice K : Nat) (selected : Select choices premium required) :
    bound swapPrice K choices ≤ premium + swapPrice * max K required := by
  have ht := table_le_selected swapPrice K selected K (by omega)
  have he : K + (required - K) = max K required := by omega
  unfold bound
  have hs := Nat.add_le_add_left ht (swapPrice * K)
  rw [Nat.add_left_comm, ← Nat.mul_add, he] at hs
  exact hs

theorem bound_le_accounting (swapPrice K : Nat) (selected : Select choices premium required)
    (hp : premium ≤ actualPremium) (hr : required ≤ actualSwaps) (hk : K ≤ actualSwaps) :
    bound swapPrice K choices ≤ actualPremium + swapPrice * actualSwaps := by
  apply (bound_le_selected swapPrice K selected).trans
  exact Nat.add_le_add hp (Nat.mul_le_mul_left _ (Nat.max_le.mpr ⟨hk, hr⟩))

def Fits (choice : Choice) (premium required : Nat) : Prop :=
  choice.retain ≤ required ∨
    ∃ p r, choice.regenerate = some (p, r) ∧ p ≤ premium ∧ r ≤ required

theorem exists_selection (items : List α) (choose : α → Choice)
    (premium required : α → Nat) (fits : ∀ item ∈ items, Fits (choose item) (premium item) (required item)) :
    ∃ p r, Select (items.map choose) p r ∧
      p ≤ (items.map premium).sum ∧ r ≤ (items.map required).sum := by
  induction items with
  | nil => exact ⟨0, 0, .nil, by simp, by simp⟩
  | cons item items ih =>
      obtain ⟨p, r, selected, hp, hr⟩ := ih (fun x hx => fits x (by simp [hx]))
      rcases fits item (by simp) with hretain | ⟨dp, dr, hd, hp', hr'⟩
      · refine ⟨p, (choose item).retain + r, .retain _ selected, ?_, ?_⟩ <;>
          simp only [List.map_cons, List.sum_cons] <;> omega
      · refine ⟨dp + p, dr + r, .regenerate _ hd selected, ?_, ?_⟩ <;>
          simp only [List.map_cons, List.sum_cons] <;> omega

theorem bound_le_sum_accounting (swapPrice K : Nat) (items : List α) (choose : α → Choice)
    (premium required : α → Nat) (fits : ∀ item ∈ items, Fits (choose item) (premium item) (required item))
    (hp : (items.map premium).sum ≤ actualPremium)
    (hr : (items.map required).sum ≤ actualSwaps) (hk : K ≤ actualSwaps) :
    bound swapPrice K (items.map choose) ≤ actualPremium + swapPrice * actualSwaps := by
  obtain ⟨p, r, selected, hp', hr'⟩ := exists_selection items choose premium required fits
  exact bound_le_accounting swapPrice K selected (hp'.trans hp) (hr'.trans hr) hk

end Shuffler.Optimality.Capped

namespace Shuffler.Optimality

theorem coupledValueChoice_fits (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (he : Eligible missing trace) :
    Capped.Fits (coupledValueChoice costs weights spills source target missing value)
      ((directPrice costs weights spills value - unitPrice costs weights spills value) *
        Lineage.directCount value trace -
        if ForcedIntroduction.Required value source target missing then
          directPrice costs weights spills value - unitPrice costs weights spills value else 0)
      (Lineage.upwardCount value trace) := by
  have ht := Transport.requiredSwaps_le_upwardCount value trace he.1
  by_cases hr : ForcedIntroduction.Required value source target missing
  · left
    simpa only [coupledValueChoice, hr, ite_true] using ht
  simp only [hr, ite_false, Nat.sub_zero]
  by_cases hd : Lineage.directCount value trace = 0
  · left
    have hl := Lineage.requiredSwaps_le_upwardCount value trace hd
    rw [he.2] at hl
    have hg := GapCount.requiredSwaps_le_upwardCount value trace he.1 hd
    simpa only [coupledValueChoice, hr, ite_false] using
      Nat.max_le.mpr ⟨ht, Nat.max_le.mpr ⟨hl, hg⟩⟩
  · right
    have hfree : Shuffler.Placement.Free spills value := by
      by_contra hn
      exact hd (Lineage.directCount_eq_zero_of_not_free value trace hn)
    have hmissing : 0 < missing.count value := by
      have hc := Lineage.additions_count_eq value trace
      rw [he.2] at hc
      omega
    refine ⟨directPrice costs weights spills value - unitPrice costs weights spills value,
      Transport.requiredSwaps value source target, ?_, ?_, ht⟩
    · simp only [coupledValueChoice, hr, ite_false, hfree, hmissing, and_self, ite_true]
    · have hp := Nat.mul_le_mul_left
        (directPrice costs weights spills value - unitPrice costs weights spills value)
        (show 1 ≤ Lineage.directCount value trace by omega)
      simpa using hp

theorem forcedIntroductionPremium_le (costs : PrimitiveCosts) (weights : Weights)
    (value : Value) (trace : Trace spills source target) (he : Eligible missing trace) :
    (if ForcedIntroduction.Required value source target missing then
      directPrice costs weights spills value - unitPrice costs weights spills value else 0) ≤
      (directPrice costs weights spills value - unitPrice costs weights spills value) *
        Lineage.directCount value trace := by
  by_cases hr : ForcedIntroduction.Required value source target missing
  · simp only [hr, ite_true]
    exact Nat.le_mul_of_pos_right _
      (ForcedIntroduction.Required.directCount_pos value trace he.1 (he.2.symm ▸ hr))
  · simp only [hr, ite_false, Nat.zero_le]

theorem baseline_add_coupledBound_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace) (hk : swapFloor ≤ trace.swapCount) :
    baseline costs weights spills source missing +
      coupledBound costs weights spills source target missing swapFloor ≤
        (traceCost costs trace).score weights := by
  let premium := fun value => directPrice costs weights spills value - unitPrice costs weights spills value
  let forced := fun value => if ForcedIntroduction.Required value source target missing then premium value else 0
  have accounting : ForcedIntroduction.bound costs weights spills source target missing +
      (source.dedup.map (fun value => premium value * Lineage.directCount value trace - forced value)).sum =
        reintroductionSurcharge costs weights trace := by
    rw [← List.sum_toFinset _ (List.nodup_dedup source), List.toFinset_dedup]
    unfold ForcedIntroduction.bound reintroductionSurcharge
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro value _
    have hp := forcedIntroductionPremium_le costs weights value trace he
    dsimp [premium, forced]
    omega
  have hh := Capped.bound_le_sum_accounting (costs.swap.score weights) (min 17 swapFloor)
    source.dedup (coupledValueChoice costs weights spills source target missing)
    (fun value => premium value * Lineage.directCount value trace - forced value)
    (fun value => Lineage.upwardCount value trace)
    (fun value _ => coupledValueChoice_fits costs weights value trace he)
    (actualSwaps := trace.swapCount) (Nat.le_refl _)
    (by rw [← List.sum_toFinset _ (List.nodup_dedup source), List.toFinset_dedup]
        exact Lineage.sum_upwardCount_le source.toFinset trace)
    ((Nat.min_le_right _ _).trans hk)
  have hs := baseline_add_swapCost_add_reintroductions_le_score_of_eligible costs weights trace he
  unfold coupledBound
  omega

end Shuffler.Optimality

namespace Shuffler.Optimality.Capped

theorem table_attained (swapPrice K : Nat) (choices : List Choice) (cap : Nat) (hcap : cap < K + 1) :
    ∃ p r, Select choices p r ∧ (table swapPrice K choices)[cap] = p + swapPrice * (r - cap) := by
  induction choices generalizing cap with
  | nil => exact ⟨0, 0, .nil, by simp [table]⟩
  | cons choice rest ih =>
      obtain ⟨p, r, hs, he⟩ := ih (cap - choice.retain) (by omega)
      have hretain : swapPrice * (choice.retain - cap) +
          (table swapPrice K rest)[cap - choice.retain] = p + swapPrice * (choice.retain + r - cap) := by
        rw [he, ← sub_add_sub choice.retain r cap, Nat.mul_add]
        omega
      cases choice with
      | mk retain regenerate =>
          cases regenerate with
          | none =>
              refine ⟨p, retain + r, .retain _ hs, ?_⟩
              simpa only [table, List.foldr_cons, extend, Vector.getElem_ofFn] using hretain
          | some pair =>
              rcases pair with ⟨premium, required⟩
              obtain ⟨p', r', hs', he'⟩ := ih (cap - required) (by omega)
              have hregenerate : premium + swapPrice * (required - cap) +
                  (table swapPrice K rest)[cap - required] =
                    (premium + p') + swapPrice * (required + r' - cap) := by
                rw [he', ← sub_add_sub required r' cap, Nat.mul_add]
                omega
              by_cases hc : swapPrice * (retain - cap) + (table swapPrice K rest)[cap - retain] ≤
                  premium + swapPrice * (required - cap) + (table swapPrice K rest)[cap - required]
              · refine ⟨p, retain + r, .retain _ hs, ?_⟩
                simp only [table, List.foldr_cons, extend, Vector.getElem_ofFn]
                exact (Nat.min_eq_left hc).trans hretain
              · refine ⟨premium + p', required + r', .regenerate _ rfl hs', ?_⟩
                simp only [table, List.foldr_cons, extend, Vector.getElem_ofFn]
                exact (Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hc))).trans hregenerate

theorem bound_attained (swapPrice K : Nat) (choices : List Choice) :
    ∃ p r, Select choices p r ∧ bound swapPrice K choices = p + swapPrice * max K r := by
  obtain ⟨p, r, hs, he⟩ := table_attained swapPrice K choices K (by omega)
  refine ⟨p, r, hs, ?_⟩
  unfold bound
  rw [he]
  have hm : K + (r - K) = max K r := by omega
  rw [Nat.add_left_comm, ← Nat.mul_add, hm]

end Shuffler.Optimality.Capped
