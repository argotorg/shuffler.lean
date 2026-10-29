module

public import Shuffler.PermuteAtLowestHeight.Defs
public import Shuffler.Emission.Run.Lemmas.Permute
public import Shuffler.BuildMapping.Lemmas.Basic

@[expose] public section

namespace Shuffler.PermuteAtLowestHeight

open Emission BuildMapping

variable {source target : Stack} {spills : SpillSet}

theorem filter_balance {α : Type} (xs : List α) (p q : α → Bool)
    (h : (xs.filter p).length = (xs.filter q).length) :
    (xs.filter (fun x => p x && !q x)).length =
      (xs.filter (fun x => !p x && q x)).length := by
  have hp := (xs.filter p).length_eq_length_filter_add q
  have hq := (xs.filter q).length_eq_length_filter_add p
  simp only [List.filter_filter] at hp hq
  have he : (xs.filter (fun x => p x && q x)).length =
      (xs.filter (fun x => q x && p x)).length := by simp [Bool.and_comm]
  simp only [Bool.and_comm] at hp hq ⊢
  omega

theorem parked_holes_size (state : State source target spills)
    (htotal : ∀ i, (state.mapping.destinationOf i).isSome)
    (hdom : ∀ j, (state.mapping.symm j).isSome = (state.planned_mapping.symm j).isSome) :
    let hlen : state.stack.length ≤ target.length := by
      have := Mapping.total_size state.mapping htotal; omega
    let dest := fun i => (state.mapping.destinationOf i).get (htotal i)
    let hole := fun i : Fin state.stack.length =>
      state.planned_mapping.symm (Fin.castLE hlen i) = none
    ((List.finRange state.stack.length).filter
      (fun i => decide (state.stack.length ≤ (dest i).val ∧ ¬hole i))).length =
    ((List.finRange state.stack.length).filter
      (fun i => decide (¬state.stack.length ≤ (dest i).val ∧ hole i))).length := by
  let hlen : state.stack.length ≤ target.length := by
    have := Mapping.total_size state.mapping htotal; omega
  let dest := fun i => (state.mapping.destinationOf i).get (htotal i)
  let hole := fun i : Fin state.stack.length =>
    state.planned_mapping.symm (Fin.castLE hlen i) = none
  have hc : (Finset.univ.filter (fun i : Fin state.stack.length => (dest i).val < state.stack.length)).card =
      (Finset.univ.filter fun i : Fin state.stack.length => ¬hole i).card := by
    apply Finset.card_bij (fun i hi => (⟨(dest i).val, (Finset.mem_filter.mp hi).2⟩ : Fin state.stack.length))
    · intro i hi
      have hb : state.mapping i = some (dest i) := (Option.some_get (htotal i)).symm
      have hd := hdom (dest i)
      rw [state.mapping.eq_some_iff.mpr hb] at hd
      simpa [hole, ← Option.isSome_iff_ne_none] using hd.symm
    · intro a ha b hb he
      have hv : dest a = dest b := Fin.ext (congrArg (fun x : Fin state.stack.length => x.val) he)
      have ha' := state.mapping.eq_some_iff.mpr (Option.some_get (htotal a)).symm
      have hb' := state.mapping.eq_some_iff.mpr (Option.some_get (htotal b)).symm
      change state.mapping.symm (dest a) = some a at ha'
      change state.mapping.symm (dest b) = some b at hb'
      rw [hv] at ha'
      apply Option.some.inj
      exact ha'.symm.trans hb'
    · intro i hi
      have hd : (state.planned_mapping.symm (Fin.castLE hlen i)).isSome := by
        simpa [hole, Option.isSome_iff_ne_none] using (Finset.mem_filter.mp hi).2
      have hs : (state.mapping.symm (Fin.castLE hlen i)).isSome := by rw [hdom]; exact hd
      let s := (state.mapping.symm (Fin.castLE hlen i)).get hs
      have hb : state.mapping s = some (Fin.castLE hlen i) :=
        state.mapping.eq_some_iff.mp (Option.some_get hs).symm
      have hv : dest s = Fin.castLE hlen i := by
        exact Option.some.inj ((Option.some_get (htotal s)).trans hb)
      refine ⟨s, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv]; exact i.isLt, ?_⟩
      exact Fin.ext (congrArg (fun x : Fin target.length => x.val) hv)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin state.stack.length)))
    (fun i => (dest i).val < state.stack.length)
  have hh := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin state.stack.length))) hole
  have he : (Finset.univ.filter (fun i : Fin state.stack.length => state.stack.length ≤ (dest i).val)).card =
      (Finset.univ.filter hole).card := by
    simp only [not_lt] at hpart
    omega
  have hlist (p : Fin state.stack.length → Bool) :
      ((List.finRange state.stack.length).filter p).length =
        (Finset.univ.filter fun i => p i).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
    simp
  apply filter_balance _ (fun i => decide (state.stack.length ≤ (dest i).val)) (fun i => decide (hole i))
  simpa only [hlist, decide_eq_true_eq] using he

theorem forIn_filters {α β : Type} (xs : List α) (p q : α → Bool)
    (f : α → β × List α × List α → Except ShuffleErr (ForInStep (β × List α × List α)))
    (step : ∀ a b, ∃ v, f a b = .ok (.yield
      (v, b.2.1 ++ (if p a then [a] else []), b.2.2 ++ (if q a then [a] else []))))
    (init : β × List α × List α) :
    Succeeds (forIn xs init f) fun result =>
      result.2.1 = init.2.1 ++ xs.filter p ∧ result.2.2 = init.2.2 ++ xs.filter q := by
  induction xs generalizing init with
  | nil => exact ⟨by simp, by simp⟩
  | cons a xs ih =>
    obtain ⟨v, hv⟩ := step a init
    rw [List.forIn_cons, hv, except_ok_bind]
    refine (ih (v, init.2.1 ++ (if p a then [a] else []),
      init.2.2 ++ (if q a then [a] else []))).mono fun result hr => ?_
    cases hp : p a <;> cases hq : q a <;>
      simpa [List.filter_cons, List.append_assoc, hp, hq] using hr

theorem permuteAtLowestHeight_result_spec (state : State source target spills)
    (htotal : ∀ i, (state.mapping.destinationOf i).isSome)
    (hdom : ∀ j, (state.mapping.symm j).isSome = (state.planned_mapping.symm j).isSome) :
    ∃ result, permuteAtLowestHeight state = .ok result ∧
      result.state.stack.length = state.stack.length ∧
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue ∧
      ∀ b, result.blocked = some b → 0 < b.excess := by
  let hlen : state.stack.length ≤ target.length := by
    have := Mapping.total_size state.mapping htotal; omega
  let dest := fun i => (state.mapping.destinationOf i).get (htotal i)
  let hole := fun i : Fin state.stack.length =>
    state.planned_mapping.symm (Fin.castLE hlen i) = none
  let p := fun i => decide (¬state.stack.length ≤ (dest i).val ∧ hole i)
  let q := fun i => decide (state.stack.length ≤ (dest i).val ∧ ¬hole i)
  suffices hs : Succeeds (permuteAtLowestHeight state) (fun result =>
      result.state.stack.length = state.stack.length ∧
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue ∧
      ∀ b, result.blocked = some b → 0 < b.excess) from hs.exists
  unfold permuteAtLowestHeight
  refine Succeeds.bind (pre := fun result =>
    result.2.1 = (List.finRange state.stack.length).filter p ∧
    result.2.2 = (List.finRange state.stack.length).filter q) ?_ ?_
  · refine (forIn_filters (List.finRange state.stack.length) p q _ ?_ (1, ∅, ∅)).mono ?_
    · intro pos acc
      have hi : index target.length pos.val = .ok (Fin.castLE hlen pos) :=
        index_eq (Fin.castLE hlen pos)
      simp only [requires_of_true _ (htotal pos), except_ok_bind,
        hi, Mapping.positionOf,
        Option.isSome_iff_ne_none, not_not]
      by_cases hp : state.stack.length ≤ (dest pos).val
      · by_cases hh : hole pos <;>
          simp only [dest, hole] at hp hh <;>
          simp [p, q, dest, hole, hp, hh, Nat.not_lt.mpr hp, pure, Except.pure]
      · have hd : (dest pos).val < state.stack.length := by omega
        have hi' : index state.stack.length (dest pos).val = .ok ⟨(dest pos).val, hd⟩ :=
          index_eq (⟨(dest pos).val, hd⟩ : Fin state.stack.length)
        by_cases hh : hole pos <;>
          simp only [dest, hole] at hp hh hi' hd <;>
          simp [p, q, dest, hole, hp, hh, hi', hd, pure, Except.pure, except_ok_bind]
    · intro result hr
      exact hr
  · intro scan hscan
    have hsz : scan.2.2.length = scan.2.1.length := by
      rw [hscan.1, hscan.2]
      exact parked_holes_size state htotal hdom
    simp only [requires_of_true _ hsz, except_ok_bind]
    refine Succeeds.bind (pre := fun _ => True) ?_ ?_
    · exact Succeeds.forIn _ _ _ _ trivial (fun _ _ _ => trivial)
    · intro permutation _
      obtain ⟨result, hr, hs⟩ := Shuffler.Permute.permute_result_spec state permutation
      rw [hr]
      exact hs

end Shuffler.PermuteAtLowestHeight
