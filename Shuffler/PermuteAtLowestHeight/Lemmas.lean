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

theorem setValue_apply_of_ne {n : ℕ} (f : Equiv.Perm (Fin n)) (a b x : Fin n)
    (hx : x ≠ a) (hfx : f x ≠ b) : f.setValue a b x = f x := by
  have hb : x ≠ f.symm b := fun he => hfx (by rw [he]; simp)
  simp [Equiv.setValue, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hx hb]

-- Every slot in `done` whose destination is below the current height is sent there by `perm`.
def Settled (state : State source target spills) (htotal : ∀ i, (state.mapping.destinationOf i).isSome)
    (done : List (Fin state.stack.length)) (perm : Shuffler.Permute.Permutation state.stack) : Prop :=
  ∀ i ∈ done, ((state.mapping.destinationOf i).get (htotal i)).val < state.stack.length →
    (perm i).val = ((state.mapping.destinationOf i).get (htotal i)).val

theorem Settled.keep {state : State source target spills} {htotal} {done perm}
    (hset : Settled state htotal done perm) (pos : Fin state.stack.length)
    (hp : state.stack.length ≤ ((state.mapping.destinationOf pos).get (htotal pos)).val) :
    Settled state htotal (done ++ [pos]) perm := by
  intro i hi hd
  rcases List.mem_append.mp hi with hi | hi
  · exact hset i hi hd
  · obtain rfl : i = pos := by simpa using hi
    omega

-- Setting `a ↦ b` keeps every settled slot when no other settled slot is sent to `b`.
theorem Settled.setValue {state : State source target spills} {htotal} {done perm}
    (hset : Settled state htotal done perm) (a b : Fin state.stack.length)
    (hfresh : ∀ i, i ≠ a → ((state.mapping.destinationOf i).get (htotal i)).val < state.stack.length →
      ((state.mapping.destinationOf i).get (htotal i)).val ≠ b.val)
    (ha : ((state.mapping.destinationOf a).get (htotal a)).val < state.stack.length →
      b.val = ((state.mapping.destinationOf a).get (htotal a)).val)
    (done' : List (Fin state.stack.length)) (hdone : ∀ i ∈ done', i ∈ done ∨ i = a) :
    Settled state htotal done' (perm.setValue a b) := by
  intro i hi hd
  by_cases hia : i = a
  · subst i
    simpa using ha hd
  have hi := (hdone i hi).resolve_right hia
  rw [setValue_apply_of_ne perm a b i hia fun he => hfresh i hia hd (by rw [← hset i hi hd, he])]
  exact hset i hi hd

theorem forIn_filters {α β : Type} (xs : List α) (p q : α → Bool) (inv : List α → β → Prop)
    (f : α → β × List α × List α → Except ShuffleErr (ForInStep (β × List α × List α)))
    (step : ∀ done a b, inv done b.1 → ∃ v, f a b = .ok (.yield
      (v, b.2.1 ++ (if p a then [a] else []), b.2.2 ++ (if q a then [a] else []))) ∧
      inv (done ++ [a]) v)
    (done : List α) (init : β × List α × List α) (hinit : inv done init.1) :
    Succeeds (forIn xs init f) fun result => inv (done ++ xs) result.1 ∧
      result.2.1 = init.2.1 ++ xs.filter p ∧ result.2.2 = init.2.2 ++ xs.filter q := by
  induction xs generalizing done init with
  | nil => exact ⟨by simpa using hinit, by simp, by simp⟩
  | cons a xs ih =>
    obtain ⟨v, hv, hinv⟩ := step done a init hinit
    rw [List.forIn_cons, hv, except_ok_bind]
    refine (ih (done ++ [a]) (v, init.2.1 ++ (if p a then [a] else []),
      init.2.2 ++ (if q a then [a] else [])) hinv).mono fun result ⟨hr, h1, h2⟩ => ?_
    refine ⟨by simpa using hr, ?_⟩
    cases hp : p a <;> cases hq : q a <;>
      simpa [List.filter_cons, List.append_assoc, hp, hq] using And.intro h1 h2

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
  have hbound (i : Fin state.stack.length) : state.mapping i = some (dest i) :=
    (Option.some_get (htotal i)).symm
  have hinj (a b : Fin state.stack.length) (he : (dest a).val = (dest b).val) : a = b := by
    apply Option.some.inj
    rw [← state.mapping.eq_some_iff.mpr (hbound a), ← state.mapping.eq_some_iff.mpr (hbound b),
      Fin.ext he]
  -- a hole is not the destination of any slot
  have hfree (x h : Fin state.stack.length) (hh : hole h) : (dest x).val ≠ h.val := by
    intro he
    have hs := state.mapping.eq_some_iff.mpr (hbound x)
    rw [show dest x = Fin.castLE hlen h from Fin.ext he] at hs
    have hd := hdom (Fin.castLE hlen h)
    rw [hs, hh] at hd
    cases hd
  suffices hs : Succeeds (permuteAtLowestHeight state) (fun result =>
      result.state.stack.length = state.stack.length ∧
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue ∧
      ∀ b, result.blocked = some b → 0 < b.excess) from hs.exists
  unfold permuteAtLowestHeight
  refine Succeeds.bind (pre := fun result =>
    Settled state htotal (List.finRange state.stack.length) result.1 ∧
    result.2.1 = (List.finRange state.stack.length).filter p ∧
    result.2.2 = (List.finRange state.stack.length).filter q) ?_ ?_
  · refine (forIn_filters (List.finRange state.stack.length) p q (Settled state htotal) _ ?_
      [] (1, ∅, ∅) (by simp [Settled])).mono ?_
    · intro done pos acc hset
      have hi : index target.length pos.val = .ok (Fin.castLE hlen pos) :=
        index_eq (Fin.castLE hlen pos)
      simp only [requires_of_true _ (htotal pos), except_ok_bind,
        hi, Mapping.positionOf,
        Option.isSome_iff_ne_none, not_not]
      by_cases hp : state.stack.length ≤ (dest pos).val
      · by_cases hh : hole pos
        · simp only [dest, hole] at hp hh
          simp [p, q, dest, hole, hp, hh, Nat.not_lt.mpr hp, pure, Except.pure]
          exact hset.setValue pos pos (fun i _ _ => hfree i pos hh) (fun hd => absurd hd (by omega))
            _ (by simp)
        · simp only [dest, hole] at hp hh
          simp [p, q, dest, hole, hp, hh, Nat.not_lt.mpr hp, pure, Except.pure]
          exact hset.keep pos hp
      · have hd : (dest pos).val < state.stack.length := by omega
        have hi' : index state.stack.length (dest pos).val = .ok ⟨(dest pos).val, hd⟩ :=
          index_eq (⟨(dest pos).val, hd⟩ : Fin state.stack.length)
        by_cases hh : hole pos <;>
          simp only [dest, hole] at hp hh hi' hd <;>
          simp [p, q, dest, hole, hp, hh, hi', hd, pure, Except.pure, except_ok_bind] <;>
          exact hset.setValue pos _ (fun i hip _ he => hip (hinj i pos he)) (fun _ => rfl) _ (by simp)
    · intro result hr
      simpa using hr
  · intro scan ⟨hset, hholes, hparked⟩
    have hsz : scan.2.2.length = scan.2.1.length := by
      rw [hholes, hparked]
      exact parked_holes_size state htotal hdom
    simp only [requires_of_true _ hsz, except_ok_bind]
    refine Succeeds.bind (pre := Settled state htotal (List.finRange state.stack.length)) ?_ ?_
    · have hhole : ∀ x ∈ scan.2.1, hole x := by
        rw [hholes]
        exact fun x hx => (of_decide_eq_true (List.mem_filter.mp hx).2).2
      have hpark : ∀ x ∈ scan.2.2, state.stack.length ≤ (dest x).val := by
        rw [hparked]
        exact fun x hx => (of_decide_eq_true (List.mem_filter.mp hx).2).1
      refine Succeeds.forIn _ _ _ _ hset ?_
      intro k perm hperm
      refine Settled.setValue hperm _ _ ?_ ?_ _ (fun i h => Or.inl h)
      · exact fun i _ _ => hfree i _ (hhole _ (List.getElem_mem _))
      · exact fun hd => absurd hd (Nat.not_lt.mpr (hpark _ (List.mem_mergeSort.mp (List.getElem_mem _))))
    · intro permutation hperm
      have hagree : Shuffler.Permute.bindings_agree state permutation := by
        intro i d hd hb
        have hdi : dest i = d := Option.some.inj ((hbound i).symm.trans hb)
        have hpi := hperm i (List.mem_finRange i) (by simpa [dest, hdi] using hd)
        have hsymm : permutation.symm ⟨d.val, hd⟩ = i :=
          (Equiv.symm_apply_eq _).mpr (Fin.ext (by simpa [dest, hdi] using hpi.symm))
        simp only [hsymm]
      obtain ⟨result, hr, hs⟩ := Shuffler.Permute.permute_result_spec state permutation hagree
      rw [hr]
      exact hs

end Shuffler.PermuteAtLowestHeight
