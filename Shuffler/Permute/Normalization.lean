module

public import Shuffler.Permute.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Shuffler.Emission.Lemmas

@[expose] public section

namespace Shuffler.Permute

open Emission

theorem forIn_pure_yield {α β ε : Type} (xs : List α) (b : β) (f : β → α → β) :
    (forIn xs b (fun a b => pure (.yield (f b a))) : Except ε β) =
      .ok (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => simpa only [List.forIn_cons, except_ok_bind, pure_bind,
      List.foldl_cons] using ih (f b a)

def reassignGroup (stack : Stack) (slot : Value) (perm : Permutation stack) :
    Except ShuffleErr (ForInStep (Permutation stack)) := do
  let group := (List.finRange stack.length).filter (fun pos => stack[pos] = slot)
  if group.length < 2 then return .yield perm
  let desired := (group.map perm).mergeSort (· ≤ ·)
  let stayers := group.filter (· ∈ desired)
  let perm := stayers.foldl (fun p pos => p.setValue pos pos) perm
  let movers := group.filter (· ∉ desired)
  let vacant := desired.filter (· ∉ group)
  let ⟨hsz⟩ ← requires (movers.length = vacant.length) "movers and vacant must have the same size"
  return .yield ((List.finRange movers.length).foldl
    (fun p i => p.setValue movers[i] vacant[i]) perm)

def normalize (stack : Stack) (perm : Permutation stack) : Except ShuffleErr (Permutation stack) :=
  forIn stack.dedup perm (fun slot p => reassignGroup stack slot p)

theorem permute_eq_normalize (initial : State source target spills) (perm : Permutation initial.stack) :
    permute initial perm = do
      let remaining ← normalize initial.stack perm
      if hne : 0 < initial.stack.length then permute.go initial remaining hne
      else return ⟨none, initial⟩ := by
  simp only [permute, normalize, reassignGroup, forIn_pure_yield, except_ok_bind]

def Assigns {n : ℕ} (value expected : Fin n → Value) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, value i = expected (p i)

theorem Assigns.setValue {n : ℕ} {value expected : Fin n → Value}
    {p : Equiv.Perm (Fin n)} (h : Assigns value expected p) (a b : Fin n)
    (hab : value a = expected b) : Assigns value expected (p.setValue a b) := by
  intro i
  have hpre : value (p.symm b) = expected b := by simpa using h (p.symm b)
  by_cases ha : i = a
  · subst i; simpa using hab
  by_cases hb : i = p.symm b
  · subst i
    simpa [Equiv.setValue, Equiv.trans_apply, Equiv.swap_apply_right] using hpre.trans (hab.symm.trans (h a))
  · simpa [Equiv.setValue, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne ha hb] using h i

theorem setValue_preserves_fixed {n : ℕ} (p : Equiv.Perm (Fin n)) (a b : Fin n)
    (hab : a = b ∨ (p a ≠ a ∧ p b ≠ b)) :
    ∀ i, p i = i → (p.setValue a b) i = i := by
  intro i hi
  by_cases hia : i = a
  · subst i
    rcases hab with rfl | ⟨ha, _⟩
    · simp
    · exact (ha hi).elim
  have hib : i ≠ p.symm b := by
    intro he
    have hib : i = b := by simpa [hi] using congrArg p he
    rcases hab with rfl | ⟨_, hb⟩
    · exact hia hib
    · exact hb (hib ▸ hi)
  simpa [Equiv.setValue, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hia hib] using hi

theorem length_vacant {α : Type} [DecidableEq α] (group desired : List α)
    (hg : group.Nodup) (hd : desired.Nodup) (hlen : group.length = desired.length) :
    (group.filter (· ∉ desired)).length = (desired.filter (· ∉ group)).length := by
  have hg' := List.toFinset_card_of_nodup (hg.filter (fun x => decide (x ∉ desired)))
  have hd' := List.toFinset_card_of_nodup (hd.filter (fun x => decide (x ∉ group)))
  have hgs : (group.filter (fun x => decide (x ∉ desired))).toFinset =
      group.toFinset \ desired.toFinset := by ext; simp
  have hds : (desired.filter (fun x => decide (x ∉ group))).toFinset =
      desired.toFinset \ group.toFinset := by ext; simp
  rw [← hg', ← hd', hgs, hds, Finset.card_sdiff, Finset.card_sdiff,
    List.toFinset_card_of_nodup hg, List.toFinset_card_of_nodup hd, Finset.inter_comm, hlen]

theorem eq_of_mem_of_length_lt_two {α : Type} (xs : List α) (h : xs.length < 2)
    (a b : α) (ha : a ∈ xs) (hb : b ∈ xs) : a = b := by
  cases xs with
  | nil => simp at ha
  | cons x xs =>
    cases xs with
    | nil =>
      have hax : a = x := by simpa using ha
      have hbx : b = x := by simpa using hb
      exact hax.trans hbx.symm
    | cons y xs => simp at h

theorem reassignGroup_spec (stack : Stack) (slot : Value) (p : Permutation stack)
    (expected : Fin stack.length → Value) (hp : Assigns (fun i => stack[i]) expected p) :
    ∃ q, reassignGroup stack slot p = .ok (.yield q) ∧
      Assigns (fun i => stack[i]) expected q ∧
      (∀ i, p i = i → q i = i) ∧
      (∀ i, stack[i] = slot → stack[i] = expected i → q i = i) := by
  let group := (List.finRange stack.length).filter (fun pos => stack[pos] = slot)
  have hmem (i : Fin stack.length) : i ∈ group ↔ stack[i] = slot := by simp [group]
  let desired := (group.map p).mergeSort (· ≤ ·)
  have hdperm : desired.Perm (group.map p) := List.mergeSort_perm _ _
  have hdesired (i : Fin stack.length) : i ∈ desired ↔ expected i = slot := by
    rw [hdperm.mem_iff, List.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact (hp j).symm.trans ((hmem j).mp hj)
    · intro hi
      refine ⟨p.symm i, (hmem _).mpr ?_, p.apply_symm_apply i⟩
      simpa using (hp (p.symm i)).trans (by simpa using hi)
  by_cases hsmall : group.length < 2
  · refine ⟨p, ?_, hp, fun _ hi => hi, ?_⟩
    · simp only [reassignGroup, show (List.finRange stack.length).filter
        (fun pos => decide (stack[pos] = slot)) = group from rfl, hsmall, ↓reduceIte, pure, Except.pure]
    · intro i hi he
      have him := (hmem i).mpr hi
      have hjm := (hmem (p.symm i)).mpr (by
        simpa using (hp (p.symm i)).trans (by simpa using he.symm.trans hi))
      have heq : p.symm i = i := eq_of_mem_of_length_lt_two group hsmall _ _ hjm him
      simpa using (congrArg p heq).symm
  let stayers := group.filter (· ∈ desired)
  let movers := group.filter (· ∉ desired)
  let vacant := desired.filter (· ∉ group)
  have hg : group.Nodup := (List.nodup_finRange _).filter _
  have hd : desired.Nodup := hdperm.nodup_iff.mpr (hg.map p.injective)
  have hsz : movers.length = vacant.length := length_vacant group desired hg hd
    (by simp [desired])
  let fixed := stayers.foldl (fun q pos => q.setValue pos pos) p
  have hfixed : Assigns (fun i => stack[i]) expected fixed ∧
      (∀ i, p i = i → fixed i = i) ∧ (∀ i ∈ stayers, fixed i = i) := by
    have step (xs : List (Fin stack.length))
        (hxs : ∀ i ∈ xs, stack[i] = expected i) :
        ∀ q, Assigns (fun i => stack[i]) expected q →
          Assigns (fun i => stack[i]) expected (xs.foldl (fun q pos => q.setValue pos pos) q) ∧
          (∀ i, q i = i → (xs.foldl (fun q pos => q.setValue pos pos) q) i = i) ∧
          (∀ i ∈ xs, (xs.foldl (fun q pos => q.setValue pos pos) q) i = i) := by
      induction xs with
      | nil => intro q hq; exact ⟨hq, fun _ hi => hi, by simp⟩
      | cons a xs ih =>
        intro q hq
        obtain ⟨ha, hf, hx⟩ := ih (fun i hi => hxs i (by simp [hi])) _
          (hq.setValue a a (hxs a (by simp)))
        refine ⟨ha, fun i hi => hf i (setValue_preserves_fixed q a a (Or.inl rfl) i hi), ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hf _ (by simp)
        · exact hx i hi
    apply step stayers _ p hp
    intro i hi
    have hi' := List.mem_filter.mp hi
    exact ((hmem i).mp hi'.1).trans ((hdesired i).mp (by simpa using hi'.2)).symm
  have hmover (i : Fin movers.length) : stack[movers[i]] = slot ∧ expected movers[i] ≠ slot := by
    have hi := List.mem_filter.mp (List.getElem_mem i.isLt : movers[i] ∈ movers)
    exact ⟨(hmem _).mp hi.1, fun he => (of_decide_eq_true hi.2) ((hdesired _).mpr he)⟩
  have hvacant (i : Fin movers.length) : expected vacant[i] = slot ∧ stack[vacant[i]] ≠ slot := by
    have hi := List.mem_filter.mp (List.getElem_mem (hsz ▸ i.isLt) : vacant[i] ∈ vacant)
    exact ⟨(hdesired _).mp hi.1, fun he => (of_decide_eq_true hi.2) ((hmem _).mpr he)⟩
  let q := (List.finRange movers.length).foldl (fun q i => q.setValue movers[i] vacant[i]) fixed
  have hq : Assigns (fun i => stack[i]) expected q ∧ (∀ i, fixed i = i → q i = i) := by
    apply List.foldlRecOn (List.finRange movers.length)
      (fun q i => q.setValue movers[i] vacant[i]) (motive := fun q =>
        Assigns (fun i => stack[i]) expected q ∧ (∀ i, fixed i = i → q i = i))
    · exact ⟨hfixed.1, fun _ hi => hi⟩
    · intro r hr i _
      have ha : r movers[i] ≠ movers[i] := by
        intro he
        have hv := hr.1 movers[i]
        simp only [he] at hv
        exact (hmover i).2 (hv.symm.trans (hmover i).1)
      have hb : r vacant[i] ≠ vacant[i] := by
        intro he
        have hv := hr.1 vacant[i]
        simp only [he] at hv
        exact (hvacant i).2 (hv.trans (hvacant i).1)
      exact ⟨hr.1.setValue _ _ ((hmover i).1.trans (hvacant i).1.symm),
        fun j hj => setValue_preserves_fixed r _ _ (Or.inr ⟨ha, hb⟩) j (hr.2 j hj)⟩
  refine ⟨q, ?_, hq.1, fun i hi => hq.2 i (hfixed.2.1 i hi), ?_⟩
  · simp only [reassignGroup, show (List.finRange stack.length).filter
        (fun pos => decide (stack[pos] = slot)) = group from rfl, hsmall, ↓reduceIte]
    rw [requires_of_true _ hsz]
    rfl
  · intro i hi he
    apply hq.2 i
    apply hfixed.2.2 i
    simp only [stayers, List.mem_filter, decide_eq_true_eq]
    exact ⟨(hmem i).mpr hi, (hdesired i).mpr (he.symm.trans hi)⟩

theorem normalize_assigns (stack : Stack) (p : Permutation stack)
    (expected : Fin stack.length → Value) (hp : Assigns (fun i => stack[i]) expected p) :
    ∃ q, normalize stack p = .ok q ∧ Assigns (fun i => stack[i]) expected q ∧
      (∀ i, p i = i → q i = i) ∧ (∀ i, stack[i] = expected i → q i = i) := by
  have run (slots : List Value) : ∀ p : Permutation stack,
      Assigns (fun i => stack[i]) expected p →
      ∃ q, forIn slots p (fun slot p => reassignGroup stack slot p) = .ok q ∧
        Assigns (fun i => stack[i]) expected q ∧ (∀ i, p i = i → q i = i) ∧
        (∀ i, stack[i] ∈ slots → stack[i] = expected i → q i = i) := by
    induction slots with
    | nil => intro p hp; exact ⟨p, rfl, hp, fun _ hi => hi, by simp⟩
    | cons slot slots ih =>
      intro p hp
      obtain ⟨r, hr, hra, hrf, hrc⟩ := reassignGroup_spec stack slot p expected hp
      obtain ⟨q, hq, hqa, hqf, hqc⟩ := ih r hra
      refine ⟨q, ?_, hqa, fun i hi => hqf i (hrf i hi), ?_⟩
      · simpa only [List.forIn_cons, hr, except_ok_bind] using hq
      · intro i hi he
        rcases List.mem_cons.mp hi with hi | hi
        · exact hqf i (hrc i hi he)
        · exact hqc i hi he
  obtain ⟨q, hq, hqa, hqf, hqc⟩ := run stack.dedup p hp
  exact ⟨q, hq, hqa, hqf, fun i he =>
    hqc i (List.mem_dedup.mpr (List.getElem_mem i.isLt)) he⟩

theorem all_swaps_reachable.values {stack : Stack} {p : Permutation stack}
    (h : all_swaps_reachable p) : values_reachable p := by
  intro i hne
  apply h i
  apply Equiv.Perm.mem_support.mpr
  intro hfix
  apply hne
  have hi : p.symm i = i := by
    apply p.injective
    simpa using hfix.symm
  simp only [hi]

theorem normalize_spec (stack : Stack) (p : Permutation stack) :
    ∃ q, normalize stack p = .ok q ∧
      apply_permutation stack q = apply_permutation stack p ∧
      q.support ⊆ p.support ∧ (all_swaps_reachable q ↔ values_reachable p) := by
  obtain ⟨q, hq, ha, hf, hc⟩ := normalize_assigns stack p
    (fun i => stack[p.symm i]) (by intro i; simp)
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · apply congrArg List.ofFn
    funext i
    simpa using ha (q.symm i)
  · intro i hi
    by_contra hn
    exact (Equiv.Perm.mem_support.mp hi) (hf i (Equiv.Perm.notMem_support.mp hn))
  · constructor
    · intro hr i hne
      apply hr i
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      exact hne (by simpa [hfix] using ha i)
    · intro hr i hi
      apply hr i
      intro he
      exact (Equiv.Perm.mem_support.mp hi) (hc i he)

theorem normalize_of_nodup (stack : Stack) (p : Permutation stack) (hn : stack.Nodup) :
    normalize stack p = .ok p := by
  obtain ⟨q, hq, ha, _, _⟩ := normalize_assigns stack p
    (fun i => stack[p.symm i]) (by intro i; simp)
  have hsymm : q.symm = p.symm := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    exact hn.getElem_inj_iff.mp (by simpa using ha (q.symm i))
  have he : q = p := by simpa using congrArg Equiv.symm hsymm
  simpa [he] using hq

theorem values_reachable_congr {stack : Stack} (p q : Permutation stack)
    (he : apply_permutation stack p = apply_permutation stack q) :
    values_reachable p ↔ values_reachable q := by
  have hv (i : Fin stack.length) : stack[p.symm i] = stack[q.symm i] := by
    simpa [apply_permutation] using congrArg (fun xs => xs[i.val]?) he
  simp only [values_reachable, hv]

theorem values_reachable_iff_deep (stack : Stack) (p : Permutation stack) :
    values_reachable p ↔ ∀ i, i < stack.length - (MAX_SWAP_DEPTH + 1) →
      stack[i]? = (apply_permutation stack p)[i]? := by
  constructor
  · intro hr i hi
    have hin : i < stack.length := by omega
    have he : stack[i] = stack[p.symm ⟨i, hin⟩] := by
      by_contra hne
      have hd := hr ⟨i, hin⟩ hne
      dsimp [Fin.rev] at hd
      omega
    simpa [apply_permutation, hin] using he
  · intro hr i hne
    by_contra hd
    have hi : i.val < stack.length - (MAX_SWAP_DEPTH + 1) := by
      dsimp [Fin.rev] at hd
      omega
    apply hne
    simpa [apply_permutation, i.isLt] using hr i.val hi

end Shuffler.Permute
