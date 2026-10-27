import Shuffler.BuildBottomUp.Optimality.Lemmas.TightLowerBound
import Shuffler.BuildBottomUp.Optimality.Lemmas.SharpBound

/-! Attained window bound. `buildBottomUp_sharp_bound` gives at most
U = 2 (min n 17 - 1) + 2k - 2 new swaps for n ≥ 3 source slots and k ≥ 1 pending
generations. For 3 ≤ n ≤ 17 BBU attains U when k ≤ 2, when k = 3 and n ≥ 4, when n ≥ 16,
and when n = 15 and k mod 16 is not 2 or 3.

Families C (k ≤ 2) and D (k = 3, n ≤ 15) are all-spilled: target j holds the spilled
variable j and the source holds distinct values. No target is urgent and every target can
be loaded. Family C runs a conveyor: at cursor t the slot n - 2 holds target t and the
top holds target t + 1, so each cursor costs 2 swaps. Family D generates target n at the
top first and then runs the conveyor of C on n + 1 slots. For n ≥ 15 and k ≥ 3 (k ≥ 4 for
n = 15) family W of `TightLowerBound` attains U. -/

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

set_option maxHeartbeats 2000000

/-! All-spilled states. Source slot i holds target `lab i`; `inv` inverts `lab`. -/

def allTarget (N : Nat) : Stack := List.ofFn fun j : Fin N => .Var ⟨j.val⟩

def allSpills (N : Nat) : SpillSet := (Finset.range N).image VarId.mk

def allSource (n : Nat) (lab : Nat → Nat) : Stack := List.ofFn fun i : Fin n => .Var ⟨lab i.val⟩

@[simp] theorem allTarget_length : (allTarget N).length = N := by simp [allTarget]

@[simp] theorem allSource_length : (allSource n lab).length = n := by simp [allSource]

theorem allTarget_getElem? (j : Nat) :
    (allTarget N)[j]? = if j < N then some (.Var ⟨j⟩) else none := by
  simp only [allTarget, List.getElem?_ofFn]
  split_ifs <;> rfl
@[simp] theorem allTarget_getElem (j : Nat) (h : j < (allTarget N).length) :
    (allTarget N)[j] = .Var ⟨j⟩ := by
  simp [allTarget]

theorem all_allSpilled (N : Nat) : AllSpilled (allTarget N) (allSpills N) := by
  intro j
  have : j.val < N := by simpa using j.isLt
  rw [Fin.getElem_fin, allTarget_getElem]
  simp [SpillSet.is_spilled, allSpills, this]

theorem all_ne (ha : a < N) (h : a ≠ b) : (allTarget N)[a]? ≠ (allTarget N)[b]? := by
  rw [allTarget_getElem?, allTarget_getElem?]
  split_ifs <;> simp_all

-- Slot i binds to target lab i when inv inverts lab there. The mapping is a partial
-- bijection for all lab and inv.
def allMapping (n N : Nat) (lab inv : Nat → Nat) :
    Mapping (allSource n lab).length (allTarget N).length where
  toFun i := if h : lab i.val < N ∧ inv (lab i.val) = i.val then
    some ⟨lab i.val, by simpa using h.1⟩ else none
  invFun j := if h : inv j.val < n ∧ lab (inv j.val) = j.val then
    some ⟨inv j.val, by simpa using h.1⟩ else none
  inv i j := by
    have hi : i.val < n := by simpa using i.isLt
    have hj : j.val < N := by simpa using j.isLt
    show _ = some _ ↔ _ = some _
    by_cases hij : lab i.val = j.val ∧ inv j.val = i.val
    · obtain ⟨h1, h2⟩ := hij
      simp [h1, h2, hi, hj]
    · constructor
      · intro he
        split_ifs at he with h
        simp only [Option.some.injEq, Fin.ext_iff] at he
        exact absurd ⟨by rw [← he]; exact h.2, he⟩ hij
      · intro he
        split_ifs at he with h
        simp only [Option.some.injEq, Fin.ext_iff] at he
        exact absurd ⟨he, by rw [← he]; exact h.2⟩ hij

def allState (n N : Nat) (lab inv : Nat → Nat) :
    State (allSource n lab) (allTarget N) (allSpills N) where
  planned_mapping := allMapping n N lab inv
  stack := allSource n lab
  trace := .Lit (allSource n lab)
  mapping := allMapping n N lab inv
  pending_generations := N - n

-- The n labels are below N and inv inverts them.
structure Labels (n N : Nat) (lab inv : Nat → Nat) : Prop where
  lt : ∀ i < n, lab i < N
  left : ∀ i < n, inv (lab i) = i

theorem allMapping_symm (j : Fin (allTarget N).length) :
    ((allMapping n N lab inv).symm j).map Fin.val =
      if inv j.val < n ∧ lab (inv j.val) = j.val then some (inv j.val) else none := by
  change Option.map Fin.val (if h : _ then some _ else none) = _
  split_ifs <;> rfl

theorem all_unbound (h : Labels n N lab inv) (j : Fin (allTarget N).length) :
    (allState n N lab inv).mapping.symm j = none ↔ ∀ i < n, lab i ≠ j.val := by
  have hs := allMapping_symm (n := n) (lab := lab) (inv := inv) j
  rw [← Option.map_eq_none_iff (f := Fin.val)]
  change Option.map Fin.val ((allMapping n N lab inv).symm j) = none ↔ _
  rw [hs]
  constructor
  · intro hn i hi he
    rw [← he, h.left i hi] at hn
    simp [hi] at hn
  · intro hne
    rw [ite_eq_right_iff.mpr fun hc => (hne _ hc.1 hc.2).elim]

theorem all_placed (h : Labels n N lab inv) (hle : n ≤ N) :
    Placed n lab (allState n N lab inv) where
  length := allSource_length
  value i hi := by
    have := h.lt i hi
    simp only [allState, allSource, List.getElem?_ofFn, hi, ↓reduceDIte, allTarget_getElem?,
      this, ↓reduceIte]
  slot i hi := by
    have hlt : lab i < (allTarget N).length := by simpa using h.lt i hi
    have hs := allMapping_symm (n := n) (lab := lab) (inv := inv) ⟨_, hlt⟩
    simp only [h.left i hi, hi, true_and, ↓reduceIte] at hs
    simp only [State.positionOfNat, State.positionOf, hlt, ↓reduceDIte]
    exact hs
  expected := by
    apply List.ext_getElem (by simp [State.expectedStack])
    intro j _ hj
    simp only [State.expectedStack, List.getElem_ofFn]
    split
    · rename_i pos hpos
      have hs := allMapping_symm (n := n) (lab := lab) (inv := inv) ⟨j, hj⟩
      change (allMapping n N lab inv).symm _ = some pos at hpos
      rw [hpos] at hs
      replace hs : some pos.val = if inv j < n ∧ lab (inv j) = j then some (inv j) else none := hs
      split_ifs at hs with hc
      · simp only [Option.some.injEq] at hs
        change (allSource n lab)[pos.val] = _
        simp only [allSource, List.getElem_ofFn, allTarget, hs, hc.2]
    · rfl
  pending := by simp [allState]
  le := by simpa using hle

theorem all_valid (h : Labels n N lab inv) (hle : n ≤ N) : (allState n N lab inv).Valid where
  size := by simp [allState]; omega
  pending := by
    unfold Mapping.unmapped_target_slots
    rw [Finset.filter_congr fun j _ => all_unbound h j]
    simp only [allState]
    have hbound : (Finset.univ.filter fun j : Fin (allTarget N).length =>
        ¬ ∀ i < n, lab i ≠ j.val) = Finset.univ.image fun i : Fin n =>
          (⟨lab i.val, by simpa using h.lt i.val i.isLt⟩ : Fin (allTarget N).length) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_forall,
        not_not, Fin.ext_iff]
      exact ⟨fun ⟨i, hi, he⟩ => ⟨⟨i, hi⟩, he⟩, fun ⟨i, he⟩ => ⟨i.val, i.isLt, he⟩⟩
    have hinj : Function.Injective fun i : Fin n =>
        (⟨lab i.val, by simpa using h.lt i.val i.isLt⟩ : Fin (allTarget N).length) := by
      intro a b he
      have := congrArg (inv ∘ Fin.val) he
      simp only [Function.comp, h.left a.val a.isLt, h.left b.val b.isLt] at this
      exact Fin.ext this
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : Fin (allTarget N).length => ¬ ∀ i < n, lab i ≠ j.val)
    simp only [hbound, Finset.card_image_of_injective _ hinj, not_not, Finset.card_univ,
      Fintype.card_fin, allTarget_length] at this
    omega
  available := (all_allSpilled N).available _

theorem allState_swapCount : (allState n N lab inv).trace.swapCount = 0 := by
  simp [allState, Trace.swapCount]

/-! The conveyor on L slots. At cursor t ≤ L - 2 slot i < t is final, slot L - 2 holds
target t and the top holds target t + 1. Targets L and L - 1 sit in slots L - 3 and L - 4,
and slot i holds target i + 2 otherwise. -/

def cLab (L t i : Nat) : Nat :=
  if i < t then i
  else if i = L - 1 then (if t + 4 ≤ L then t + 1 else if t + 3 = L then L - 1 else L)
  else if i = L - 2 then (if t + 2 < L then t else L - 1)
  else if i = L - 3 then L else if i = L - 4 then L - 1 else i + 2

theorem AllSpilled.not_urgent (h : AllSpilled target spills) {state : State source target spills} :
    ¬ Urgent t state o := fun ⟨ho, _, _, hns, _⟩ => hns (h ⟨o, ho⟩)

section conveyor

variable {N L : Nat} {source : Stack} {spills : SpillSet}
  {state : State source (allTarget N) spills}
  {post : ((res : Stack) × Trace spills source res) → Prop}

-- Distinct values: no open slot other than c holds the value of target t.
theorem all_unique (hp : Placed len lab state) (hc : c < len) (hlab : lab c = t) :
    ∀ s < len, s ≠ c → lab s ≠ s → (allTarget N)[lab s]? ≠ (allTarget N)[t]? :=
  fun s hs hsc _ => all_ne (by simpa using hp.range s hs)
    fun he => hsc (hp.inj s hs c hc (he.trans hlab.symm))

-- At cursor t with t + 3 ≤ L, slot L - 2 holds target t and the step costs 2 swaps.
theorem conv_step (hsp : AllSpilled (allTarget N) spills) (hL : L ≤ 17) (hLN : L < N)
    (ht : t + 3 ≤ L) (hp : Placed L (cLab L t) state)
    (cont : ∀ next : State source (allTarget N) spills, Placed L (cLab L (t + 1)) next →
      next.trace.swapCount = state.trace.swapCount + 2 →
      Succeeds (buildBottomUp.loop (t + 1) next) post) :
    Succeeds (buildBottomUp.loop t state) post := by
  have htop : state.positionOfNat L ≠ none := by
    have hs := hp.slot (L - 3) (by omega)
    rw [show cLab L t (L - 3) = L by unfold cLab; split_ifs <;> omega] at hs
    simp [hs]
  refine hp.bound_step t state (hsp.reachable _) (Or.inr ⟨fun _ => hsp.not_urgent,
    fun _ => htop⟩) (L - 2) (by omega) (by unfold cLab; split_ifs <;> omega) (by omega)
    (by omega) (by rw [hp.pending]; simp; omega) (by unfold cLab; split_ifs <;> omega)
    (all_unique hp (by omega) (by unfold cLab; split_ifs <;> omega)) fun next hb hc => ?_
  refine cont next ((hp.boundSwaps hb).congr fun i hi => ?_) (by rw [hc]; simp; omega)
  simp only [boundLab, cLab, swapIdx]
  split_ifs <;> omega

-- At cursor L - 2 the loop fills the hole at L - 2. Then it permutes the top pair at
-- once (N = L + 1, 1 swap) or after it generates target L + 1 (N = L + 2, 3 swaps).
theorem conv_end (hsp : AllSpilled (allTarget N) spills) (h3 : 3 ≤ L) (hL : L ≤ 17)
    (hN : N = L + 1 ∨ N = L + 2) (hp : Placed L (cLab L (L - 2)) state) :
    Succeeds (buildBottomUp.loop (L - 2) state) (fun r => r.2.swapCount =
      state.trace.swapCount + if N = L + 1 then 2 else 4) := by
  have hl := hp.length
  have htop : state.positionOfNat L ≠ none := by
    have hs := hp.slot (L - 1) (by omega)
    rw [show cLab L (L - 2) (L - 1) = L by unfold cLab; split_ifs <;> omega] at hs
    simp [hs]
  have hNt : L - 2 < (allTarget N).length := by simp; omega
  have hfree : state.positionOfNat (L - 2) = none :=
    (hp.positionOf_none _).mpr fun i hi => by unfold cLab; split_ifs <;> omega
  refine hp.hole_step (L - 2) state (hsp.reachable _)
    (Or.inr ⟨fun _ => hsp.not_urgent, fun _ => htop⟩) (by omega) (by omega)
    (by simp; omega) hfree (hsp.available _ _)
    (all_ne (by unfold cLab; split_ifs <;> omega) (by unfold cLab; split_ifs <;> omega))
    fun s1 hp1 hc1 => ?_
  have hlab1 : ∀ i < L + 1, (fun i => if i = L - 2 then L - 2 else
      if i = L then cLab L (L - 2) (L - 2) else cLab L (L - 2) i) i =
      if L - 2 + 1 ≤ i ∧ i < L - 2 + 1 + 1 then i + 1 else if i = L - 2 + 1 + 1 then L - 2 + 1
      else i := fun i hi => by
    simp only [cLab]
    split_ifs <;> omega
  rcases hN with rfl | rfl
  · apply (hp1.permute_step (L - 2 + 1) s1 (by simp) 1 le_rfl (by omega) (by omega)
      hlab1).mono
    intro r hr
    rw [hr, hc1]
    split_ifs <;> omega
  · have hl1 := hp1.length
    have hNd : L + 1 < (allTarget (L + 2)).length := by simp
    have hfree1 : s1.positionOfNat (L + 1) = none :=
      (hp1.positionOf_none _).mpr fun i hi => by simp only [cLab]; split_ifs <;> omega
    refine hp1.gen_step (L - 2 + 1) s1 (hsp.reachable _) (L + 1) le_rfl hNd hfree1
      (hsp.available _ _) (by omega) (by simp only [cLab]; split_ifs <;> omega) (by omega)
      (fun choice hsc => Or.inr ⟨hsp.no_urgent hsc, rfl⟩) fun s2 hg hc2 => ?_
    have hp2 := hp1.grow hg hfree1 (by simp)
    apply (hp2.permute_step (L - 2 + 1) s2 (by simp) 1 le_rfl (by omega) (by omega)
      fun i hi => by simp only [cLab]; split_ifs <;> omega).mono
    intro r hr
    rw [hr, hc2, hc1]
    split_ifs <;> omega

-- From cursor t the conveyor costs 2 swaps per cursor up to L - 3, then the end.
theorem conv_run (hsp : AllSpilled (allTarget N) spills) (h3 : 3 ≤ L) (hL : L ≤ 17)
    (hN : N = L + 1 ∨ N = L + 2) :
    ∀ r t (state : State source (allTarget N) spills), t + 2 + r = L →
      Placed L (cLab L t) state →
      Succeeds (buildBottomUp.loop t state) (fun res => res.2.swapCount =
        state.trace.swapCount + 2 * r + if N = L + 1 then 2 else 4) := by
  intro r
  induction r with
  | zero =>
    intro t state ht hp
    obtain rfl : t = L - 2 := by omega
    exact (conv_end hsp h3 hL hN hp).mono fun res hr => by rw [hr]; omega
  | succ r ih =>
    intro t state ht hp
    refine conv_step hsp hL (by omega) (by omega) hp fun next hp1 hc => ?_
    exact (ih (t + 1) next (by omega) hp1).mono fun res hr => by rw [hr, hc]; omega

end conveyor

theorem ok_of_map {initial : State source target spills} {hvalid : initial.Valid}
    (h : (buildBottomUp initial hvalid).map (·.2.swapCount) = .ok c) :
    ∃ result trace, buildBottomUp initial hvalid = .ok ⟨result, trace⟩ ∧ trace.swapCount = c := by
  cases hrun : buildBottomUp initial hvalid with
  | error e => rw [hrun] at h; cases h
  | ok value =>
    obtain ⟨result, trace⟩ := value
    rw [hrun] at h
    exact ⟨result, trace, rfl, Except.ok.inj h⟩

theorem map_of_success {initial : State source target spills} (hvalid : initial.Valid)
    (h : Succeeds (buildBottomUp.loop 0 initial) (fun r => r.2.swapCount = c)) :
    (buildBottomUp initial hvalid).map (·.2.swapCount) = .ok c := by
  obtain ⟨⟨res, trace⟩, hv, hc⟩ := h
  have hspec := loop_spec 0 initial (State.invariant.initial hvalid)
  rw [hv] at hspec
  have hsize : res.length = target.length := by
    simp [show res = _ from hspec, State.expectedStack]
  unfold buildBottomUp
  rw [hv, except_ok_bind]
  simp only [requires_of_true _ hsize, except_ok_bind]
  simp only [Except.map, pure, Except.pure, Except.ok.injEq]
  exact hc

/-! Family C: n slots in conveyor order at cursor 0 and k ∈ {1, 2} pending generations. -/

def c0Inv (n j : Nat) : Nat :=
  if j = n then n - 3 else if j = n - 1 then (if n = 3 then 2 else n - 4)
  else if j = 0 then n - 2 else if j = 1 then n - 1 else j - 2

def convState (n k : Nat) := allState n (n + k) (cLab n 0) (c0Inv n)

theorem conv_labels (h3 : 3 ≤ n) (hk : 1 ≤ k) : Labels n (n + k) (cLab n 0) (c0Inv n) where
  lt i hi := by unfold cLab; split_ifs <;> omega
  left i hi := by unfold cLab; split_ifs <;> unfold c0Inv <;> split_ifs <;> (try contradiction) <;> omega

theorem conv_valid (h3 : 3 ≤ n) (hk : 1 ≤ k) : (convState n k).Valid :=
  all_valid (conv_labels h3 hk) (by omega)

-- For 3 ≤ n ≤ 17 and k ∈ {1, 2} family C costs 2 (n - 1) + 2k - 2 swaps.
theorem conv_swapCount (h3 : 3 ≤ n) (h17 : n ≤ 17) (hk : 1 ≤ k) (hk2 : k ≤ 2) :
    (buildBottomUp (convState n k) (conv_valid h3 hk)).map (·.2.swapCount) = .ok (2 * (n - 1) + 2 * k - 2) := by
  apply map_of_success _
  apply (conv_run (all_allSpilled (n + k)) h3 h17 (by omega) (n - 2) 0 (convState n k)
    (by omega) (all_placed (conv_labels h3 hk) (by omega))).mono
  intro r hr
  rw [hr, show (convState n k).trace.swapCount = 0 from allState_swapCount]
  split_ifs <;> omega

/-! Family D: n slots and 3 pending generations. Target n is missing, so the loop
generates it at the top first. One bound step on n + 1 slots leaves the conveyor of
family C at cursor 1. -/

def dLab (n i : Nat) : Nat :=
  if i = n - 3 then 0 else if i = n - 2 then n + 1 else if i = n - 1 then 1 else i + 2

def dInv (n j : Nat) : Nat :=
  if j = 0 then n - 3 else if j = n + 1 then n - 2 else if j = 1 then n - 1 else j - 2

def dTop (n i : Nat) : Nat := if i = n then n else dLab n i

def dState (n : Nat) := allState n (n + 3) (dLab n) (dInv n)

theorem d_labels (h4 : 4 ≤ n) : Labels n (n + 3) (dLab n) (dInv n) where
  lt i hi := by unfold dLab; split_ifs <;> omega
  left i hi := by unfold dLab; split_ifs <;> unfold dInv <;> split_ifs <;> (try contradiction) <;> omega

theorem d_valid (h4 : 4 ≤ n) : (dState n).Valid := all_valid (d_labels h4) (by omega)

-- For 4 ≤ n ≤ 15 family D costs 2 (n - 1) + 2 · 3 - 2 = 2n + 2 swaps.
theorem d_swapCount (h4 : 4 ≤ n) (h15 : n ≤ 15) :
    (buildBottomUp (dState n) (d_valid h4)).map (·.2.swapCount) = .ok (2 * (n - 1) + 2 * 3 - 2) := by
  apply map_of_success _
  have hsp := all_allSpilled (n + 3)
  have hp := all_placed (d_labels h4) (by omega)
  have hfree : (dState n).positionOfNat n = none :=
    (hp.positionOf_none _).mpr fun i hi => by unfold dLab; split_ifs <;> omega
  refine hp.gen_step 0 _ (hsp.reachable _) n le_rfl (by simp) hfree (hsp.available _ _)
    (by omega) (by unfold dLab; split_ifs <;> omega) (by omega)
    (fun choice hsc => Or.inr ⟨hsp.no_urgent hsc, rfl⟩) fun s1 hg hc1 => ?_
  have hp1 : Placed (n + 1) (dTop n) s1 := (hp.grow hg hfree (by simp)).congr fun _ _ => rfl
  have htop : s1.positionOfNat (n + 1) ≠ none := by
    have hs := hp1.slot (n - 2) (by omega)
    rw [show dTop n (n - 2) = n + 1 by unfold dTop dLab; split_ifs <;> omega] at hs
    simp [hs]
  have hlab : dTop n (n - 3) = 0 := by unfold dTop dLab; split_ifs <;> omega
  refine hp1.bound_step 0 s1 (hsp.reachable _) (Or.inr ⟨fun _ => hsp.not_urgent,
    fun _ => htop⟩) (n - 3) (by omega) hlab (by omega) (by omega)
    (by rw [hp1.pending]; simp) (by unfold dTop dLab; split_ifs <;> omega)
    (all_unique hp1 (by omega) hlab) fun s2 hb hc2 => ?_
  have hp2 : Placed (n + 1) (cLab (n + 1) 1) s2 := (hp1.boundSwaps hb).congr fun i hi => by
    simp only [boundLab, dTop, dLab, cLab, swapIdx]
    split_ifs <;> omega
  apply (conv_run hsp (L := n + 1) (by omega) (by omega) (by omega) (n - 2) 1 s2 (by omega)
    hp2).mono
  intro r hr
  rw [hr, hc2, hc1, allState_swapCount]
  split_ifs <;> omega

/-! Family W with n = 17 - b slots: `windowState 17 k` is `tightState k`. -/

def windowState (n k : Nat) := winState (17 - n) (k - (17 - n))

theorem window_cls (h15 : 15 ≤ n) (h17 : n ≤ 17)
    (h : n = 15 → 4 ≤ k ∧ k % 16 ≠ 2 ∧ k % 16 ≠ 3) :
    17 - n ≤ cls (k - (17 - n) + (17 - n) - 2) ∧ 17 - n ≤ cls (k - (17 - n) + (17 - n) - 1) := by
  obtain rfl | rfl | rfl : n = 15 ∨ n = 16 ∨ n = 17 := by omega
  · obtain ⟨_, _, _⟩ := h rfl
    unfold cls
    constructor <;> omega
  all_goals unfold cls; constructor <;> omega

theorem window_valid (h15 : 15 ≤ n) (h17 : n ≤ 17)
    (h : n = 15 → 4 ≤ k ∧ k % 16 ≠ 2 ∧ k % 16 ≠ 3) : (windowState n k).Valid :=
  win_valid (by omega) (window_cls h15 h17 h).1 (window_cls h15 h17 h).2

-- For 15 ≤ n ≤ 17 and k ≥ 3 (k ≥ 4 and k mod 16 ∉ {2, 3} for n = 15) family W costs
-- 2 (n - 1) + 2k - 2 swaps.
theorem window_swapCount (h15 : 15 ≤ n) (h17 : n ≤ 17) (hk : 3 ≤ k)
    (h : n = 15 → 4 ≤ k ∧ k % 16 ≠ 2 ∧ k % 16 ≠ 3) :
    (buildBottomUp (windowState n k) (window_valid h15 h17 h)).map (·.2.swapCount) = .ok (2 * (n - 1) + 2 * k - 2) := by
  have h4 : n = 15 → 4 ≤ k := fun hn => (h hn).1
  rw [show 2 * (n - 1) + 2 * k - 2 = 2 * (k - (17 - n)) + 30 by omega]
  exact win_swapCount (by omega) (by omega) (by omega) (window_cls h15 h17 h).1
    (window_cls h15 h17 h).2

end Shuffler.Optimality.BBU
