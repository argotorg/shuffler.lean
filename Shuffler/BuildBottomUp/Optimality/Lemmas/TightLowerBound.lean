import Shuffler.BuildBottomUp.Optimality.Lemmas.GenerationLowerBound

/-! Family W: 17 - b source slots and k + b pending generations, for b ≤ 2. For k ≥ 2 and
k + b ≥ 3 BBU emits exactly 2k + 30 swaps, the upper bound 2 (17 - b - 1) + 2 (k + b) - 2.
Family T, the 17-slot family, is W with b = 0.

W is T without its b bottom slots: target j of W is target j + b of T, and slot i of W is
slot i + b of T. All labels and slots are relative, so the proofs of T carry over. Only the
values change: target j holds variable `winVal b k j`. Only X = cls (k + b - 2) and
Y = cls (k + b - 1) are not spilled. Targets k + 15 and k + 16 hold X and Y, and below k
the values X and Y repeat every 16 slots. At cursors k - 1 and k the last copy of X or Y
is at depth 15, so the urgent scan generates target k + 15 or k + 16 before the cursor
reaches it. The source holds targets 0 … 16 - b in the order `headLab b (headB b k)`.
For b = 2 both X and Y must be at least 2: value 1 is in a dropped slot. -/

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

set_option maxHeartbeats 2000000

def cls (j : Nat) : Nat := (j + 15) % 16 + 1

def winVal (b k j : Nat) : Nat :=
  if j = k + 15 then cls (k + b - 2) else if j = k + 16 then cls (k + b - 1)
  else if 17 ≤ j + b ∧ j < k ∧ (k - 1 - j) % 16 ≤ 1 then cls (j + b) else j + b

-- The second source order is used only for b = 0.
def headB (b k : Nat) : Bool := b = 0 ∧ (k % 16 = 3 ∨ k % 16 = 4)

def headLab (b : Nat) (f : Bool) (i : Nat) : Nat :=
  if f then
    if i = 0 then 16 else if i = 1 then 3 else if i = 14 then 1 else if i = 15 then 0
    else if i = 16 then 2 else i + 2
  else if i = 15 - b then 0 else if i = 16 - b then 1 else i + 2

def headInv (b : Nat) (f : Bool) (j : Nat) : Nat :=
  if f then
    if j = 16 then 0 else if j = 3 then 1 else if j = 1 then 14 else if j = 0 then 15
    else if j = 2 then 16 else j - 2
  else if j = 0 then 15 - b else if j = 1 then 16 - b else j - 2

theorem headB_spec (b k : Nat) : headB b k = true → b = 0 := by simp [headB]; omega

theorem headLab_spec {f : Bool} (hf : f = true → b = 0) (hi : i < 17 - b) :
    headLab b f i < 17 - b ∧ headInv b f (headLab b f i) = i := by
  cases f
  · simp only [headLab, headInv, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> (try contradiction) <;> constructor <;> omega
  · obtain rfl := hf rfl
    simp only [headLab, headInv, ↓reduceIte]
    split_ifs <;> (try contradiction) <;> constructor <;> omega

theorem headInv_spec {f : Bool} (hf : f = true → b = 0) (hj : j < 17 - b) :
    headInv b f j < 17 - b ∧ headLab b f (headInv b f j) = j := by
  cases f
  · simp only [headLab, headInv, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> (try contradiction) <;> constructor <;> omega
  · obtain rfl := hf rfl
    simp only [headLab, headInv, ↓reduceIte]
    split_ifs <;> (try contradiction) <;> constructor <;> omega

def winSource (b k : Nat) : Stack :=
  List.ofFn fun i : Fin (17 - b) => .Var ⟨headLab b (headB b k) i.val + b⟩

def winTarget (b k : Nat) : Stack := List.ofFn fun j : Fin (17 + k) => .Var ⟨winVal b k j.val⟩

def winSpills (b k : Nat) : SpillSet :=
  ((Finset.range (17 + k + b)).filter fun j => j ≠ cls (k + b - 2) ∧ j ≠ cls (k + b - 1)).image
    VarId.mk

@[simp] theorem winSource_length : (winSource b k).length = 17 - b := by simp [winSource]
@[simp] theorem winTarget_length : (winTarget b k).length = 17 + k := by simp [winTarget]

def winMapping (b k : Nat) : Mapping (winSource b k).length (winTarget b k).length where
  toFun i := some ⟨headLab b (headB b k) i.val, by
    have := (headLab_spec (headB_spec b k) (by simpa using i.isLt)).1
    simp only [winTarget_length]
    omega⟩
  invFun j := if h : j.val < 17 - b then some ⟨headInv b (headB b k) j.val, by
    simpa using (headInv_spec (headB_spec b k) h).1⟩ else none
  inv i j := by
    have hi : i.val < 17 - b := by simpa using i.isLt
    obtain ⟨h1, h2⟩ := headLab_spec (headB_spec b k) hi
    by_cases h : j.val < 17 - b
    · have := (headInv_spec (headB_spec b k) h).2
      simp only [h, ↓reduceDIte, Option.some.injEq, Fin.ext_iff]
      constructor <;> intro he <;> rw [← he] <;> assumption
    · simp only [h, ↓reduceDIte, reduceCtorEq, false_iff, Option.some.injEq, Fin.ext_iff]
      omega

def winState (b k : Nat) : State (winSource b k) (winTarget b k) (winSpills b k) where
  planned_mapping := winMapping b k
  stack := winSource b k
  trace := .Lit (winSource b k)
  mapping := winMapping b k
  pending_generations := k + b


-- The two variables that are not spilled.
def Shared (b k v : Nat) : Prop := v = cls (k + b - 2) ∨ v = cls (k + b - 1)

instance : Decidable (Shared b k v) := by unfold Shared; infer_instance

theorem winVal_lt (h : j < 17 + k) : winVal b k j < 17 + k + b := by
  unfold winVal cls; split_ifs <;> omega

@[simp] theorem winTarget_getElem (j : Nat) (h : j < (winTarget b k).length) :
    (winTarget b k)[j] = .Var ⟨winVal b k j⟩ := by
  simp [winTarget]

theorem win_spilled (h : j < 17 + k) :
    (winSpills b k).is_spilled (.Var ⟨winVal b k j⟩) ↔ ¬ Shared b k (winVal b k j) := by
  simp [SpillSet.is_spilled, winSpills, winVal_lt h, Shared]

variable {b k len : Nat} {lab : Nat → Nat}
  {state : State (winSource b k) (winTarget b k) (winSpills b k)}

theorem positionOfNat_none_iff {state : State source target spills} (j : Nat)
    (hj : j < target.length) : state.positionOfNat j = none ↔ state.positionOf ⟨j, hj⟩ = none := by
  simp [State.positionOfNat, hj]

theorem stack_val (hp : Placed len lab state) (i : Nat) (hi : i < state.stack.length) :
    state.stack[i] = .Var ⟨winVal b k (lab i)⟩ := by
  rw [hp.getElem, winTarget_getElem]

-- Every unbound shared target has a copy among the 16 top slots.
theorem win_reachable (hp : Placed len lab state)
    (h : ∀ j < 17 + k, (∀ i < len, lab i ≠ j) → Shared b k (winVal b k j) →
      ∃ i < len, len ≤ i + 16 ∧ winVal b k (lab i) = winVal b k j) : state.reachable := by
  intro dest hd
  have hfree := (hp.unbound dest).mp hd
  have hdl : dest.val < 17 + k := by simpa using dest.isLt
  unfold State.isReachable
  rw [Fin.getElem_fin, winTarget_getElem]
  by_cases hs : Shared b k (winVal b k dest.val)
  · obtain ⟨i, hi, hr, hv⟩ := h dest.val hdl hfree hs
    refine Or.inr (Or.inr ⟨⟨i, hp.length ▸ hi⟩, ?_, ?_⟩)
    · rw [Fin.getElem_fin, stack_val hp, hv]
    · rw [Stack.isDupReachable_iff_length]
      have := hp.length
      unfold MAX_DUP_DEPTH
      simp only
      omega
  · exact Or.inr (Or.inl ((win_spilled hdl).mpr hs))

theorem urgent_copy (hp : Placed len lab state) (hu : Urgent t state o) :
    o < 17 + k ∧ (∀ i < len, lab i ≠ o) ∧ Shared b k (winVal b k o) ∧ 16 ≤ len ∧
      len - 16 ≠ t ∧ winVal b k (lab (len - 16)) = winVal b k o := by
  obtain ⟨ho, hpos, _, hns, copy, hcopy, hdepth, hne⟩ := hu
  have hol : o < 17 + k := by simpa using ho
  have hval := shallowestCopyPosition_value _ _ _ hcopy
  rw [Stack.offsetToDepth_val] at hdepth
  have hc := copy.isLt
  have hl := hp.length
  unfold MAX_DUP_DEPTH at hdepth
  have hcv : copy.val = len - 16 := by omega
  refine ⟨hol, (hp.positionOf_none o).mp ((positionOfNat_none_iff o ho).mpr hpos), ?_, by omega, by omega, ?_⟩
  · by_contra hs
    rw [winTarget_getElem] at hns
    exact hns ((win_spilled hol).mpr hs)
  · rw [Fin.getElem_fin, stack_val hp, winTarget_getElem] at hval
    rw [← hcv]
    simpa using hval

theorem urgent_of (hp : Placed len lab state) (ho : o < 17 + k) (hfree : ∀ i < len, lab i ≠ o)
    (hs : Shared b k (winVal b k o)) (h16 : 16 ≤ len) (hne : len - 16 ≠ t)
    (hval : winVal b k (lab (len - 16)) = winVal b k o)
    (habove : ∀ i < len, len - 16 < i → winVal b k (lab i) ≠ winVal b k o) :
    Urgent t state o := by
  have hl := hp.length
  have hoN : o < (winTarget b k).length := by simpa using ho
  refine ⟨hoN, (positionOfNat_none_iff o hoN).mp ((hp.positionOf_none o).mpr hfree), by simp [Value.can_be_freely_generated], ?_, ?_⟩
  · rw [winTarget_getElem]
    exact fun h => (win_spilled ho).mp h hs
  · let copy : Fin state.stack.length := ⟨len - 16, by omega⟩
    have hv : state.stack[copy] = (winTarget b k)[o] := by
      simp only [copy, Fin.getElem_fin, stack_val hp, hval, winTarget_getElem]
    have hmem : (state.stack.shallowestCopyPosition (winTarget b k)[o]).isSome :=
      (Stack.shallowestCopyPosition_isSome _ _).mpr (hv ▸ List.getElem_mem copy.isLt)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hmem
    have hge := shallowestCopyPosition_ge _ _ c copy hc hv
    have hcval := shallowestCopyPosition_value _ _ _ hc
    have hcl := c.isLt
    have hceq : c.val = len - 16 := by
      by_contra hne'
      apply habove c.val (by omega) (by simp only [copy] at hge; omega)
      rw [Fin.getElem_fin, stack_val hp, winTarget_getElem] at hcval
      simpa using hcval
    refine ⟨c, hc, ?_, by omega⟩
    rw [Stack.offsetToDepth_val]
    unfold MAX_DUP_DEPTH
    omega

theorem _root_.Shuffler.BuildBottomUp.ScanProgress.eq_some {state : State source target spills}
    (h : ScanProgress t state (List.range' t (target.length - t)) choice)
    (hu : Urgent t state d) (htd : t ≤ d) (hmin : ∀ o, Urgent t state o → d ≤ o) :
    choice = some d := by
  have hdN : d < target.length := hu.1
  have hmem : d ∈ List.range' t (target.length - t) := by simp; omega
  obtain ⟨o, rfl⟩ := Option.isSome_iff_exists.mp (h.covered d hmem hu)
  have h1 := h.least o rfl d hmem hu
  have h2 := hmin o (h.selected o rfl)
  rw [show o = d by omega]

theorem winVal_head (hk : 2 ≤ k + b) (hj : j + b < 17) : winVal b k j = j + b := by
  unfold winVal; split_ifs <;> omega

theorem cls_le (j : Nat) : cls j < 17 := by unfold cls; omega

theorem shared_bounds (hx : b ≤ cls (k + b - 2)) (hy : b ≤ cls (k + b - 1)) (hs : Shared b k v) :
    v < 17 ∧ b ≤ v := by
  have := cls_le (k + b - 2)
  have := cls_le (k + b - 1)
  unfold Shared at hs
  omega

-- A copy of each shared value among the source values j + b with j + b < 17.
theorem reach_head (hp : Placed len lab state) (hk : 2 ≤ k + b) (hx : b ≤ cls (k + b - 2))
    (hy : b ≤ cls (k + b - 1))
    (h : ∀ e, e + b < 17 → Shared b k (e + b) → ∃ i < len, len ≤ i + 16 ∧ lab i = e) :
    state.reachable :=
  win_reachable hp fun j _ _ hs => by
    have hv := shared_bounds hx hy hs
    obtain ⟨i, hi, hr, he⟩ := h (winVal b k j - b) (by omega) (by rwa [Nat.sub_add_cancel hv.2])
    exact ⟨i, hi, hr, by rw [he, winVal_head hk (by omega), Nat.sub_add_cancel hv.2]⟩

theorem winMapping_symm (j : Fin (winTarget b k).length) :
    ((winMapping b k).symm j).map Fin.val =
      if j.val < 17 - b then some (headInv b (headB b k) j.val) else none := by
  change Option.map Fin.val (if h : j.val < 17 - b then some _ else none) = _
  split_ifs <;> rfl

theorem win_unbound (j : Fin (winTarget b k).length) :
    (winState b k).mapping.symm j = none ↔ 17 - b ≤ j.val := by
  have h := winMapping_symm (b := b) (k := k) j
  rw [← Option.map_eq_none_iff (f := Fin.val)]
  change Option.map Fin.val ((winMapping b k).symm j) = none ↔ _
  rw [h]
  split_ifs <;> simp <;> omega

theorem win_placed (hb : b ≤ 2) (hk : 2 ≤ k + b) :
    Placed (17 - b) (headLab b (headB b k)) (winState b k) where
  length := winSource_length
  value i hi := by
    have := (headLab_spec (headB_spec b k) hi).1
    simp only [winState, winSource, winTarget, List.getElem?_ofFn, hi,
      show headLab b (headB b k) i < 17 + k by omega, ↓reduceDIte,
      winVal_head hk (show headLab b (headB b k) i + b < 17 by omega)]
  slot i hi := by
    obtain ⟨h1, h2⟩ := headLab_spec (headB_spec b k) hi
    have hlt : headLab b (headB b k) i < (winTarget b k).length := by simp; omega
    have hs := winMapping_symm (b := b) (k := k) ⟨_, hlt⟩
    simp only [h1, ↓reduceIte, h2] at hs
    simp only [State.positionOfNat, State.positionOf, hlt, ↓reduceDIte]
    exact hs
  expected := by
    apply List.ext_getElem (by simp [State.expectedStack])
    intro j _ hj
    simp only [State.expectedStack, List.getElem_ofFn]
    split
    · rename_i pos hpos
      have hs := winMapping_symm (b := b) (k := k) ⟨j, hj⟩
      change (winMapping b k).symm _ = some pos at hpos
      rw [hpos] at hs
      replace hs : some pos.val = if j < 17 - b then some (headInv b (headB b k) j) else none := hs
      have hlt : j < 17 - b := by by_contra hn; simp [hn] at hs
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hs
      change (winSource b k)[pos.val] = _
      simp only [winSource, List.getElem_ofFn, winTarget_getElem, hs,
        (headInv_spec (headB_spec b k) hlt).2, winVal_head hk (show j + b < 17 by omega)]
    · rfl
  pending := by simp [winState]; omega
  le := by simp; omega

theorem win_valid (hb : b ≤ 2) (hx : b ≤ cls (k + b - 2)) (hy : b ≤ cls (k + b - 1)) :
    (winState b k).Valid where
  size := by simp [winState]; omega
  pending := by
    unfold Mapping.unmapped_target_slots
    rw [Finset.filter_congr fun j _ => win_unbound j]
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : Fin (winTarget b k).length => j.val < 17 - b)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin, Fin.card_filter_val_lt,
      winTarget_length] at this
    simp only [winState]
    omega
  available j := by
    have hj : j.val < 17 + k := by simpa using j.isLt
    unfold State.isAvailable
    rw [Fin.getElem_fin, winTarget_getElem]
    by_cases hs : Shared b k (winVal b k j.val)
    · right; right
      rw [Stack.shallowestCopyPosition_isSome]
      have hv := shared_bounds hx hy hs
      have hi := headInv_spec (headB_spec b k) (show winVal b k j.val - b < 17 - b by omega)
      simp only [winState, winSource, List.mem_ofFn]
      exact ⟨⟨_, hi.1⟩, by simp [hi.2, Nat.sub_add_cancel hv.2]⟩
    · exact Or.inr (Or.inl ((win_spilled hj).mpr hs))

-- Equal values below the two last targets lie 16 or more apart.
theorem winVal_sep (hk : 3 ≤ k + b) (hac : a < c) (hc : c < 17 + k)
    (h : winVal b k a = winVal b k c) : a + 16 ≤ c := by
  unfold winVal cls at h; split_ifs at h <;> omega

theorem winVal_window_x (ha : 1 ≤ a + b) (hak : a + 2 ≤ k) :
    winVal b k (a + (k - 2 - a) % 16) = cls (k + b - 2) := by
  unfold winVal cls; split_ifs <;> omega

theorem winVal_window_y (ha : 1 ≤ a + b) (hak : a + 1 ≤ k) :
    winVal b k (a + (k - 1 - a) % 16) = cls (k + b - 1) := by
  unfold winVal cls; split_ifs <;> omega

theorem winVal_next (ht : 1 ≤ t) (htk : t + 2 ≤ k) (ho : t + 15 ≤ o)
    (h : winVal b k (t - 1) = winVal b k o) : winVal b k (t + 15) = winVal b k (t - 1) := by
  unfold winVal cls at *; split_ifs at * <;> omega

theorem target_ne (ha : a < 17 + k) (hc : c < 17 + k) (h : winVal b k a ≠ winVal b k c) :
    (winTarget b k)[a]? ≠ (winTarget b k)[c]? := by
  rw [List.getElem?_eq_getElem (by simpa using ha), List.getElem?_eq_getElem (by simpa using hc)]
  simpa using h

-- The 16 top slots carry the labels a, …, a + 15, so both shared values have a copy.
theorem reach_window (hp : Placed len lab state) (a : Nat) (ha : 1 ≤ a + b) (hak : a + 2 ≤ k)
    (inv : Nat → Nat)
    (hinv : ∀ e, a ≤ e → e ≤ a + 15 → inv e < len ∧ len ≤ inv e + 16 ∧ lab (inv e) = e) :
    state.reachable :=
  win_reachable hp fun j _ _ hs => by
    rcases hs with hs | hs
    · have h := hinv (a + (k - 2 - a) % 16) (by omega) (by omega)
      exact ⟨_, h.1, h.2.1, by rw [h.2.2, winVal_window_x ha hak, hs]⟩
    · have h := hinv (a + (k - 1 - a) % 16) (by omega) (by omega)
      exact ⟨_, h.1, h.2.1, by rw [h.2.2, winVal_window_y ha (by omega), hs]⟩

-- Labels at cursor t in the middle phase: slots below t are final, slots t … t + 12
-- carry i + 2, and slots t + 13 and t + 14 carry t and t + 1.
def midLab (t i : Nat) : Nat :=
  if i < t then i else if i ≤ t + 12 then i + 2 else if i = t + 13 then t
  else if i = t + 14 then t + 1 else i

def midInv (t e : Nat) : Nat :=
  if e < t then e else if e = t then t + 13 else if e = t + 1 then t + 14 else e - 2

theorem midLab_midInv (h : e ≤ t + 14) : midLab t (midInv t e) = e := by
  unfold midLab midInv; split_ifs <;> omega

-- Label facts of the middle phase.
def midTop (t i : Nat) : Nat := if i = t + 15 then t + 15 else midLab t i

theorem midLab_free (hi : i < t + 15) : midLab t i < t + 15 := by
  unfold midLab; split_ifs <;> omega

theorem midLab_window (h1 : t ≤ i) (h2 : i ≤ t + 14) : t ≤ midLab t i ∧ midLab t i ≤ t + 14 := by
  unfold midLab; split_ifs <;> omega

theorem midInv_lt (h : e ≤ t + 14) :
    midInv t e < t + 15 ∧ (t ≤ e → t ≤ midInv t e) ∧ (e < t → midInv t e = e) := by
  unfold midInv; split_ifs <;> omega

theorem midTop_unique (hk : 3 ≤ k + b) (htk : t + 2 ≤ k) (hs : s < t + 16)
    (hsc : s ≠ t + 13) (hns : midTop t s ≠ s) :
    midTop t s < 17 + k ∧ winVal b k (midTop t s) ≠ winVal b k t := by
  unfold midTop midLab at *; unfold winVal cls; split_ifs at * <;> omega

theorem midTop_next (hi : i < t + 16) :
    boundLab (t + 16) (t + 13) t (midTop t) i = midLab (t + 1) i := by
  simp only [boundLab, swapIdx, midTop, midLab]
  split_ifs <;> omega

theorem avail_of_reach {state : State source target spills} (hr : state.reachable)
    (hd : state.mapping.symm d = none) : state.isAvailable d := by
  rcases hr d hd with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨c, hc, _⟩ := h.shallowest
    exact Or.inr (Or.inr (by rw [hc]; rfl))

section steps

variable {post : ((res : Stack) × Trace (winSpills b k) (winSource b k) res) → Prop}

-- At cursor t of the middle phase the loop generates target t + 15 and then spends
-- 2 swaps on cursor t.
theorem mid_step (hk : 3 ≤ k + b) (ht : 2 ≤ t + b) (htk : t + 2 ≤ k)
    (hx : b ≤ cls (k + b - 2)) (hy : b ≤ cls (k + b - 1))
    (hp : Placed (t + 15) (midLab t) state)
    (cont : ∀ next : State (winSource b k) (winTarget b k) (winSpills b k),
      Placed (t + 16) (midLab (t + 1)) next →
      next.trace.swapCount = state.trace.swapCount + 2 →
      Succeeds (buildBottomUp.loop (t + 1) next) post) :
    Succeeds (buildBottomUp.loop t state) post := by
  have hl := hp.length
  have hN : t + 15 < (winTarget b k).length := by simp; omega
  have hfree : state.positionOfNat (t + 15) = none :=
    (hp.positionOf_none _).mpr fun i hi => (midLab_free hi).ne
  have hge : ∀ o, (∀ i < t + 15, midLab t i ≠ o) → t + 15 ≤ o := fun o ho => by
    by_contra hlt
    exact ho (midInv t o) (midInv_lt (by omega)).1 (midLab_midInv (by omega))
  have hreach : state.reachable := by
    rcases Nat.eq_zero_or_pos t with rfl | ht1
    · exact reach_head hp (by omega) hx hy fun e he _ =>
        ⟨midInv 0 e, (midInv_lt (by omega)).1, by omega, midLab_midInv (by omega)⟩
    · exact reach_window hp (t - 1) (by omega) (by omega) (midInv t) fun e _ _ => by
        have := midInv_lt (t := t) (e := e) (by omega)
        exact ⟨by omega, by omega, midLab_midInv (by omega)⟩
  refine hp.gen_step t state hreach (t + 15) le_rfl hN hfree
    (avail_of_reach hreach (symm_eq_none_of_positionOf hN hfree)) (by omega)
    (by unfold midLab; split_ifs <;> omega) (by omega) ?_ fun s1 hg hc1 => ?_
  · intro choice hsc
    cases choice with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some o =>
      left
      obtain ⟨hoN, hof, hos, h16, _, hv⟩ := urgent_copy hp (hsc.selected o rfl)
      have hml : midLab t (t + 15 - 16) = t - 1 := by unfold midLab; split_ifs <;> omega
      rw [hml] at hv
      have hnext := winVal_next (by omega) htk (hge o hof) hv
      refine hsc.eq_some (urgent_of hp (by omega) (fun i hi => (midLab_free hi).ne)
        (by rw [hnext, hv]; exact hos) (by omega) (by omega) (by rw [hml, hnext])
        fun i hi hgt he => ?_) (by omega) fun o' ho' => hge o' (urgent_copy hp ho').2.1
      have hb := midLab_window (t := t) (i := i) (by omega) (by omega)
      rw [hnext] at he
      have := winVal_sep hk (by omega) (by omega) he.symm
      omega
  · have hp1 : Placed (t + 16) (midTop t) s1 := hp.grow hg hfree (by simp; omega)
    have hl1 := hp1.length
    refine hp1.bound_step t s1 (reach_window hp1 t (by omega) (by omega)
      (fun e => if e = t + 15 then t + 15 else midInv t e) fun e _ _ => ?_) (Or.inl (by omega))
      (t + 13) (by omega) (by simp [midTop, midLab]) (by omega) (by omega)
      (by rw [hp1.pending]; simp; omega) (by simp [midTop, midLab])
      (fun s hs hsc hns => ?_) fun next hb hc => ?_
    · by_cases he : e = t + 15
      · simp [he, midTop]
      · have := midInv_lt (t := t) (e := e) (by omega)
        simp only [he, ↓reduceIte, midTop]
        rw [ite_eq_right (by omega), midLab_midInv (by omega)]
        omega
    · have h := midTop_unique hk htk hs hsc hns
      exact target_ne h.1 (by omega) h.2
    · exact cont next (hp1.boundSwaps hb |>.congr fun i hi => midTop_next hi)
        (by rw [hc, hc1]; simp)

end steps

-- Label facts of the two shift steps and the tail.
def xTop (k i : Nat) : Nat := if i = k + 14 then k + 15 else midLab (k - 1) i
def xInv (k e : Nat) : Nat := if e = k + 15 then k + 14 else midInv (k - 1) e
def yLab (k i : Nat) : Nat := if i = k + 12 then k + 15 else midLab k i
def yInv (k e : Nat) : Nat := if e = k + 15 then k + 12 else midInv k e
def yTop (k i : Nat) : Nat := if i = k + 15 then k + 16 else yLab k i
def yTInv (k e : Nat) : Nat := if e = k + 16 then k + 15 else yInv k e

-- Labels at cursor u of the tail: slots below u are final, slot k + 14 carries u.
def endLab (k u i : Nat) : Nat :=
  if i < u then i else if i ≤ k + 11 then i + 2 else if i = k + 12 then k + 15
  else if i = k + 13 then k + 16 else if i = k + 14 then u else if i = k + 15 then u + 1 else i

def endInv (k u e : Nat) : Nat :=
  if e < u then e else if e = u then k + 14 else if e = u + 1 then k + 15
  else if e ≤ k + 13 then e - 2 else if e = k + 15 then k + 12 else if e = k + 16 then k + 13 else e

def endA (k i : Nat) : Nat := if i = k + 13 then k + 16 else if i = k + 14 then k + 13 else i
def endAInv (k e : Nat) : Nat := if e = k + 16 then k + 13 else if e = k + 13 then k + 14 else e
def endB (k i : Nat) : Nat := if i = k + 14 then k + 15 else if i = k + 15 then k + 16 else i
def endBInv (k e : Nat) : Nat := if e = k + 15 then k + 14 else if e = k + 16 then k + 15 else e

theorem free_cover (inv : Nat → Nat) (S : Nat → Prop)
    (h : ∀ e < 17 + k, ¬ S e → inv e < len ∧ lab (inv e) = e) :
    ∀ j < 17 + k, (∀ i < len, lab i ≠ j) → S j := fun j hj hf => by
  by_contra hs
  obtain ⟨h1, h2⟩ := h j hj hs
  exact hf _ h1 h2

theorem not_shared_14 (hk : 3 ≤ k + b) : ¬ Shared b k (winVal b k (k + 14)) := by
  unfold Shared winVal cls; split_ifs <;> omega

theorem shared_ge (hk : 3 ≤ k + b) (ho : k + 14 ≤ o) (hoN : o < 17 + k)
    (hs : Shared b k (winVal b k o)) : k + 15 ≤ o := by
  unfold Shared winVal cls at hs; split_ifs at hs <;> omega

theorem xInv_spec (hk2 : 2 ≤ k) (he : e < 17 + k) (hs : ¬ (e = k + 14 ∨ e = k + 16)) :
    xInv k e < k + 15 ∧ xTop k (xInv k e) = e := by
  unfold xInv midInv; split_ifs <;> refine ⟨by omega, ?_⟩ <;> unfold xTop midLab <;> split_ifs <;> omega

theorem yInv_spec (he : e < 17 + k) (hs : ¬ (e = k + 14 ∨ e = k + 16)) :
    yInv k e < k + 15 ∧ yLab k (yInv k e) = e := by
  unfold yInv yLab midInv midLab; split_ifs <;> omega

theorem yTInv_spec (he : e < 17 + k) (hs : ¬ e = k + 14) :
    yTInv k e < k + 16 ∧ yTop k (yTInv k e) = e := by
  unfold yTInv yTop yInv yLab midInv midLab; split_ifs <;> omega

theorem endInv_spec (hu : k + 1 ≤ u) (hu2 : u ≤ k + 12) (he : e < 17 + k) (hs : ¬ e = k + 14) :
    endInv k u e < k + 16 ∧ endLab k u (endInv k u e) = e := by
  unfold endInv; split_ifs <;> refine ⟨by omega, ?_⟩ <;> unfold endLab <;> split_ifs <;> omega

theorem endAInv_spec (he : e < 17 + k) (hs : ¬ e = k + 14) :
    endAInv k e < k + 16 ∧ endA k (endAInv k e) = e := by
  unfold endAInv endA; split_ifs <;> omega

theorem endBInv_spec (he : e < 17 + k) (hs : ¬ e = k + 14) :
    endBInv k e < k + 16 ∧ endB k (endBInv k e) = e := by
  unfold endBInv endB; split_ifs <;> omega

theorem shiftX_val (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) :
    winVal b k (midLab (k - 1) (k + 14 - 16)) = winVal b k (k + 15) := by
  unfold midLab winVal cls; split_ifs <;> omega

theorem shiftX_above (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) (hi : i < k + 14) (h : k + 14 - 16 < i) :
    winVal b k (midLab (k - 1) i) ≠ winVal b k (k + 15) := by
  unfold midLab winVal cls; split_ifs <;> omega

theorem shiftX_copy (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) :
    winVal b k (xTop k (k + 12)) = winVal b k (k + 16) := by
  unfold xTop midLab winVal cls; split_ifs <;> omega

theorem xTop_unique (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) (hs : s < k + 15) (hsc : s ≠ k + 12)
    (hns : xTop k s ≠ s) : xTop k s < 17 + k ∧ winVal b k (xTop k s) ≠ winVal b k (k - 1) := by
  unfold xTop midLab at *; unfold winVal cls; split_ifs at * <;> omega

theorem xTop_next (hk2 : 2 ≤ k) (hi : i < k + 15) :
    boundLab (k + 15) (k + 12) (k - 1) (xTop k) i = yLab k i := by
  simp only [boundLab, show ¬ (k + 12 = k + 15 - 1) by omega, ↓reduceIte, swapIdx, xTop, yLab, midLab]
  split_ifs <;> omega

theorem shiftY_val (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) :
    winVal b k (yLab k (k + 15 - 16)) = winVal b k (k + 16) := by
  unfold yLab midLab winVal cls; split_ifs <;> omega

theorem shiftY_above (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) (hi : i < k + 15) (h : k + 15 - 16 < i) :
    winVal b k (yLab k i) ≠ winVal b k (k + 16) := by
  unfold yLab midLab winVal cls; split_ifs <;> omega

theorem yTop_unique (hk : 3 ≤ k + b) (hs : s < k + 16) (hsc : s ≠ k + 13) :
    yTop k s < 17 + k ∧ winVal b k (yTop k s) ≠ winVal b k k := by
  unfold yTop yLab midLab at *; unfold winVal cls; split_ifs at * <;> omega

theorem yTop_next (hi : i < k + 16) :
    boundLab (k + 16) (k + 13) k (yTop k) i = endLab k (k + 1) i := by
  simp only [boundLab, swapIdx, yTop, yLab, midLab, endLab]
  split_ifs <;> omega

theorem endLab_unique (hk : 3 ≤ k + b) (hu : k + 1 ≤ u) (hu2 : u ≤ k + 12) (hs : s < k + 16)
    (hsc : s ≠ k + 14) (hns : endLab k u s ≠ s) :
    endLab k u s < 17 + k ∧ winVal b k (endLab k u s) ≠ winVal b k u := by
  unfold endLab at *; unfold winVal cls; split_ifs at * <;> omega

theorem endA_unique (hk : 3 ≤ k + b) (hs : s < k + 16) (hsc : s ≠ k + 14) (hns : endA k s ≠ s) :
    endA k s < 17 + k ∧ winVal b k (endA k s) ≠ winVal b k (k + 13) := by
  unfold endA at *; unfold winVal cls; split_ifs at * <;> omega

theorem endLab_next (hu2 : u ≤ k + 11) (hi : i < k + 16) :
    boundLab (k + 16) (k + 14) u (endLab k u) i = endLab k (u + 1) i := by
  simp only [boundLab, swapIdx, endLab]
  split_ifs <;> omega

theorem endLab_last (hi : i < k + 16) :
    boundLab (k + 16) (k + 14) (k + 12) (endLab k (k + 12)) i = endA k i := by
  simp only [boundLab, swapIdx, endLab, endA]
  split_ifs <;> omega

theorem endA_next (hi : i < k + 16) :
    boundLab (k + 16) (k + 14) (k + 13) (endA k) i = endB k i := by
  simp only [boundLab, swapIdx, endA, endB]
  split_ifs <;> omega

-- In the tail only target k + 14 is unbound. It is spilled, so no target is urgent.
theorem late_quiet (hk : 3 ≤ k + b) (hp : Placed (k + 16) lab state)
    (hfree : ∀ j < 17 + k, (∀ i < k + 16, lab i ≠ j) → j = k + 14) :
    state.reachable ∧ (∀ o, ¬ Urgent t state o) ∧ state.positionOfNat (k + 16) ≠ none := by
  refine ⟨win_reachable hp fun j hj hf hs => ?_, fun o hu => ?_, fun h => ?_⟩
  · rw [hfree j hj hf] at hs
    exact (not_shared_14 hk hs).elim
  · obtain ⟨ho, hof, hos, _⟩ := urgent_copy hp hu
    rw [hfree o ho hof] at hos
    exact not_shared_14 hk hos
  · have := hfree (k + 16) (by omega) ((hp.positionOf_none _).mp h)
    omega

section steps

variable {post : ((res : Stack) × Trace (winSpills b k) (winSource b k) res) → Prop}

-- At cursor k - 1 the loop generates target k + 15, whose value has its last copy at
-- slot k - 2, and then spends 2 swaps on cursor k - 1.
theorem shiftX_step (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) (hp : Placed (k + 14) (midLab (k - 1)) state)
    (cont : ∀ next : State (winSource b k) (winTarget b k) (winSpills b k),
      Placed (k + 15) (yLab k) next →
      next.trace.swapCount = state.trace.swapCount + 2 →
      Succeeds (buildBottomUp.loop k next) post) :
    Succeeds (buildBottomUp.loop (k - 1) state) post := by
  have hl := hp.length
  have hN : k + 15 < (winTarget b k).length := by simp only [winTarget_length]; omega
  have hlabfree : ∀ i < k + 14, midLab (k - 1) i ≠ k + 15 := fun i hi => by
    have := midLab_free (t := k - 1) (i := i) (by omega)
    omega
  have hfree : state.positionOfNat (k + 15) = none := (hp.positionOf_none _).mpr hlabfree
  have hge : ∀ o, (∀ i < k + 14, midLab (k - 1) i ≠ o) → k + 14 ≤ o := fun o ho => by
    by_contra hlt
    have := (midInv_lt (t := k - 1) (e := o) (by omega)).1
    exact ho (midInv (k - 1) o) (by omega) (midLab_midInv (by omega))
  have hreach : state.reachable := reach_window hp (k - 2) (by omega) (by omega) (midInv (k - 1))
    fun e _ _ => by
      have := midInv_lt (t := k - 1) (e := e) (by omega)
      exact ⟨by omega, by omega, midLab_midInv (by omega)⟩
  have hurg : Urgent (k - 1) state (k + 15) := urgent_of hp (by omega) hlabfree
    (by simp [Shared, winVal]) (by omega) (by omega) (shiftX_val hk hk2)
    fun i hi hgt => shiftX_above hk hk2 hi hgt
  refine hp.gen_step (k - 1) state hreach (k + 15) (by omega) hN hfree
    (avail_of_reach hreach (symm_eq_none_of_positionOf hN hfree)) (by omega)
    (by unfold midLab; split_ifs <;> omega) (by omega)
    (fun choice hsc => Or.inl (hsc.eq_some hurg (by omega) fun o ho => by
      obtain ⟨hoN, hof, hos, _⟩ := urgent_copy hp ho
      exact shared_ge hk (hge o hof) hoN hos)) fun s1 hg hc1 => ?_
  have hp1 : Placed (k + 15) (xTop k) s1 :=
    hp.grow hg hfree (by simp only [winTarget_length]; omega)
  have hreach1 : s1.reachable := win_reachable hp1 fun j hj hf hs => by
    rcases free_cover (xInv k) (fun e => e = k + 14 ∨ e = k + 16)
      (fun e he hs => xInv_spec hk2 he hs) j hj hf with h | h
    · rw [h] at hs
      exact (not_shared_14 hk hs).elim
    · exact ⟨k + 12, by omega, by omega, by rw [shiftX_copy hk hk2, h]⟩
  refine hp1.bound_step (k - 1) s1 hreach1 (Or.inl (by omega)) (k + 12) (by omega)
    (by unfold xTop midLab; split_ifs <;> omega) (by omega) (by omega)
    (by rw [hp1.pending]; simp only [winTarget_length]; omega)
    (by unfold xTop midLab; split_ifs <;> omega)
    (fun s hs hsc hns => ?_) fun next hb hc => ?_
  · have h := xTop_unique hk hk2 hs hsc hns
    exact target_ne h.1 (by omega) h.2
  · rw [show k - 1 + 1 = k by omega]
    exact cont next (hp1.boundSwaps hb |>.congr fun i hi => xTop_next hk2 hi)
      (by rw [hc, hc1]; simp)

-- At cursor k the loop generates target k + 16, whose value has its last copy at
-- slot k - 1, and then spends 2 swaps on cursor k.
theorem shiftY_step (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) (hp : Placed (k + 15) (yLab k) state)
    (cont : ∀ next : State (winSource b k) (winTarget b k) (winSpills b k),
      Placed (k + 16) (endLab k (k + 1)) next →
      next.trace.swapCount = state.trace.swapCount + 2 →
      Succeeds (buildBottomUp.loop (k + 1) next) post) :
    Succeeds (buildBottomUp.loop k state) post := by
  have hl := hp.length
  have hN : k + 16 < (winTarget b k).length := by simp only [winTarget_length]; omega
  have hcover := free_cover (yInv k) (fun e => e = k + 14 ∨ e = k + 16)
    fun e he hs => yInv_spec he hs
  have hlabfree : ∀ i < k + 15, yLab k i ≠ k + 16 := fun i hi => by
    unfold yLab midLab; split_ifs <;> omega
  have hfree : state.positionOfNat (k + 16) = none := (hp.positionOf_none _).mpr hlabfree
  have hreach : state.reachable := win_reachable hp fun j hj hf hs => by
    rcases hcover j hj hf with h | h
    · rw [h] at hs
      exact (not_shared_14 hk hs).elim
    · exact ⟨k + 15 - 16, by omega, by omega, by rw [shiftY_val hk hk2, h]⟩
  have hurg : Urgent k state (k + 16) := urgent_of hp (by omega) hlabfree
    (by simp [Shared, winVal]) (by omega) (by omega) (shiftY_val hk hk2)
    fun i hi hgt => shiftY_above hk hk2 hi hgt
  refine hp.gen_step k state hreach (k + 16) (by omega) hN hfree
    (avail_of_reach hreach (symm_eq_none_of_positionOf hN hfree)) (by omega)
    (by unfold yLab midLab; split_ifs <;> omega) (by omega)
    (fun choice hsc => Or.inl (hsc.eq_some hurg (by omega) fun o ho => by
      obtain ⟨hoN, hof, hos, _⟩ := urgent_copy hp ho
      rcases hcover o hoN hof with h | h
      · rw [h] at hos
        exact (not_shared_14 hk hos).elim
      · omega)) fun s1 hg hc1 => ?_
  have hp1 : Placed (k + 16) (yTop k) s1 :=
    hp.grow hg hfree (by simp only [winTarget_length]; omega)
  have hreach1 : s1.reachable := win_reachable hp1 fun j hj hf hs => by
    rw [free_cover (yTInv k) (fun e => e = k + 14) (fun e he hs => yTInv_spec he hs) j hj hf] at hs
    exact (not_shared_14 hk hs).elim
  refine hp1.bound_step k s1 hreach1 (Or.inl (by omega)) (k + 13) (by omega)
    (by unfold yTop yLab midLab; split_ifs <;> omega) (by omega) (by omega)
    (by rw [hp1.pending]; simp only [winTarget_length]; omega)
    (by unfold yTop yLab midLab; split_ifs <;> omega)
    (fun s hs hsc _ => ?_) fun next hb hc => ?_
  · have h := yTop_unique hk hs hsc
    exact target_ne h.1 (by omega) h.2
  · exact cont next (hp1.boundSwaps hb |>.congr fun i hi => yTop_next hi) (by rw [hc, hc1]; simp)

-- A tail step: cursor u is bound to slot k + 14 and costs 2 swaps.
theorem late_step (hk : 3 ≤ k + b) (hu : k + 1 ≤ u) (hu2 : u ≤ k + 13)
    (hp : Placed (k + 16) lab state)
    (hfree : ∀ j < 17 + k, (∀ i < k + 16, lab i ≠ j) → j = k + 14)
    (hc : lab (k + 14) = u) (hnf : lab u ≠ u)
    (hunique : ∀ s < k + 16, s ≠ k + 14 → lab s ≠ s →
      lab s < 17 + k ∧ winVal b k (lab s) ≠ winVal b k u)
    (cont : ∀ next : State (winSource b k) (winTarget b k) (winSpills b k),
      Placed (k + 16) (boundLab (k + 16) (k + 14) u lab) next →
      next.trace.swapCount = state.trace.swapCount + 2 →
      Succeeds (buildBottomUp.loop (u + 1) next) post) :
    Succeeds (buildBottomUp.loop u state) post := by
  have hl := hp.length
  obtain ⟨hreach, hno, hpos⟩ := late_quiet (t := u) hk hp hfree
  refine hp.bound_step u state hreach (Or.inr ⟨hno, fun _ => hpos⟩) (k + 14) (by omega) hc
    (by omega) (by omega) (by rw [hp.pending]; simp only [winTarget_length]; omega) hnf
    (fun s hs hsc hns => ?_) fun next hb hcount => ?_
  · have h := hunique s hs hsc hns
    exact target_ne h.1 (by omega) h.2
  · exact cont next (hp.boundSwaps hb) (by rw [hcount]; simp)

end steps

theorem endB_diff (hk : 3 ≤ k + b) :
    endB k (k + 14) < 17 + k ∧ winVal b k (endB k (k + 14)) ≠ winVal b k (k + 14) := by
  unfold endB winVal cls; split_ifs <;> omega

-- Cursors k + 12 and k + 13 are bound steps, cursor k + 14 is a hole and the last
-- two slots form a 2-cycle.
theorem end_run (hk : 3 ≤ k + b) (hp : Placed (k + 16) (endLab k (k + 12)) state) :
    Succeeds (buildBottomUp.loop (k + 12) state)
      (fun r => r.2.swapCount = state.trace.swapCount + 6) := by
  refine late_step hk (by omega) (by omega) hp
    (free_cover (endInv k (k + 12)) (fun e => e = k + 14)
      fun e he hs => endInv_spec (by omega) le_rfl he hs)
    (by unfold endLab; split_ifs <;> omega) (by unfold endLab; split_ifs <;> omega)
    (fun s hs hsc hns => endLab_unique hk (by omega) le_rfl hs hsc hns) fun s1 hp1 hc1 => ?_
  replace hp1 := hp1.congr fun i hi => endLab_last hi
  refine late_step hk (by omega) le_rfl hp1
    (free_cover (endAInv k) (fun e => e = k + 14) fun e he hs => endAInv_spec he hs)
    (by simp [endA]) (by simp [endA]) (fun s hs hsc hns => endA_unique hk hs hsc hns)
    fun s2 hp2 hc2 => ?_
  replace hp2 := hp2.congr fun i hi => endA_next hi
  obtain ⟨hreach, hno, hpos⟩ := late_quiet (t := k + 14) hk hp2
    (free_cover (endBInv k) (fun e => e = k + 14) fun e he hs => endBInv_spec he hs)
  have hl := hp2.length
  have hN : k + 14 < (winTarget b k).length := by simp only [winTarget_length]; omega
  have hfree : s2.positionOfNat (k + 14) = none := (hp2.positionOf_none _).mpr fun i hi => by
    unfold endB; split_ifs <;> omega
  refine hp2.hole_step (k + 14) s2 hreach (Or.inr ⟨hno, fun _ => hpos⟩) (by omega) (by omega)
    (by simp only [winTarget_length]; omega) hfree
    (avail_of_reach hreach (symm_eq_none_of_positionOf hN hfree))
    (target_ne (endB_diff hk).1 (by omega) (endB_diff hk).2) fun s3 hp3 hc3 => ?_
  apply (hp3.permute_step (k + 15) s3 (by simp; omega) 1 le_rfl (by omega) (by omega)
    fun i hi => by simp only [endB]; split_ifs <;> omega).mono
  intro r hr
  rw [hr, hc3, hc2, hc1]
  split_ifs <;> omega

theorem tail_run (hk : 3 ≤ k + b) :
    ∀ n u (state : State (winSource b k) (winTarget b k) (winSpills b k)),
    u + n = k + 12 → k + 1 ≤ u → Placed (k + 16) (endLab k u) state →
    Succeeds (buildBottomUp.loop u state)
      (fun r => r.2.swapCount = state.trace.swapCount + 2 * n + 6) := by
  intro n
  induction n with
  | zero =>
    intro u state hu _ hp
    obtain rfl : u = k + 12 := by omega
    exact (end_run hk hp).mono fun r hr => by omega
  | succ n ih =>
    intro u state hu hu1 hp
    refine late_step hk hu1 (by omega) hp
      (free_cover (endInv k u) (fun e => e = k + 14)
        fun e he hs => endInv_spec hu1 (by omega) he hs)
      (by unfold endLab; split_ifs <;> omega) (by unfold endLab; split_ifs <;> omega)
      (fun s hs hsc hns => endLab_unique hk hu1 (by omega) hs hsc hns) fun next hp1 hc => ?_
    exact (ih (u + 1) next (by omega) (by omega)
      (hp1.congr fun i hi => endLab_next (by omega) hi)).mono fun r hr => by omega

theorem mid_run (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) (hx : b ≤ cls (k + b - 2))
    (hy : b ≤ cls (k + b - 1)) :
    ∀ n t (state : State (winSource b k) (winTarget b k) (winSpills b k)),
    t + 1 + n = k → 2 ≤ t + b → Placed (t + 15) (midLab t) state →
    Succeeds (buildBottomUp.loop t state)
      (fun r => r.2.swapCount = state.trace.swapCount + 2 * n + 32) := by
  intro n
  induction n with
  | zero =>
    intro t state ht _ hp
    obtain rfl : t = k - 1 := by omega
    rw [show k - 1 + 15 = k + 14 by omega] at hp
    refine shiftX_step hk hk2 hp fun s1 hp1 hc1 => ?_
    refine shiftY_step hk hk2 hp1 fun s2 hp2 hc2 => ?_
    exact (tail_run hk 11 (k + 1) s2 (by omega) le_rfl hp2).mono fun r hr => by omega
  | succ n ih =>
    intro t state ht ht2 hp
    refine mid_step hk ht2 (by omega) hx hy hp fun next hp1 hc => ?_
    exact (ih (t + 1) next (by omega) (by omega) hp1).mono fun r hr => by omega

section steps

variable {post : ((res : Stack) × Trace (winSpills b k) (winSource b k) res) → Prop}

-- A cursor t with t + b ≤ 1 among the 17 - b source slots: a bound step of 2 swaps. For
-- b = 0, slot 0 carries no shared value, so the 16 top slots hold a copy of both
-- shared values.
theorem head_step (hk : 3 ≤ k + b) (hx : b ≤ cls (k + b - 2)) (hy : b ≤ cls (k + b - 1))
    (t c : Nat) (hp : Placed (17 - b) lab state)
    (hrange : ∀ i < 17 - b, lab i < 17 - b) (hsurj : ∀ e < 17 - b, ∃ i < 17 - b, lab i = e)
    (h0 : b = 0 → ¬ Shared b k (lab 0 + b)) (hc : c < 16 - b) (hlab : lab c = t) (htc : t < c)
    (ht : t + b ≤ 1) (hnf : lab t ≠ t)
    (cont : ∀ next : State (winSource b k) (winTarget b k) (winSpills b k),
      Placed (17 - b) (boundLab (17 - b) c t lab) next →
      next.trace.swapCount = state.trace.swapCount + 2 →
      Succeeds (buildBottomUp.loop (t + 1) next) post) :
    Succeeds (buildBottomUp.loop t state) post := by
  have hreach : state.reachable := reach_head hp (by omega) hx hy fun e he hs => by
    obtain ⟨i, hi, hie⟩ := hsurj e (by omega)
    refine ⟨i, hi, ?_, hie⟩
    rcases Nat.eq_zero_or_pos b with hb | hb
    · have hi0 : i ≠ 0 := by
        rintro rfl
        exact h0 hb (by rw [hie]; exact hs)
      omega
    · omega
  refine hp.bound_step t state hreach (Or.inl (by omega)) c (by omega) hlab htc (by omega)
    (by rw [hp.pending]; simp only [winTarget_length]; omega) hnf
    (fun s hs hsc hns => target_ne (by have := hrange s hs; omega) (by omega) ?_)
    fun next hb hcount => cont next (hp.boundSwaps hb) (by
      rw [hcount]; split_ifs <;> omega)
  rw [winVal_head (by omega) (by have := hrange s hs; omega), winVal_head (by omega) (by omega)]
  intro he
  exact hsc (hp.inj s hs c (by omega) (by omega))

end steps

theorem not_shared_zero : ¬ Shared 0 k 0 := by unfold Shared cls; omega

-- From the source the loop spends 2 swaps on each cursor t with t + b ≤ 1, then the
-- middle phase starts at cursor 2 - b.
theorem win_run (hb : b ≤ 2) (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) (hx : b ≤ cls (k + b - 2))
    (hy : b ≤ cls (k + b - 1)) :
    Succeeds (buildBottomUp.loop 0 (winState b k)) (fun r => r.2.swapCount = 2 * k + 30) := by
  have hp := win_placed hb (by omega : 2 ≤ k + b)
  have hz : (winState b k).trace.swapCount = 0 := by simp [winState, Trace.swapCount]
  have hmid : ∀ t s, t + b = 2 → Placed (t + 15) (midLab t) s → s.trace.swapCount = 2 * t →
      Succeeds (buildBottomUp.loop t s) (fun r => r.2.swapCount = 2 * k + 30) :=
    fun t s ht hs hc =>
      (mid_run hk hk2 hx hy (k - 1 - t) t s (by omega) (by omega) hs).mono fun r hr => by omega
  obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  · cases hf : headB 0 k with
    | false =>
      rw [hf] at hp
      have hs : ¬ Shared 0 k (headLab 0 false 0 + 0) := by
        simp [headB] at hf
        rw [show headLab 0 false 0 + 0 = 2 from rfl]
        unfold Shared cls
        omega
      refine head_step hk hx hy 0 15 hp (by decide) (by decide) (fun _ => hs) (by omega) rfl
        (by omega) (by omega) (by decide) fun s1 hp1 hc1 => ?_
      refine head_step hk hx hy 1 15 hp1 (by decide) (by decide)
        (fun _ => by
          rw [show boundLab (17 - 0) 15 0 (headLab 0 false) 0 + 0 = 0 by decide]
          exact not_shared_zero)
        (by omega) (by decide) (by omega) (by omega) (by decide) fun s2 hp2 hc2 => ?_
      exact hmid 2 s2 rfl (hp2.congr (by decide)) (by rw [hc2, hc1, hz])
    | true =>
      rw [hf] at hp
      have hs : ¬ Shared 0 k (headLab 0 true 0 + 0) := by
        simp [headB] at hf
        rw [show headLab 0 true 0 + 0 = 16 from rfl]
        unfold Shared cls
        omega
      refine head_step hk hx hy 0 15 hp (by decide) (by decide) (fun _ => hs) (by omega) rfl
        (by omega) (by omega) (by decide) fun s1 hp1 hc1 => ?_
      refine head_step hk hx hy 1 14 hp1 (by decide) (by decide)
        (fun _ => by
          rw [show boundLab (17 - 0) 15 0 (headLab 0 true) 0 + 0 = 0 by decide]
          exact not_shared_zero)
        (by omega) (by decide) (by omega) (by omega) (by decide) fun s2 hp2 hc2 => ?_
      exact hmid 2 s2 rfl (hp2.congr (by decide)) (by rw [hc2, hc1, hz])
  · have hf : headB 1 k = false := by simp [headB]
    rw [hf] at hp
    refine head_step hk hx hy 0 14 hp (by decide) (by decide) (by omega) (by omega) rfl
      (by omega) (by omega) (by decide) fun s1 hp1 hc1 => ?_
    exact hmid 1 s1 rfl (hp1.congr (by decide)) (by rw [hc1, hz])
  · have hf : headB 2 k = false := by simp [headB]
    rw [hf] at hp
    exact hmid 0 _ rfl (hp.congr (by decide)) hz

theorem win_swapCount (hb : b ≤ 2) (hk : 3 ≤ k + b) (hk2 : 2 ≤ k) (hx : b ≤ cls (k + b - 2))
    (hy : b ≤ cls (k + b - 1)) :
    (buildBottomUp (winState b k) (win_valid hb hx hy)).map (·.2.swapCount) =
      .ok (2 * k + 30) := by
  obtain ⟨⟨res, trace⟩, hv, hc⟩ := win_run hb hk hk2 hx hy
  have hspec := loop_spec 0 (winState b k) (State.invariant.initial (win_valid hb hx hy))
  rw [hv] at hspec
  have hsize : res.length = (winTarget b k).length := by
    simp [show res = _ from hspec, State.expectedStack]
  unfold buildBottomUp
  rw [hv, except_ok_bind]
  simp only [requires_of_true _ hsize, except_ok_bind]
  simp only [Except.map, pure, Except.pure, Except.ok.injEq]
  exact hc

end Shuffler.Optimality.BBU
