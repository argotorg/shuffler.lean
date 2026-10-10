import Shuffler.BuildBottomUp.Optimality.Defs
import Shuffler.BuildBottomUp.Optimality.Lemmas.ActionCounts
import Shuffler.BuildBottomUp.Optimality.Lemmas.GeneralBound
import Shuffler.BuildBottomUp.Lemmas.StaticGeneration
import Shuffler.BuildBottomUp.Lemmas.ReachActions
import Shuffler.BuildBottomUp.Lemmas.ReachScan
import Shuffler.Permute.Theorems
import Mathlib.GroupTheory.Perm.Cycle.Concrete

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp Shuffler.Permute

-- The index that a swap of a and b moves to i.
def swapIdx (a b i : Nat) : Nat := if i = a then b else if i = b then a else i

theorem getElem?_swap_swapIdx (xs : List α) (a b i : Nat) (ha : a < xs.length)
    (hb : b < xs.length) : (xs.swap a b)[i]? = xs[swapIdx a b i]? := by
  by_cases hi : i < xs.length
  · have hs : swapIdx a b i < xs.length := by unfold swapIdx; split_ifs <;> omega
    rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem?_eq_getElem hs,
      List.getElem_swap]
    unfold swapIdx
    by_cases h1 : i = a
    · subst i; simp [hb]
    · by_cases h2 : i = b
      · subst i; simp [ha, h1]
      · simp [h1, h2]
  · have hs : ¬ swapIdx a b i < xs.length := by unfold swapIdx; split_ifs <;> omega
    rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by omega)]

variable {source target : Stack} {spills : SpillSet}

-- Slot i of the stack holds target[lab i]. Targets below len are bound and
-- the others are unbound, and every bound target keeps its value.
structure Labeled (len : Nat) (lab : Nat → Nat) (state : State source target spills) : Prop where
  length : state.stack.length = len
  range : ∀ i < len, lab i < len
  value : ∀ i < len, state.stack[i]? = target[lab i]?
  expected : state.expectedStack = target
  unbound : ∀ j : Fin target.length, state.mapping.symm j = none ↔ len ≤ j.val
  pending : state.pending_generations = target.length - len
  le : len ≤ target.length

theorem Labeled.congr {state : State source target spills} (h : Labeled len lab state)
    (heq : ∀ i < len, lab i = other i) : Labeled len other state :=
  ⟨h.length, fun i hi => heq i hi ▸ h.range i hi, fun i hi => heq i hi ▸ h.value i hi,
    h.expected, h.unbound, h.pending, h.le⟩

theorem Labeled.getElem {state : State source target spills} (h : Labeled len lab state)
    (i : Nat) (hi : i < state.stack.length) :
    state.stack[i] = target[lab i]'(by have := h.range i (h.length ▸ hi); have := h.le; omega) := by
  have hv := h.value i (h.length ▸ hi)
  have hr := h.range i (h.length ▸ hi)
  have hl := h.le
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at hv
  exact Option.some.inj hv

-- With distinct target values, the slot bound to target j carries label j.
theorem Labeled.position {state : State source target spills} (h : Labeled len lab state)
    (hnodup : target.Nodup) (j : Fin target.length) (hj : j.val < len) :
    ∃ pos : Fin state.stack.length, state.mapping.symm j = some pos ∧ lab pos.val = j.val := by
  cases hb : state.mapping.symm j with
  | none => exact absurd ((h.unbound j).mp hb) (by omega)
  | some pos =>
    refine ⟨pos, rfl, ?_⟩
    have he := congrArg (fun stack : Stack => stack[j.val]?) h.expected
    simp only [State.expectedStack, List.getElem?_ofFn, hb] at he
    have hv := h.getElem pos.val pos.isLt
    have hr := h.range pos.val (h.length ▸ pos.isLt)
    have hl := h.le
    rw [List.getElem?_eq_getElem j.isLt] at he
    simp only [j.isLt, dite_true, Option.some.injEq, Fin.getElem_fin] at he
    rw [hv] at he
    exact (List.Nodup.getElem_inj_iff hnodup).mp he

theorem Labeled.swap {state next : State source target spills} {pos : Fin state.stack.length}
    (h : Labeled len lab state) (hs : Swapped state next pos) :
    Labeled len (fun i => lab (swapIdx pos (len - 1) i)) next := by
  have hl := h.length
  have hp := pos.isLt
  have hidx (i : Nat) (hi : i < len) : swapIdx pos (len - 1) i < len := by
    unfold swapIdx; split_ifs <;> omega
  refine ⟨hs.size.trans hl, fun i hi => h.range _ (hidx i hi), fun i hi => ?_,
    hs.expected.trans h.expected, fun j => (hs.unbound j).trans (h.unbound j),
    hs.pending.trans h.pending, h.le⟩
  rw [hs.stack_eq, getElem?_swap_swapIdx _ _ _ _ pos.isLt (by omega),
    show state.stack.length - 1 = len - 1 by omega]
  exact h.value _ (hidx i hi)

theorem Labeled.grow {state next : State source target spills} {dest : Fin target.length}
    (h : Labeled len lab state) (hg : Generation state next dest) (hd : dest.val = len) :
    Labeled (len + 1) (fun i => if i = len then len else lab i) next := by
  have hl := h.length
  have hstack : next.stack = state.stack ++ [target[dest]] := by
    rcases hg.stack_eq with he | he
    · exact he
    · rw [he, show state.stack.length = dest.val by omega, List.swap_self]
  refine ⟨hg.size.trans (by omega), fun i hi => ?_, fun i hi => ?_,
    hg.expected.trans h.expected, fun j => ?_, ?_, by omega⟩
  · split_ifs with he
    · omega
    · have := h.range i (by omega); omega
  · rw [hstack]
    by_cases he : i = len
    · subst i
      simp [hl, hd]
    · rw [ite_eq_right he, List.getElem?_append_left (by omega)]
      exact h.value i (by omega)
  · rw [hg.unbound j, h.unbound j, ne_eq, Fin.ext_iff, hd]
    omega
  · rw [hg.pending, h.pending]
    omega

def LabInj (len : Nat) (lab : Nat → Nat) : Prop := ∀ i < len, ∀ j < len, lab i = lab j → i = j

theorem Labeled.mapping_apply {state : State source target spills} (h : Labeled len lab state)
    (hnodup : target.Nodup) (hinj : LabInj len lab) (i : Fin state.stack.length) :
    state.mapping i = some ⟨lab i.val, by
      have := h.range i.val (h.length ▸ i.isLt); have := h.le; omega⟩ := by
  have hlen := h.length
  have hr := h.range i.val (by omega)
  have hl := h.le
  obtain ⟨pos, hpos, hlab⟩ := h.position hnodup ⟨lab i.val, by omega⟩ hr
  have he : pos = i := Fin.ext (hinj _ (by omega) _ (by omega) hlab)
  subst he
  exact state.mapping.eq_some_iff.mp hpos

-- Every target value is a spilled variable, so each one can be loaded.
def AllSpilled (target : Stack) (spills : SpillSet) : Prop :=
  ∀ j : Fin target.length, spills.is_spilled target[j]

theorem AllSpilled.available (h : AllSpilled target spills) (state : State source target spills)
    (j : Fin target.length) : state.isAvailable j :=
  Or.inr (Or.inl (h j))

theorem AllSpilled.reachable (h : AllSpilled target spills) (state : State source target spills) :
    state.reachable :=
  fun j _ => Or.inr (Or.inl (h j))

theorem AllSpilled.no_urgent (h : AllSpilled target spills) {state : State source target spills}
    {choice : Option Nat} (hp : ScanProgress cursor state seen choice) : choice = none := by
  cases choice with
  | none => rfl
  | some offset =>
    obtain ⟨hlt, _, _, hns, _⟩ := hp.selected offset rfl
    exact (hns (h ⟨offset, hlt⟩)).elim

def boundLab (len c t : Nat) (lab : Nat → Nat) (i : Nat) : Nat :=
  if c = len - 1 then lab (swapIdx t (len - 1) i)
  else lab (swapIdx c (len - 1) (swapIdx t (len - 1) i))

-- The bound slot c for cursor t is above t. Values are distinct, so the
-- copy scan keeps c. The step swaps c to the top if needed, then swaps t.
theorem reach_of_fit (stack : Stack) (pos : Fin stack.length) (h : stack.length ≤ pos.val + 17) :
    stack.isSwapReachable pos := by
  simp only [Stack.isSwapReachable, Stack.offsetToDepth, MAX_SWAP_DEPTH]
  omega

-- positionOf over any target offset, as a stack offset.
def _root_.Shuffler.BuildBottomUp.State.positionOfNat (state : State source target spills)
    (offset : Nat) : Option Nat :=
  if h : offset < target.length then (state.positionOf ⟨offset, h⟩).map Fin.val else none

theorem positionOfNat_eq_some {state : State source target spills}
    (h : state.positionOfNat j = some p) :
    ∃ hj : j < target.length, ∃ hp : p < state.stack.length,
      state.positionOf ⟨j, hj⟩ = some ⟨p, hp⟩ := by
  unfold State.positionOfNat at h
  split at h
  · rename_i hj
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hj, q.isLt, hq⟩
  · cases h

theorem positionOf_some {state : State source target spills} (h : state.positionOfNat j = some p) :
    ∃ hj : j < target.length, ∃ hp : p < state.stack.length,
      state.mapping ⟨p, hp⟩ = some ⟨j, hj⟩ := by
  obtain ⟨hj, hp, hq⟩ := positionOfNat_eq_some h
  exact ⟨hj, hp, state.mapping.eq_some_iff.mp hq⟩

theorem positionOf_inj {state : State source target spills} (ha : state.positionOfNat a = some p)
    (hb : state.positionOfNat b = some p) : a = b := by
  obtain ⟨_, _, ha⟩ := positionOf_some ha
  obtain ⟨_, _, hb⟩ := positionOf_some hb
  rw [ha] at hb
  simpa using hb

theorem isFinal_iff_positionOf (state : State source target spills) (j : Nat) :
    (∃ h, state.isFinal ⟨j, h⟩) ↔ state.positionOfNat j = some j := by
  rw [State.exists_isFinal_iff]
  unfold State.positionOfNat State.positionOf
  split <;> simp

-- Slot i holds target[lab i] and is bound to it. The labels need not be
-- below len, and target values may repeat.
structure Placed (len : Nat) (lab : Nat → Nat) (state : State source target spills) : Prop where
  length : state.stack.length = len
  value : ∀ i < len, state.stack[i]? = target[lab i]?
  slot : ∀ i < len, state.positionOfNat (lab i) = some i
  expected : state.expectedStack = target
  pending : state.pending_generations = target.length - len
  le : len ≤ target.length

namespace Placed

variable {state : State source target spills} {len : Nat} {lab : Nat → Nat}

theorem congr (h : Placed len lab state) (heq : ∀ i < len, lab i = other i) :
    Placed len other state :=
  ⟨h.length, fun i hi => heq i hi ▸ h.value i hi, fun i hi => heq i hi ▸ h.slot i hi,
    h.expected, h.pending, h.le⟩

theorem range (h : Placed len lab state) (i : Nat) (hi : i < len) : lab i < target.length :=
  (positionOf_some (h.slot i hi)).1

theorem getElem (h : Placed len lab state) (i : Nat) (hi : i < state.stack.length) :
    state.stack[i] = target[lab i]'(h.range i (h.length ▸ hi)) := by
  have hv := h.value i (h.length ▸ hi)
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (h.range i (h.length ▸ hi))] at hv
  exact Option.some.inj hv

theorem inj (h : Placed len lab state) : LabInj len lab := fun i hi j hj he => by
  have := h.slot i hi
  rw [he, h.slot j hj] at this
  exact (Option.some.inj this).symm

theorem isFinal_iff (h : Placed len lab state) (j : Nat) (hj : j < len) :
    (∃ h, state.isFinal ⟨j, h⟩) ↔ lab j = j := by
  rw [isFinal_iff_positionOf]
  constructor
  · intro hp
    exact positionOf_inj (h.slot j hj) hp
  · intro he
    simpa [he] using h.slot j hj

theorem positionOf_none (h : Placed len lab state) (j : Nat) :
    state.positionOfNat j = none ↔ ∀ i < len, lab i ≠ j := by
  constructor
  · intro hn i hi he
    rw [← he, h.slot i hi] at hn
    cases hn
  · intro hne
    cases hp : state.positionOfNat j with
    | none => rfl
    | some p =>
      obtain ⟨_, hpl, _⟩ := positionOf_some hp
      exact absurd (positionOf_inj (h.slot p (h.length ▸ hpl)) hp) (hne p (h.length ▸ hpl))

theorem unbound (h : Placed len lab state) (j : Fin target.length) :
    state.mapping.symm j = none ↔ ∀ i < len, lab i ≠ j.val := by
  rw [← h.positionOf_none]
  simp [State.positionOfNat, State.positionOf, j.isLt]

theorem mapping_apply (h : Placed len lab state) (i : Fin state.stack.length) :
    state.mapping i = some ⟨lab i.val, h.range i.val (h.length ▸ i.isLt)⟩ := by
  obtain ⟨_, _, hm⟩ := positionOf_some (h.slot i.val (h.length ▸ i.isLt))
  exact hm

end Placed

theorem Labeled.placed {state : State source target spills} (h : Labeled len lab state)
    (hnodup : target.Nodup) (hinj : LabInj len lab) : Placed len lab state where
  length := h.length
  value := h.value
  slot i hi := by
    have hm := h.mapping_apply hnodup hinj ⟨i, h.length ▸ hi⟩
    have hs := state.mapping.eq_some_iff.mpr hm
    have := h.range i hi
    have := h.le
    simp [State.positionOfNat, State.positionOf, show lab i < target.length by omega, hs]
  expected := h.expected
  pending := h.pending
  le := h.le

theorem _root_.Shuffler.BuildBottomUp.Swapped.positionOf {state next : State source target spills} {pos : Fin state.stack.length}
    (hs : Swapped state next pos) (j : Nat) :
    next.positionOfNat j = (state.positionOfNat j).map (swapIdx pos (state.stack.length - 1)) := by
  unfold State.positionOfNat State.positionOf
  split
  · rename_i hj
    rw [hs.mapping ⟨j, hj⟩, Mapping.swapDestinations_symm_apply]
    cases state.mapping.symm ⟨j, hj⟩ with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.some.injEq, swapIdx, Equiv.swap_apply_def]
      split_ifs <;> simp_all [Fin.ext_iff]
  · rfl

theorem swapIdx_swapIdx (a b i : Nat) : swapIdx a b (swapIdx a b i) = i := by
  unfold swapIdx; split_ifs <;> omega

theorem Placed.swap {state next : State source target spills} {pos : Fin state.stack.length}
    (h : Placed len lab state) (hs : Swapped state next pos) :
    Placed len (fun i => lab (swapIdx pos (len - 1) i)) next := by
  have hl := h.length
  have hp := pos.isLt
  have hidx (i : Nat) (hi : i < len) : swapIdx pos (len - 1) i < len := by
    unfold swapIdx; split_ifs <;> omega
  refine ⟨hs.size.trans hl, fun i hi => ?_, fun i hi => ?_, hs.expected.trans h.expected,
    hs.pending.trans h.pending, h.le⟩
  · rw [hs.stack_eq, getElem?_swap_swapIdx _ _ _ _ pos.isLt (by omega),
      show state.stack.length - 1 = len - 1 by omega]
    exact h.value _ (hidx i hi)
  · rw [hs.positionOf, h.slot _ (hidx i hi), Option.map_some,
      show state.stack.length - 1 = len - 1 by omega, swapIdx_swapIdx]

theorem _root_.Shuffler.BuildBottomUp.Growth.positionOf_ne {state next : State source target spills} {dest : Fin target.length}
    (hg : Growth state next dest pending) (j : Nat) (hj : j ≠ dest.val) :
    next.positionOfNat j = state.positionOfNat j := by
  unfold State.positionOfNat State.positionOf
  split
  · rename_i hlt
    exact hg.others ⟨j, hlt⟩ (fun he => hj (congrArg Fin.val he))
  · rfl

theorem Placed.grow {state next : State source target spills} {dest : Fin target.length}
    (h : Placed len lab state) (hg : Growth state next dest (state.pending_generations - 1))
    (hfree : state.positionOfNat dest.val = none) (hlt : len < target.length) :
    Placed (len + 1) (fun i => if i = len then dest.val else lab i) next := by
  have hl := h.length
  refine ⟨hg.size.trans (by omega), fun i hi => ?_, fun i hi => ?_,
    hg.expected.trans h.expected, ?_, by omega⟩
  · rw [hg.stack_eq]
    by_cases he : i = len
    · subst i
      simp [hl]
    · rw [ite_eq_right he, List.getElem?_append_left (by omega)]
      exact h.value i (by omega)
  · by_cases he : i = len
    · subst i
      simpa [State.positionOfNat, dest.isLt, hl, hg.size] using hg.top
    · rw [ite_eq_right he]
      have hne : lab i ≠ dest.val := (h.positionOf_none _).mp hfree i (by omega)
      rw [hg.positionOf_ne _ hne]
      exact h.slot i (by omega)
  · rw [hg.pending_eq, h.pending]
    omega

theorem produce_swaps {state next : State source target spills} {dest : Fin target.length}
    (h : state.produce dest = .ok next) : next.trace.swapCount = state.trace.swapCount := by
  have hp := (produce_swapCount_triple state dest).le_wp trivial
  rw [h] at hp
  exact hp

theorem generate_eq_after_produce_above (state produced : State source target spills)
    (dest : Fin target.length) (he : state.produce dest = .ok produced)
    (hge : produced.stack.length ≤ dest.val + 1) :
    state.generate dest.val = .ok produced := by
  unfold State.generate
  simp_loop
  rw [index_eq dest, except_ok_bind, he, except_ok_bind,
    ite_eq_right (show ¬dest.val + 1 < produced.stack.length by omega)]
  rfl

theorem generate_eq_after_produce_swap (state produced : State source target spills)
    (dest : Fin target.length)
    (he : state.produce dest = .ok produced)
    (current top : Fin produced.stack.length)
    (hc : current.val = dest.val) (ht : top.val = produced.stack.length - 1)
    (hbelow : current.val + 1 < produced.stack.length)
    (hb : produced.mapping.symm dest = some top)
    (hv : produced.stack[current] ≠ produced.stack[top])
    (hreach : produced.stack.isSwapReachable current) :
    state.generate dest.val = produced.swapWith dest.val := by
  have hn : ¬ ∃ h, produced.isFinal ⟨current, h⟩ := by
    rw [hc, produced.isFinal_of_bound_iff dest top hb]
    omega
  unfold State.generate
  simp_loop
  rw [index_eq dest, except_ok_bind, he, except_ok_bind,
    ite_eq_left (show dest.val + 1 < produced.stack.length by omega),
    ← hc, index_eq current, except_ok_bind, ite_eq_left ((produced.isFinal_iff current).not.mpr hn)]
  rw [slotAt_index produced.stack current, ← ht, slotAt_index produced.stack top]
  simp_loop
  rw [ite_eq_right hv,
    ite_eq_left (show produced.isSwapReachable current from hreach)]
  simp only [bind_pure]

-- The swaps of a bound step for cursor t with bound slot c: c to the top if
-- needed, then t with the top.
def BoundSwaps (state next : State source target spills) (len c t : Nat) : Prop :=
  if c = len - 1 then ∃ h, Swapped state next ⟨t, h⟩
  else ∃ mid, (∃ h, Swapped state mid ⟨c, h⟩) ∧ ∃ h, Swapped mid next ⟨t, h⟩

theorem Placed.boundSwaps {state next : State source target spills} (h : Placed len lab state)
    (hb : BoundSwaps state next len c t) : Placed len (boundLab len c t lab) next := by
  unfold BoundSwaps at hb
  split_ifs at hb with hc
  · obtain ⟨_, hs⟩ := hb
    exact (h.swap hs).congr fun i _ => by simp [boundLab, hc]
  · obtain ⟨mid, ⟨_, h1⟩, _, h2⟩ := hb
    exact ((h.swap h1).swap h2).congr fun i _ => by simp [boundLab, hc]

theorem Labeled.boundSwaps {state next : State source target spills} (h : Labeled len lab state)
    (hb : BoundSwaps state next len c t) : Labeled len (boundLab len c t lab) next := by
  unfold BoundSwaps at hb
  split_ifs at hb with hc
  · obtain ⟨_, hs⟩ := hb
    exact (h.swap hs).congr fun i _ => by simp [boundLab, hc]
  · obtain ⟨mid, ⟨_, h1⟩, _, h2⟩ := hb
    exact ((h.swap h1).swap h2).congr fun i _ => by simp [boundLab, hc]

-- The last part of a bound step: SWAP the slot at t with the top.
theorem swap_tail {post : ((res : Stack) × Trace spills source res) → Prop}
    (t : Nat) (state : State source target spills) (hnft : ¬ ∃ h, state.isFinal ⟨t, h⟩)
    (htl : t + 1 < state.stack.length) (hfit : state.stack.length ≤ t + 17)
    (cont : ∀ next, (∃ h, Swapped state next ⟨t, h⟩) →
      next.trace.swapCount = state.trace.swapCount + 1 →
      Succeeds (buildBottomUp.loop (t + 1) next) post) :
    Succeeds (do
      let __do_lift ← index state.stack.length t
      let _ ← requires (¬ state.isFinal __do_lift) "target slot is already final"
      if t ≠ state.stack.length - 1 then do
        let __do_lift ← index state.stack.length t
        if ¬ state.isSwapReachable __do_lift then do
          let __do_lift ← index state.stack.length t
          throw (Error.blocked (↑(state.depthOf __do_lift) - MAX_SWAP_DEPTH))
          let state ← state.swapWith t
          buildBottomUp.loop (t + 1) state
        else do
          let state ← state.swapWith t
          buildBottomUp.loop (t + 1) state
      else buildBottomUp.loop (t + 1) state) post := by
  let current : Fin state.stack.length := ⟨t, by omega⟩
  have hreach := reach_of_fit state.stack current (by simp only [current]; omega)
  rw [index_eq current, except_ok_bind,
    requires_of_true _ ((state.isFinal_iff current).not.mpr hnft), except_ok_bind]
  simp only [show t ≠ state.stack.length - 1 by omega, ne_eq, not_false_eq_true, ↓reduceIte]
  rw [except_ok_bind,
    ite_eq_right (not_not_intro (show state.isSwapReachable current from hreach))]
  obtain ⟨next, heq, hs⟩ := swap_success state current (by simp only [current]; omega) hreach
    (fun hf => hnft ⟨_, hf⟩)
  rw [heq, except_ok_bind]
  exact cont next ⟨_, hs⟩ (swap_counts _ _ _ heq).swaps

-- Cursor t is bound to slot c above it. No other open slot holds the value of
-- target t, so the copy scan keeps c. No generation happens.
theorem Placed.bound_step
    {post : ((res : Stack) × Trace spills source res) → Prop}
    (t : Nat) (state : State source target spills) (hp : Placed len lab state)
    (hreach : state.reachable)
    (hstay : t + 16 ≤ len ∨
      ((∀ o, ¬Urgent t state o) ∧ (len < target.length → state.positionOfNat len ≠ none)))
    (c : Nat) (hc : c < len) (hlab : lab c = t) (htc : t < c) (hfit : len ≤ t + 17)
    (hpend : state.pending_generations ≠ 0) (hnfinal : lab t ≠ t)
    (hunique : ∀ s < len, s ≠ c → lab s ≠ s → target[lab s]? ≠ target[t]?)
    (cont : ∀ next, BoundSwaps state next len c t →
      next.trace.swapCount = state.trace.swapCount + (if c = len - 1 then 1 else 2) →
      Succeeds (buildBottomUp.loop (t + 1) next) post) :
    Succeeds (buildBottomUp.loop t state) post := by
  have hlen := hp.length
  have hct : t < target.length := hlab ▸ hp.range c hc
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  simp only [show ¬t ≥ target.length by omega, ↓reduceIte]
  have hnft : ¬ ∃ h, state.isFinal ⟨t, h⟩ := by rw [hp.isFinal_iff _ (by omega)]; exact hnfinal
  rw [skip_unless_final (fun hlt => (state.isFinal_iff ⟨t, hlt⟩).not.mpr hnft)]
  simp only [hpend, ↓reduceIte]
  have hscan := Succeeds.of_triple _ _ (urgentScan_success t state hreach)
  simp only [bind_pure] at hscan
  apply hscan.bind
  intro urgent hu
  have h1 : ¬(urgent.isSome ∧ urgent ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) := by
    rintro ⟨hs, _, hw⟩
    rcases hstay with hw' | ⟨hno, _⟩
    · unfold MAX_SWAP_DEPTH at hw; omega
    · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hs
      exact hno o (hu.selected o ho)
  rw [dite_eq_right h1]
  apply Succeeds.ite_index (fun hA => hA.2.2)
  · rintro ⟨_, _, hlt⟩ ⟨hnone, hw⟩
    rcases hstay with hw' | ⟨_, hpos⟩
    · unfold MAX_SWAP_DEPTH at hw; omega
    · exact (hpos (by omega) (by rw [← hlen]; simpa [State.positionOfNat, hlt] using hnone)).elim
  obtain ⟨_, hcl, hposition⟩ := positionOfNat_eq_some (hlab ▸ hp.slot c hc)
  obtain ⟨carrier, rfl⟩ : ∃ carrier : Fin state.stack.length, carrier.val = c := ⟨⟨c, hcl⟩, rfl⟩
  let dest : Fin target.length := ⟨t, hct⟩
  rw [index_eq dest, except_ok_bind]
  simp only [dest, show state.positionOf ⟨t, hct⟩ = some carrier from hposition]
  rw [requires_of_true _ (show carrier.val ≥ t by omega), except_ok_bind]
  let current : Fin state.stack.length := ⟨t, by omega⟩
  rw [slotAt_index state.stack current, slotAt_index state.stack carrier]
  simp only [except_ok_bind]
  have hnfc : ¬ state.isFinal carrier := by
    rw [State.isFinal_iff, hp.isFinal_iff _ hc]; omega
  have hcv : state.stack[carrier] = target[t] := by
    simp only [Fin.getElem_fin, hp.getElem, hlab]
  have hsame (s : Fin state.stack.length) (hs : state.stack[s] = state.stack[carrier])
      (hns : ¬ state.isFinal s) : s = carrier := by
    by_contra hne
    have hne' : s.val ≠ carrier.val := fun he => hne (Fin.ext he)
    have hsl : s.val < len := hlen ▸ s.isLt
    rw [State.isFinal_iff, hp.isFinal_iff _ hsl] at hns
    apply hunique s.val hsl hne' hns
    rw [List.getElem?_eq_getElem (hp.range _ hsl), List.getElem?_eq_getElem hct]
    rw [hcv, Fin.getElem_fin, hp.getElem] at hs
    exact congrArg some hs
  have hdiff : ¬ state.stack[current] = state.stack[carrier] := by
    intro he
    have := congrArg Fin.val (hsame current he (by
      rw [State.isFinal_iff, hp.isFinal_iff _ (by omega)]; exact hnfinal))
    simp only [current] at this
    omega
  rw [ite_eq_right hdiff, index_eq carrier, except_ok_bind]
  have hscan := Succeeds.of_triple _ _ (copyScan_success state carrier carrier.val
    ⟨carrier, rfl, rfl, hnfc⟩)
  simp only [except_ok_bind, bind_pure, slotAt_index state.stack carrier] at hscan
  apply hscan.bind
  intro selected hselected
  obtain ⟨pos, rfl, hequal, hnpos⟩ := hselected
  have hpc : pos = carrier := hsame pos hequal hnpos
  subst pos
  rw [slotAt_index state.stack carrier, except_ok_bind, requires_of_true _ rfl, except_ok_bind,
    swapDestinations_result state carrier carrier, except_ok_bind]
  rw [Mapping.swapDestinations_self]
  simp only [show carrier.val ≠ t by omega, ↓reduceIte]
  have heta : (⟨state.planned_mapping, state.stack, state.trace, state.mapping,
      state.pending_generations⟩ : State source target spills) = state := rfl
  simp only [heta]
  have hnft : ¬ ∃ h, state.isFinal ⟨t, h⟩ := by rw [hp.isFinal_iff _ (by omega)]; exact hnfinal
  by_cases hctop : carrier.val = len - 1
  · simp only [show ¬(carrier.val ≠ state.stack.length - 1) by omega, ↓reduceIte]
    refine swap_tail t state hnft (by omega) (by omega) fun next hn hcount => ?_
    refine cont next ?_ (by simp only [hcount, hctop, ↓reduceIte])
    simpa only [BoundSwaps, hctop, ↓reduceIte] using hn
  · simp only [show carrier.val ≠ state.stack.length - 1 by omega, ne_eq, not_false_eq_true,
      ↓reduceIte]
    have hreach := reach_of_fit state.stack carrier (by omega)
    rw [index_eq carrier, except_ok_bind,
      ite_eq_right (not_not_intro (show state.isSwapReachable carrier from hreach))]
    obtain ⟨s1, heq, hs⟩ := swap_success state carrier (by omega) hreach hnfc
    rw [heq, except_ok_bind]
    have hp1 := hp.swap hs
    have hfix : swapIdx carrier (len - 1) t = t := by unfold swapIdx; split_ifs <;> omega
    have hnft1 : ¬ ∃ h, s1.isFinal ⟨t, h⟩ := by
      rw [hp1.isFinal_iff _ (by omega), hfix]; exact hnfinal
    have hl1 := hs.size
    refine swap_tail t s1 hnft1 (by omega) (by omega) fun next hn hcount => ?_
    refine cont next ?_ ?_
    · simp only [BoundSwaps, hctop, ↓reduceIte]
      exact ⟨s1, ⟨_, hs⟩, hn⟩
    · simp only [hcount, (swap_counts _ _ _ heq).swaps, hctop, ↓reduceIte]

theorem generate_above_success (state : State source target spills) (dest : Fin target.length)
    (hb : state.mapping.symm dest = none) (ha : state.isAvailable dest) (hr : state.reachable)
    (hge : state.stack.length ≤ dest.val) :
    ∃ next, state.generate dest.val = .ok next ∧
      Growth state next dest (state.pending_generations - 1) ∧
      next.trace.swapCount = state.trace.swapCount := by
  obtain ⟨next, he, hg, _⟩ := produce_success_exact state dest hb ha hr
  exact ⟨next, generate_eq_after_produce_above _ _ _ he (by rw [hg.size]; omega), hg,
    produce_swaps he⟩

theorem symm_eq_none_of_positionOf {state : State source target spills} {j : Nat}
    (hj : j < target.length) (h : state.positionOfNat j = none) :
    state.mapping.symm ⟨j, hj⟩ = none := by
  simpa [State.positionOfNat, State.positionOf, hj] using h

-- The loop generates target d at the top, by the urgent scan or as the next
-- target above the stack. No swap happens.
theorem Placed.gen_step
    {post : ((res : Stack) × Trace spills source res) → Prop}
    (t : Nat) (state : State source target spills) (hp : Placed len lab state)
    (hreach : state.reachable) (d : Nat) (hd : len ≤ d) (hdN : d < target.length)
    (hfree : state.positionOfNat d = none) (havail : state.isAvailable ⟨d, hdN⟩)
    (htl : t < len) (hnfinal : lab t ≠ t) (hnear : len < t + 16)
    (hchoice : ∀ choice, ScanProgress t state (List.range' t (target.length - t)) choice →
      choice = some d ∨ (choice = none ∧ d = len))
    (cont : ∀ next, Growth state next ⟨d, hdN⟩ (state.pending_generations - 1) →
      next.trace.swapCount = state.trace.swapCount →
      Succeeds (buildBottomUp.loop t next) post) :
    Succeeds (buildBottomUp.loop t state) post := by
  have hlen := hp.length
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  simp only [show ¬t ≥ target.length by omega, ↓reduceIte]
  have hnft : ¬ ∃ h, state.isFinal ⟨t, h⟩ := by rw [hp.isFinal_iff t htl]; exact hnfinal
  rw [skip_unless_final (fun hlt => (state.isFinal_iff ⟨t, hlt⟩).not.mpr hnft)]
  have hpend : state.pending_generations ≠ 0 := by rw [hp.pending]; omega
  simp only [hpend, ↓reduceIte]
  have hscan := Succeeds.of_triple _ _ (urgentScan_success t state hreach)
  simp only [bind_pure] at hscan
  apply hscan.bind
  intro urgent hu
  have hnear' : state.stack.length - t < MAX_SWAP_DEPTH := by unfold MAX_SWAP_DEPTH; omega
  obtain ⟨next, heq, hg, hcount⟩ := generate_above_success state ⟨d, hdN⟩
    (symm_eq_none_of_positionOf hdN hfree) havail hreach (by simp only; omega)
  have hgen : Succeeds (state.generate d) (· = next) := ⟨next, heq, rfl⟩
  rcases hchoice urgent hu with rfl | ⟨rfl, rfl⟩
  · rw [dite_eq_left ⟨rfl, by simp only [ne_eq, Option.some.injEq]; omega, hnear'⟩]
    apply hgen.attach.bind
    rintro ⟨_, _⟩ rfl
    exact cont _ hg hcount
  · rw [dite_eq_right (by simp), ite_eq_left ⟨rfl, by omega, by omega⟩,
      index_eq ⟨state.stack.length, by omega⟩, except_ok_bind,
      ite_eq_left ⟨by simpa [State.positionOfNat, hlen, hdN] using hfree,
        by unfold MAX_SWAP_DEPTH; omega⟩]
    apply (show Succeeds (state.generate state.stack.length) (· = next) by
      rw [hlen]; exact hgen).attach.bind
    rintro ⟨_, _⟩ rfl
    exact cont _ hg hcount

-- Cursor t has no bound slot. The loop generates target t at the top and
-- swaps it into slot t at once.
theorem Placed.hole_step
    {post : ((res : Stack) × Trace spills source res) → Prop}
    (t : Nat) (state : State source target spills) (hp : Placed len lab state)
    (hreach : state.reachable)
    (hstay : t + 16 ≤ len ∨
      ((∀ o, ¬Urgent t state o) ∧ (len < target.length → state.positionOfNat len ≠ none)))
    (htl : t < len) (hfit : len + 1 ≤ t + 17) (hlt : len < target.length)
    (hfree : state.positionOfNat t = none) (havail : state.isAvailable ⟨t, by omega⟩)
    (hdiff : target[lab t]? ≠ target[t]?)
    (cont : ∀ next : State source target spills,
      Placed (len + 1) (fun i => if i = t then t else if i = len then lab t else lab i) next →
      next.trace.swapCount = state.trace.swapCount + 1 →
      Succeeds (buildBottomUp.loop (t + 1) next) post) :
    Succeeds (buildBottomUp.loop t state) post := by
  have hlen := hp.length
  have hct : t < target.length := by omega
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  simp only [show ¬t ≥ target.length by omega, ↓reduceIte]
  have hnft : ¬ ∃ h, state.isFinal ⟨t, h⟩ := by
    rw [isFinal_iff_positionOf, hfree]
    simp
  rw [skip_unless_final (fun hlt => (state.isFinal_iff ⟨t, hlt⟩).not.mpr hnft)]
  have hpend : state.pending_generations ≠ 0 := by rw [hp.pending]; omega
  simp only [hpend, ↓reduceIte]
  have hscan := Succeeds.of_triple _ _ (urgentScan_success t state hreach)
  simp only [bind_pure] at hscan
  apply hscan.bind
  intro urgent hu
  have h1 : ¬(urgent.isSome ∧ urgent ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) := by
    rintro ⟨hs, _, hw⟩
    rcases hstay with hw' | ⟨hno, _⟩
    · unfold MAX_SWAP_DEPTH at hw; omega
    · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hs
      exact hno o (hu.selected o ho)
  rw [dite_eq_right h1]
  apply Succeeds.ite_index (fun hA => hA.2.2)
  · rintro ⟨_, _, hlt⟩ ⟨hnone, hw⟩
    rcases hstay with hw' | ⟨_, hpos⟩
    · unfold MAX_SWAP_DEPTH at hw; omega
    · exact (hpos (by omega) (by rw [← hlen]; simpa [State.positionOfNat, hlt] using hnone)).elim
  have hfree' := symm_eq_none_of_positionOf hct hfree
  rw [index_eq ⟨t, hct⟩, except_ok_bind]
  simp only [show state.positionOf ⟨t, hct⟩ = none from hfree']
  obtain ⟨mid, he, hg, _⟩ := produce_success_exact state ⟨t, hct⟩ hfree' havail hreach
  have hpm := hp.grow hg hfree hlt
  have hml : mid.stack.length = len + 1 := by rw [hg.size, hlen]
  let current : Fin mid.stack.length := ⟨t, by omega⟩
  let top : Fin mid.stack.length := ⟨len, by omega⟩
  have hb : mid.mapping.symm ⟨t, hct⟩ = some top := by
    have hs := hpm.slot len (by omega)
    simp only [↓reduceIte] at hs
    obtain ⟨_, _, hm⟩ := positionOf_some hs
    exact mid.mapping.eq_some_iff.mpr hm
  have hv : mid.stack[current] ≠ mid.stack[top] := by
    intro heq
    apply hdiff
    have h1 := hpm.getElem t (by omega)
    have h2 := hpm.getElem len (by omega)
    simp only [show t ≠ len by omega, ↓reduceIte] at h1 h2
    rw [List.getElem?_eq_getElem (hp.range t htl), List.getElem?_eq_getElem hct,
      ← h1, ← h2]
    exact congrArg some heq
  have hr := reach_of_fit mid.stack current (by simp only [current]; omega)
  have hnf : ¬ ∃ h, mid.isFinal ⟨t, h⟩ := by
    rw [hpm.isFinal_iff t (by omega)]
    simp only [show t ≠ len by omega, ↓reduceIte]
    exact fun h => hdiff (by rw [h])
  rw [generate_eq_after_produce_swap state mid ⟨t, hct⟩ he current top rfl (by simp [top, hml])
    (by simp only [current]; omega) hb hv hr]
  obtain ⟨next, heq, hs⟩ := swap_success mid current (by simp only [current]; omega) hr
    (fun hf => hnf ⟨_, hf⟩)
  rw [heq, except_ok_bind]
  have hpn := (hpm.swap hs).congr (other := fun i => if i = t then t else if i = len then lab t
      else lab i) fun i hi => by
    simp only [swapIdx, current, show len + 1 - 1 = len by omega]
    split_ifs <;> omega
  have hfin : ∃ h, next.isFinal ⟨t, h⟩ := by rw [hpn.isFinal_iff t (by omega)]; simp
  rw [index_eq ⟨t, (by have := hpn.length; omega : t < next.stack.length)⟩, except_ok_bind,
    ite_eq_left ((next.isFinal_iff _).mpr hfin)]
  exact cont next hpn (by rw [(swap_counts _ _ _ heq).swaps, produce_swaps he])
theorem bound_step {post : ((res : Stack) × Trace spills source res) → Prop}
    (t : Nat) (state : State source target spills)
    (hl : Labeled len lab state) (hnodup : target.Nodup) (hsp : AllSpilled target spills)
    (hinj : LabInj len lab) (c : Nat) (hc : c < len) (hlab : lab c = t) (htc : t < c)
    (hfit : len ≤ t + 17) (hwide : t + 16 ≤ len) (hpend : state.pending_generations ≠ 0)
    (hnfinal : lab t ≠ t)
    (cont : ∀ next : State source target spills, Labeled len (boundLab len c t lab) next →
      next.trace.swapCount = state.trace.swapCount + (if c = len - 1 then 1 else 2) →
      Succeeds (buildBottomUp.loop (t + 1) next) post) :
    Succeeds (buildBottomUp.loop t state) post := by
  have hp := hl.placed hnodup hinj
  refine hp.bound_step t state (hsp.reachable state) (Or.inl hwide) c hc hlab htc hfit hpend
    hnfinal (fun s hs hsc _ he => hsc (hinj s hs c hc ?_)) fun next hb => cont next (hl.boundSwaps hb)
  have hr := hp.range s hs
  have ht := hp.range c hc
  rw [hlab] at ht
  rw [List.getElem?_eq_getElem hr, List.getElem?_eq_getElem ht, Option.some.injEq] at he
  rw [hlab]
  exact (List.Nodup.getElem_inj_iff hnodup).mp he

-- With fewer than 16 slots above t, the loop generates the next target at the top.
theorem top_step {post : ((res : Stack) × Trace spills source res) → Prop}
    (t : Nat) (state : State source target spills)
    (hl : Labeled len lab state) (hnodup : target.Nodup) (hsp : AllSpilled target spills)
    (hinj : LabInj len lab) (htl : t < len) (hlt : len < target.length) (hnear : len < t + 16)
    (hnfinal : lab t ≠ t)
    (cont : ∀ next : State source target spills,
      Labeled (len + 1) (fun i => if i = len then len else lab i) next →
      next.trace.swapCount = state.trace.swapCount →
      Succeeds (buildBottomUp.loop t next) post) :
    Succeeds (buildBottomUp.loop t state) post := by
  have hp := hl.placed hnodup hinj
  have hfree : state.positionOfNat len = none := by
    simpa [State.positionOfNat, State.positionOf, hlt] using (hl.unbound ⟨len, hlt⟩).mpr le_rfl
  refine hp.gen_step t state (hsp.reachable state) len le_rfl hlt hfree
    (hsp.available state _) htl hnfinal hnear
    (fun choice hu => Or.inr ⟨hsp.no_urgent hu, rfl⟩) fun next hg => cont next (hl.grow hg.generation rfl)

-- The cycle a → a + 1 → … → a + m → a on Fin size.
def shiftCycle (size a m : Nat) (h : a + m < size) : List (Fin size) :=
  List.ofFn fun j : Fin (m + 1) => ⟨a + j.val, by omega⟩

@[simp] theorem shiftCycle_length (h : a + m < size) : (shiftCycle size a m h).length = m + 1 := by
  simp [shiftCycle]

@[simp] theorem shiftCycle_getElem (h : a + m < size) (j : Nat) (hj : j < (shiftCycle size a m h).length) :
    ((shiftCycle size a m h)[j]).val = a + j := by
  simp only [shiftCycle, List.getElem_ofFn]

theorem shiftCycle_nodup (h : a + m < size) : (shiftCycle size a m h).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  apply Fin.ext
  simpa [Fin.ext_iff] using hij

theorem mem_shiftCycle (h : a + m < size) (i : Fin size) :
    i ∈ shiftCycle size a m h ↔ a ≤ i.val ∧ i.val ≤ a + m := by
  simp only [shiftCycle, List.mem_ofFn, Fin.ext_iff]
  constructor
  · rintro ⟨j, hj⟩; have := j.isLt; omega
  · intro hi; exact ⟨⟨i.val - a, by omega⟩, by simp; omega⟩

theorem formPerm_shiftCycle (h : a + m < size) (i : Fin size) :
    ((shiftCycle size a m h).formPerm i).val =
      if a ≤ i.val ∧ i.val < a + m then i.val + 1 else if i.val = a + m then a else i.val := by
  by_cases hi : a ≤ i.val ∧ i.val ≤ a + m
  · obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ hj : j < (shiftCycle size a m h).length,
        (shiftCycle size a m h)[j] = i :=
      List.getElem_of_mem ((mem_shiftCycle h i).mpr hi)
    rw [List.formPerm_apply_getElem _ (shiftCycle_nodup h)]
    simp only [shiftCycle_getElem, shiftCycle_length] at hj hi ⊢
    by_cases hl : j < m
    · rw [Nat.mod_eq_of_lt (by omega)]
      simp only [Nat.add_assoc]
      split_ifs <;> omega
    · rw [show j + 1 = m + 1 by omega, Nat.mod_self]
      simp only [Nat.add_zero]
      split_ifs <;> omega
  · rw [List.formPerm_apply_of_notMem (by rwa [mem_shiftCycle])]
    split_ifs <;> omega

-- A single cycle on m + 1 consecutive slots costs m swaps if it contains
-- the top and m + 2 swaps if it does not.
theorem swapCount_shiftCycle (h : a + m < size) (hm : 1 ≤ m) (perm : Equiv.Perm (Fin size))
    (hperm : ∀ i : Fin size, (perm i).val =
      if a ≤ i.val ∧ i.val < a + m then i.val + 1 else if i.val = a + m then a else i.val)
    (top : Fin size) :
    Permutation.swapCount perm top =
      if a ≤ top.val ∧ top.val ≤ a + m then m else m + 2 := by
  have heq : perm = (shiftCycle size a m h).formPerm := by
    ext i; rw [hperm, formPerm_shiftCycle]
  have hcycle := List.isCycle_formPerm (shiftCycle_nodup h) (by simp; omega)
  have hsupport := List.support_formPerm_of_nodup _ (shiftCycle_nodup h)
    (fun x hx => by have := congrArg List.length hx; simp at this; omega)
  have hfix := hperm top
  rw [Permutation.swapCount_eq, ← heq] at *
  rw [hcycle.cycleFactorsFinset_eq_singleton, hsupport,
    List.toFinset_card_of_nodup (shiftCycle_nodup h), Finset.card_singleton, shiftCycle_length]
  by_cases ht : a ≤ top.val ∧ top.val ≤ a + m
  · have hne : perm top ≠ top := by
      intro he; rw [he] at hfix; split_ifs at hfix <;> omega
    simp only [ht, hne, and_self, ↓reduceIte]
    omega
  · have he : perm top = top := by
      apply Fin.ext; rw [hfix]; split_ifs <;> omega
    simp only [ht, he, ↓reduceIte]
    omega

theorem Placed.permute_step (t : Nat) (state : State source target spills)
    (hl : Placed len lab state)
    (hfull : len = target.length) (m : Nat) (hm : 1 ≤ m) (hcyc : t + m < len)
    (hfit : len ≤ t + 17)
    (hlab : ∀ i < len, lab i = if t ≤ i ∧ i < t + m then i + 1 else if i = t + m then t else i) :
    Succeeds (buildBottomUp.loop t state) (fun result => result.2.swapCount =
      state.trace.swapCount + if t + m = len - 1 then m else m + 2) := by
  have hlen := hl.length
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  simp only [show ¬t ≥ target.length by omega, ↓reduceIte]
  have hnfinal : lab t ≠ t := by rw [hlab t (by omega)]; split_ifs <;> omega
  have hnft : ¬ ∃ h, state.isFinal ⟨t, h⟩ := by
    rw [hl.isFinal_iff t (by omega)]
    exact hnfinal
  rw [skip_unless_final (fun hlt => (state.isFinal_iff ⟨t, hlt⟩).not.mpr hnft)]
  have hz : state.pending_generations = 0 := by rw [hl.pending]; omega
  have hp : state.stack.length = target.length ∧ ∀ i, (state.mapping i).isSome :=
    ⟨by omega, fun i => by rw [hl.mapping_apply i]; rfl⟩
  simp only [hz, ↓reduceIte, requires_of_true _ hp.1, except_ok_bind]
  rw [requires_of_true (∀ i, (state.destinationOf i).isSome) hp.2, except_ok_bind]
  have hperm : ∀ i, (state.mapping.toPermutation hp.1 hp.2 i).val =
      if t ≤ i.val ∧ i.val < t + m then i.val + 1 else if i.val = t + m then t else i.val := by
    intro i
    have happly := Mapping.toPermutation_apply state.mapping hp.1 hp.2 i
    rw [hl.mapping_apply i] at happly
    have hval := congrArg (Option.map Fin.val) happly
    simp only [Option.map_some, Fin.val_cast, Option.some.injEq] at hval
    rw [hval, hlab i (by omega)]
  have hreach : all_swaps_reachable (state.mapping.toPermutation hp.1 hp.2) := by
    intro i hi
    have hmoved := Equiv.Perm.mem_support.mp hi
    have hi' := hperm i
    have hne : (state.mapping.toPermutation hp.1 hp.2 i).val ≠ i.val := fun he => hmoved (Fin.ext he)
    simp only [Fin.val_rev, MAX_SWAP_DEPTH]
    split_ifs at hi' <;> omega
  obtain ⟨res, trace, heq, _⟩ := permute_applies_permutation_reachable
    spills state.stack (state.mapping.toPermutation hp.1 hp.2) hreach
  simp only [heq, Except.mapError, except_ok_bind]
  refine ⟨_, rfl, ?_⟩
  dsimp only
  rw [swapCount_concat, permute_swapCount spills state.stack _ (by omega) heq,
    swapCount_shiftCycle (by omega) hm _ hperm]
  simp only
  split_ifs <;> omega

-- With no pending generation, the loop permutes the cycle t → t + 1 → … → t + m → t.
theorem permute_step (t : Nat) (state : State source target spills)
    (hl : Labeled len lab state) (hnodup : target.Nodup) (hinj : LabInj len lab)
    (hfull : len = target.length) (m : Nat) (hm : 1 ≤ m) (hcyc : t + m < len)
    (hfit : len ≤ t + 17)
    (hlab : ∀ i < len, lab i = if t ≤ i ∧ i < t + m then i + 1 else if i = t + m then t else i) :
    Succeeds (buildBottomUp.loop t state) (fun result => result.2.swapCount =
      state.trace.swapCount + if t + m = len - 1 then m else m + 2) :=
  (hl.placed hnodup hinj).permute_step t state hfull m hm hcyc hfit hlab

theorem rot_inj (len t w : Nat) : LabInj len (rot t w) := by
  intro i _ j _ h
  unfold rot at h
  split_ifs at h <;> omega

-- Steady state: the 16 slots from t up carry the cycle t → … → t + 14 → t and one fixed top.
-- Each of p pending generations costs one bound step of 2 swaps; the final cycle costs 16.
theorem steady (hnodup : target.Nodup) (hsp : AllSpilled target spills) :
    ∀ p t (state : State source target spills), Labeled (t + 16) (rot t 14) state →
      target.length = t + 16 + p →
      Succeeds (buildBottomUp.loop t state)
        (fun result => result.2.swapCount = state.trace.swapCount + 2 * p + 16) := by
  intro p
  induction p with
  | zero =>
    intro t state hl htarget
    apply (permute_step t state hl hnodup (rot_inj _ _ _) (by omega) 14 (by omega) (by omega)
      (by omega) (fun i _ => rfl)).mono
    intro result hr
    rw [hr]
    simp only [show ¬(t + 14 = t + 16 - 1) by omega, ↓reduceIte]
  | succ p ih =>
    intro t state hl htarget
    have hc : rot t 14 (t + 14) = t := by simp [rot]
    refine bound_step t state hl hnodup hsp (rot_inj _ _ _) (t + 14) (by omega) hc (by omega)
      (by omega) (by omega) (by rw [hl.pending]; omega) (by simp [rot]) fun mid hmid hcount => ?_
    have hmid' : Labeled (t + 1 + 15) (rot (t + 1) 14) mid := by
      refine hmid.congr fun i hi => ?_
      simp only [boundLab, rot, swapIdx]
      split_ifs <;> omega
    refine top_step (t + 1) mid hmid' hnodup hsp (rot_inj _ _ _) (by omega) (by omega) (by omega)
      (by simp [rot]) fun next hnext hcount' => ?_
    have hnext' : Labeled (t + 1 + 16) (rot (t + 1) 14) next := by
      refine hnext.congr fun i hi => ?_
      simp only [rot]
      split_ifs <;> omega
    apply (ih (t + 1) next hnext' (by omega)).mono
    intro result hr
    rw [hr, hcount', hcount]
    simp only [show ¬(t + 14 = t + 16 - 1) by omega, ↓reduceIte]
    omega

-- From the 17-slot cycle 0 → 1 → … → 16 → 0 with k pending generations,
-- the loop emits 2k + 16 swaps.
theorem start (hnodup : target.Nodup) (hsp : AllSpilled target spills) (k : Nat)
    (state : State source target spills) (hl : Labeled 17 (rot 0 16) state)
    (htarget : target.length = 17 + k) :
    Succeeds (buildBottomUp.loop 0 state)
      (fun result => result.2.swapCount = state.trace.swapCount + 2 * k + 16) := by
  cases k with
  | zero =>
    apply (permute_step 0 state hl hnodup (rot_inj _ _ _) (by omega) 16 (by omega) (by omega)
      (by omega) (fun i _ => rfl)).mono
    intro result hr
    rw [hr]
    simp
  | succ k =>
    refine bound_step 0 state hl hnodup hsp (rot_inj _ _ _) 16 (by omega) (by simp [rot])
      (by omega) (by omega) (by omega) (by rw [hl.pending]; omega) (by simp [rot])
      fun s1 hs1 hc1 => ?_
    have hs1' : Labeled 17 (rot 1 15) s1 := by
      refine hs1.congr fun i hi => ?_
      simp only [boundLab, rot, swapIdx]
      split_ifs <;> omega
    refine bound_step 1 s1 hs1' hnodup hsp (rot_inj _ _ _) 16 (by omega) (by simp [rot])
      (by omega) (by omega) (by omega) (by rw [hs1'.pending]; omega) (by simp [rot])
      fun s2 hs2 hc2 => ?_
    have hs2' : Labeled (2 + 15) (rot 2 14) s2 := by
      refine hs2.congr fun i hi => ?_
      simp only [boundLab, rot, swapIdx]
      split_ifs <;> omega
    refine top_step 2 s2 hs2' hnodup hsp (rot_inj _ _ _) (by omega) (by omega) (by omega)
      (by simp [rot]) fun s3 hs3 hc3 => ?_
    have hs3' : Labeled (2 + 16) (rot 2 14) s3 := by
      refine hs3.congr fun i hi => ?_
      simp only [rot]
      split_ifs <;> omega
    apply (steady hnodup hsp k 2 s3 hs3' (by omega)).mono
    intro result hr
    rw [hr, hc3, hc2, hc1]
    simp only [↓reduceIte]
    omega

theorem f1Target_nodup (k : Nat) : (f1Target k).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  simpa [Fin.ext_iff] using h

@[simp] theorem f1Target_getElem (j : Nat) (h : j < (f1Target k).length) :
    (f1Target k)[j] = .Var ⟨j⟩ := by
  simp [f1Target]

theorem f1_allSpilled (k : Nat) : AllSpilled (f1Target k) (f1Spills k) := by
  intro j
  have := j.isLt
  simp only [f1Target_length] at this
  rw [Fin.getElem_fin, f1Target_getElem]
  simp [SpillSet.is_spilled, f1Spills, this]

theorem f1Mapping_symm (k : Nat) (j : Fin (f1Target k).length) :
    ((f1Mapping k).symm j).map Fin.val =
      if j.val < 17 then some (if j.val = 0 then 16 else j.val - 1) else none := by
  change Option.map Fin.val (if h : j.val < 17 then some _ else none) = _
  split_ifs <;> rfl

theorem f1_unbound (k : Nat) (j : Fin (f1Target k).length) :
    (f1State k).mapping.symm j = none ↔ 17 ≤ j.val := by
  have h := f1Mapping_symm k j
  rw [← Option.map_eq_none_iff (f := Fin.val)]
  change Option.map Fin.val ((f1Mapping k).symm j) = none ↔ _
  rw [h]
  split_ifs <;> simp <;> omega

theorem f1_labeled (k : Nat) : Labeled 17 (rot 0 16) (f1State k) where
  length := f1Source_length
  range _ hi := rot_lt (by omega) hi
  value i hi := by
    have := rot_lt (t := 0) (w := 16) (by omega) hi
    simp only [f1State, f1Source, f1Target, List.getElem?_ofFn, hi,
      show rot 0 16 i < 17 + k by omega, ↓reduceDIte]
  expected := by
    apply List.ext_getElem (by simp [State.expectedStack])
    intro j _ hj
    simp only [State.expectedStack, List.getElem_ofFn]
    split
    · rename_i pos hpos
      have hs := f1Mapping_symm k ⟨j, hj⟩
      change (f1Mapping k).symm _ = some pos at hpos
      rw [hpos] at hs
      replace hs : some pos.val = if j < 17 then some (if j = 0 then 16 else j - 1) else none := hs
      have hlt : j < 17 := by by_contra hn; simp [hn] at hs
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hs
      change f1Source[pos.val] = _
      simp only [f1Source, List.getElem_ofFn, f1Target_getElem, Value.Var.injEq, VarId.mk.injEq,
        rot]
      split_ifs at hs ⊢ <;> omega
    · rfl
  unbound := f1_unbound k
  pending := by simp [f1State]
  le := by simp

theorem f1_valid (k : Nat) : (f1State k).Valid where
  size := by simp [f1State]
  pending := by
    unfold Mapping.unmapped_target_slots
    rw [Finset.filter_congr fun j _ => f1_unbound k j]
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : Fin (f1Target k).length => j.val < 17)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin, Fin.card_filter_val_lt,
      f1Target_length] at this
    simp only [f1State]
    omega
  available := (f1_allSpilled k).available _

-- For every k, the 17-slot state of family F1 with k pending generations costs 2k + 16 swaps.
theorem f1_swapCount (k : Nat) :
    (buildBottomUp (f1State k) (f1_valid k)).map (·.2.swapCount) = .ok (2 * k + 16) := by
  obtain ⟨⟨res, trace⟩, hv, hc⟩ :=
    start (f1Target_nodup k) (f1_allSpilled k) k (f1State k) (f1_labeled k) (by simp)
  have hspec := loop_spec 0 (f1State k) (State.invariant.initial (f1_valid k))
  rw [hv] at hspec
  have hsize : res.length = (f1Target k).length := by
    simp [show res = _ from hspec, State.expectedStack]
  unfold buildBottomUp
  rw [hv, except_ok_bind]
  simp only [requires_of_true _ hsize, except_ok_bind]
  simp only [Except.map, pure, Except.pure, Except.ok.injEq]
  rw [hc]
  simp [f1State, Trace.swapCount]

end Shuffler.Optimality.BBU
