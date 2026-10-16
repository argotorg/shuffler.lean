import Shuffler.RemoveSurplus.Defs
import Shuffler.Emission.Lemmas

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

--- Actions ----------------------------------------------------------------------------------------

-- No slot is surplus: every slot has a destination.
def State.noSurplus (state : State source target spills) : Prop :=
  ∀ pos, ¬ state.isSurplus pos

-- Swapping a reachable surplus slot below the top with the top keeps the height.
@[spec] theorem swapWith_surplus_spec (state : State source target spills) (offset : ℕ) :
    ⦃∃ h : offset < state.stack.length, offset ≠ state.stack.length - 1 ∧
      state.isSurplus ⟨offset, h⟩ ∧ state.isSwapReachable ⟨offset, h⟩⦄
    state.swapWith offset
    ⦃fun next => next.stack.length = state.stack.length; allowedErrors⦄ := by
  vcgen [State.swapWith, index]
  all_goals simp_all [State.isFinal, State.isSurplus, State.isSwapReachable, State.depthOf,
    Stack.offsetToDepth]
  all_goals omega

-- Popping a non-empty stack lowers the height by one.
@[spec] theorem pop_spec (state : State source target spills) :
    ⦃0 < state.stack.length⦄ state.pop
    ⦃fun next => next.stack.length = state.stack.length - 1; allowedErrors⦄ := by
  vcgen [State.pop]
  all_goals simp_all

--- Scans ------------------------------------------------------------------------------------------

-- The stack offsets from the top down: the top comes first, so a non-empty prefix contains it.
-- (`h` is the scan position as `vcgen` states it, with the reversed list unfolded.)
theorem finRange_top {n : ℕ} {pref suff : List (Fin n)} {cur : Fin n}
    (h : List.finRange n = suff.reverse ++ cur :: pref.reverse) :
    (pref = [] ∧ cur.val = n - 1) ∨ ∃ q ∈ pref, q.val = n - 1 := by
  have h' : (List.finRange n).reverse = pref ++ cur :: suff := by rw [h]; simp
  have hn : 0 < n := by
    rcases n with _ | n
    · simp at h
    · omega
  have hhead : (List.finRange n).reverse.head? = some ⟨n - 1, by omega⟩ := by
    rw [List.head?_reverse, List.getLast?_eq_getElem?, List.length_finRange,
      List.getElem?_eq_getElem (by simp; omega)]
    simp
  rcases pref with _ | ⟨q, pref⟩
  · left
    rw [h'] at hhead
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hhead
    exact ⟨rfl, by rw [hhead]⟩
  · right
    rw [h'] at hhead
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hhead
    exact ⟨q, by simp, by rw [hhead]⟩

-- The scan for a surplus slot equal to the top only looks below the top.
theorem range_lt {top cur : ℕ} {pref suff : List ℕ} (h : List.range top = suff.reverse ++ cur :: pref.reverse) : cur < top := by
  have hmem : cur ∈ List.range top := by rw [h]; simp
  simpa using hmem

-- What the scan for the shallowest and the deepest reachable surplus slot has found so far,
-- after visiting the offsets in `pref` (from the top down).
structure SurplusScan (state : State source target spills) (pref : List (Fin state.stack.length))
    (found : Option ℕ × Option ℕ) : Prop where
  -- nothing found yet: no visited slot is surplus
  clear : found.1 = none → ∀ pos ∈ pref, ¬ state.isSurplus pos
  -- the shallowest surplus slot is the top whenever the top is surplus
  shallowest : ∀ s, found.1 = some s → ∃ h : s < state.stack.length, state.isSurplus ⟨s, h⟩ ∧
    ∀ ht : state.stack.length - 1 < state.stack.length, state.isSurplus ⟨_, ht⟩ → s = state.stack.length - 1
  -- the deepest reachable surplus slot is surplus and reachable
  deepest : ∀ d, found.2 = some d → ∃ h : d < state.stack.length, state.isSurplus ⟨d, h⟩ ∧
    state.isSwapReachable ⟨d, h⟩

namespace SurplusScan

variable {state : State source target spills} {pref suff : List (Fin state.stack.length)}
  {cur : Fin state.stack.length} {found : Option ℕ × Option ℕ}

theorem start (state : State source target spills) : SurplusScan state [] (none, none) :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩

-- A slot that is not surplus changes nothing.
theorem skip (h : SurplusScan state pref found) (hc : ¬ state.isSurplus cur) :
    SurplusScan state (pref ++ [cur]) found := by
  refine ⟨fun hn pos hpos => ?_, h.shallowest, h.deepest⟩
  rcases List.mem_append.mp hpos with hpos | hpos
  · exact h.clear hn pos hpos
  · simp at hpos; subst hpos; exact hc

-- The first surplus slot is the shallowest one: either it is the top, or the top was visited
-- before and is not surplus.
theorem first_shallowest (h : SurplusScan state pref found) (hc : state.isSurplus cur)
    (hn : found.1 = none) (hpos : List.finRange state.stack.length = suff.reverse ++ cur :: pref.reverse) :
    ∃ hlt : cur.val < state.stack.length, state.isSurplus ⟨cur.val, hlt⟩ ∧
      ∀ ht : state.stack.length - 1 < state.stack.length,
        state.isSurplus ⟨_, ht⟩ → cur.val = state.stack.length - 1 := by
  refine ⟨cur.isLt, hc, fun ht htop => ?_⟩
  rcases finRange_top hpos with ⟨_, htopcur⟩ | ⟨q, hq, hqtop⟩
  · exact htopcur
  · have : q = ⟨_, ht⟩ := Fin.ext hqtop
    subst this
    exact absurd htop (h.clear hn _ hq)

theorem first_reachable (h : SurplusScan state pref found) (hc : state.isSurplus cur)
    (hn : found.1 = none) (hr : state.isSwapReachable cur)
    (hpos : List.finRange state.stack.length = suff.reverse ++ cur :: pref.reverse) :
    SurplusScan state (pref ++ [cur]) (some cur.val, some cur.val) :=
  ⟨fun hn' => by simp at hn', fun s hs => by cases hs; exact h.first_shallowest hc hn hpos,
    fun d hd => by cases hd; exact ⟨cur.isLt, hc, hr⟩⟩

theorem first_unreachable (h : SurplusScan state pref found) (hc : state.isSurplus cur)
    (hn : found.1 = none)
    (hpos : List.finRange state.stack.length = suff.reverse ++ cur :: pref.reverse) :
    SurplusScan state (pref ++ [cur]) (some cur.val, found.2) :=
  ⟨fun hn' => by simp at hn', fun s hs => by cases hs; exact h.first_shallowest hc hn hpos,
    h.deepest⟩

-- A later surplus slot keeps the shallowest one, and becomes the deepest reachable if reachable.
theorem later_reachable (h : SurplusScan state pref found) (hc : state.isSurplus cur)
    (hn : ¬ found.1 = none) (hr : state.isSwapReachable cur) :
    SurplusScan state (pref ++ [cur]) (found.1, some cur.val) :=
  ⟨fun hn' => absurd hn' hn, h.shallowest, fun d hd => by cases hd; exact ⟨cur.isLt, hc, hr⟩⟩

theorem later_unreachable (h : SurplusScan state pref found) (hn : ¬ found.1 = none) :
    SurplusScan state (pref ++ [cur]) found :=
  ⟨fun hn' => absurd hn' hn, h.shallowest, h.deepest⟩

-- After the whole scan: nothing found means nothing is surplus,
theorem noSurplus_of_none (h : SurplusScan state (List.finRange state.stack.length).reverse found)
    (hn : found.1 = none) : state.noSurplus :=
  fun pos => h.clear hn pos (by simp)

-- and something found means something is surplus.
theorem not_noSurplus (h : SurplusScan state pref found) (hs : found.1 = some s) :
    ¬ state.noSurplus := by
  obtain ⟨_, hsur, _⟩ := h.shallowest s hs
  exact fun hno => hno _ hsur

theorem shallowest_lt (h : SurplusScan state pref found) (hs : found.1 = some s) :
    s < state.stack.length :=
  (h.shallowest s hs).1

-- If the shallowest surplus slot is not the top, the top is not surplus, so neither is the deepest
-- reachable one: it can be swapped with the top.
theorem deepest_swappable (h : SurplusScan state pref found) (hs : found.1 = some s)
    (hd : found.2 = some d) (hne : ¬ s = state.stack.length - 1) :
    ¬ d = state.stack.length - 1 ∧
      ∃ h : d < state.stack.length, state.isSurplus ⟨d, h⟩ ∧ state.isSwapReachable ⟨d, h⟩ := by
  obtain ⟨hlt, hsur, hreach⟩ := h.deepest d hd
  refine ⟨fun hdt => ?_, hlt, hsur, hreach⟩
  obtain ⟨_, _, htop⟩ := h.shallowest s hs
  subst hdt
  exact hne (htop hlt hsur)

end SurplusScan

--- removeSurplus ------------------------------------------------------------------------------------

theorem noSurplus_of_length (state : State source target spills) (h : state.stack.length = 0) :
    state.noSurplus :=
  fun pos => absurd pos.isLt (by omega)

theorem noSurplus_of_nil (state : State source target spills) (h : state.stack = []) :
    state.noSurplus :=
  noSurplus_of_length state (by simp [h])

-- After all passes, the stack is empty or nothing is surplus.
theorem outer_end {state : State source target spills} {n : ℕ}
    (h : state.noSurplus ∨ state.stack.length + n ≤ n) : state.noSurplus := by
  rcases h with h | h
  · exact h
  · exact noSurplus_of_length state (by omega)

-- The outer loop: either nothing is surplus (so the loop stops), or every pass so far has popped a slot.
theorem outer_pop {old : State source target spills} {k n : ℕ} {P : Prop} (hinv : old.noSurplus ∨ old.stack.length + k ≤ n) (hsur : ¬ old.noSurplus)
    (hne : old.stack ≠ []) : P ∨ old.stack.length - 1 + (k + 1) ≤ n := by
  have := List.length_pos_iff.mpr hne
  rcases hinv with h | h
  · exact absurd h hsur
  · right; omega

theorem removeSurplus_triple (initial : State source target spills) :
    ⦃True⦄ removeSurplus initial ⦃fun res => res.noSurplus; allowedErrors⦄ := by
  vcgen [removeSurplus, index, slotAt]
  case inv1 =>
    exact fun pref _ state => state.noSurplus ∨ state.stack.length + pref.length ≤ initial.stack.length
  case inv2 =>
    rename_i state _ _
    exact fun pref _ found => SurplusScan state pref found
  case inv3 =>
    rename_i state _ _ _ _ _ _ _ _ _
    exact fun _ _ equal => ∀ e, equal = some e → e < state.stack.length - 1
  all_goals try simp_all [allowedErrors, State.blockSwapUnreachable]
  all_goals first
    | exact SurplusScan.start _
    | exact SurplusScan.skip (by assumption) (by assumption)
    | exact SurplusScan.first_reachable (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption)
    | exact SurplusScan.first_unreachable (by assumption) (by assumption) (by assumption) (by assumption)
    | exact SurplusScan.later_reachable (by assumption) (by assumption) (by assumption) (by assumption)
    | exact SurplusScan.later_unreachable (by assumption) (by assumption)
    | exact Or.inl (SurplusScan.noSurplus_of_none (by assumption) (by assumption))
    | exact outer_pop (by assumption) (SurplusScan.not_noSurplus (by assumption) (by assumption))
        (by assumption)
    | exact Or.inl (noSurplus_of_nil _ (by assumption))
    | exact outer_end (by assumption)
    | exact SurplusScan.deepest_swappable (by assumption) (by assumption) (by assumption) (by assumption)
    | exact absurd (SurplusScan.shallowest_lt (by assumption) (by assumption)) (by omega)
    | exact List.length_pos_iff.mpr (by assumption)
    | exact range_lt (by assumption)
    | (have := List.length_pos_iff.mpr (by assumption : _ ≠ []); omega)
    | (have := range_lt (by assumption); omega)

end Shuffler.Emission
