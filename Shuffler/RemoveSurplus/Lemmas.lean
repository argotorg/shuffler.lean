module

public import Shuffler.RemoveSurplus.Defs
public import Shuffler.Emission.Lemmas
import Mathlib.Algebra.Group.Nat.Defs
import Std.WP.Triple.SpecLemmas

@[expose] public section

open Std.WP

set_option experimental.vcgen true

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

--- Actions ----------------------------------------------------------------------------------------

-- No slot is surplus: every slot has a destination.
def State.noSurplus (state : State source target spills) : Prop :=
  ∀ pos, ¬ state.isSurplus pos

-- The value of the slot bound for target offset `dest`, or none if no slot is bound for it.
def State.boundValue (state : State source target spills) (dest : Fin target.length) : Option Value :=
  (state.mapping.positionOf dest).map fun pos => state.stack[pos]

-- The top slot, if any, has no destination.
def State.topSurplus (state : State source target spills) : Prop :=
  ∀ h : state.stack.length - 1 < state.stack.length, state.isSurplus ⟨_, h⟩

-- Swapping two slots moves their destinations along: every target keeps its value.
theorem boundValue_swap (state : State source target spills) (a b : Fin state.stack.length)
    (trace : Trace spills source (state.stack.swap a b)) :
    { state with
      stack := state.stack.swap a b
      trace := trace
      mapping := List.length_swap.symm ▸ state.mapping.swapDestinations a b
    }.boundValue = state.boundValue := by
  funext dest
  simp only [State.boundValue, Mapping.positionOf, Mapping.cast_symm, Mapping.swapDestinations_symm_apply,
    Option.map_map]
  cases state.mapping.symm dest with
  | none => rfl
  | some pos =>
    simp only [Option.map_some, Function.comp_apply]
    by_cases ha : pos = a
    · subst pos; simp [a.isLt]
    by_cases hb : pos = b
    · subst pos; simp [b.isLt]
    simp [Equiv.swap_apply_of_ne_of_ne ha hb, Fin.val_ne_of_ne ha, Fin.val_ne_of_ne hb]

-- Swapping a surplus slot with the top makes the top surplus.
theorem topSurplus_swap (state : State source target spills) (pos : Fin state.stack.length)
    (hpos : state.isSurplus pos) (htop : state.stack.length - 1 < state.stack.length)
    (trace : Trace spills source (state.stack.swap pos (state.stack.length - 1))) :
    State.topSurplus { state with
      stack := state.stack.swap pos (state.stack.length - 1)
      trace := trace
      mapping := List.length_swap.symm ▸ state.mapping.swapDestinations pos ⟨_, htop⟩ } := by
  intro h
  simp only [State.isSurplus, Mapping.destinationOf, Mapping.cast_apply, Mapping.swapDestinations_apply]
  have : (Fin.cast List.length_swap.symm.symm ⟨(state.stack.swap pos (state.stack.length - 1)).length - 1, h⟩ :
      Fin state.stack.length) = ⟨_, htop⟩ := Fin.ext (by simp)
  rw [this, Equiv.swap_apply_right]
  exact hpos

-- An equal surplus slot taking over the top's destination keeps every target's value, and leaves
-- the top surplus.
theorem boundValue_retag (state : State source target spills) (a b : Fin state.stack.length)
    (heq : state.stack[a] = state.stack[b]) :
    { state with mapping := state.mapping.swapDestinations a b }.boundValue = state.boundValue := by
  funext dest
  simp only [State.boundValue, Mapping.positionOf, Mapping.swapDestinations_symm_apply, Option.map_map]
  cases state.mapping.symm dest with
  | none => rfl
  | some pos =>
    simp only [Option.map_some, Function.comp_apply]
    by_cases ha : pos = a
    · subst pos; simpa using heq.symm
    by_cases hb : pos = b
    · subst pos; simpa using heq
    simp [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem topSurplus_retag (state : State source target spills) (a : Fin state.stack.length)
    (ha : state.isSurplus a) (htop : state.stack.length - 1 < state.stack.length) :
    State.topSurplus { state with mapping := state.mapping.swapDestinations a ⟨_, htop⟩ } := by
  intro _
  simp only [State.isSurplus, Mapping.destinationOf, Mapping.swapDestinations_apply,
    Equiv.swap_apply_right]
  exact ha

-- Popping a surplus top keeps every target's value.
theorem boundValue_pop (state : State source target spills) (hne : 0 < state.stack.length)
    (htop : state.topSurplus) :
    { state with
      stack := state.stack.dropLast
      trace := .Pop hne state.trace
      mapping := (stack_pop_len state.stack hne ▸ state.mapping).pop
    }.boundValue = state.boundValue := by
  have hlen := stack_pop_len state.stack hne
  have hfree : (hlen ▸ state.mapping) (Fin.last state.stack.dropLast.length) = none := by
    rw [Mapping.cast_apply]
    have := htop (by omega)
    simp only [State.isSurplus, Mapping.destinationOf] at this
    convert this using 2
    ext; simp
  funext dest
  have hkeep := Mapping.pop_symm_of_top_none _ hfree dest
  rw [Mapping.cast_symm] at hkeep
  simp only [State.boundValue, Mapping.positionOf]
  cases hq : (hlen ▸ state.mapping).pop.symm dest with
  | none =>
    rw [hq] at hkeep
    cases hp : state.mapping.symm dest
    · rfl
    · simp [hp] at hkeep
  | some q =>
    rw [hq] at hkeep
    cases hp : state.mapping.symm dest with
    | none => simp [hp] at hkeep
    | some p =>
      simp only [hp, Option.map_some, Option.some.injEq] at hkeep
      have hqp : q.val = p.val := by simpa [Fin.ext_iff] using hkeep
      simp [List.getElem_dropLast, hqp]

-- Swapping a reachable surplus slot below the top with the top keeps the height and every target's
-- value, and leaves the top surplus.
@[spec] theorem swapWith_surplus_spec (state : State source target spills) (offset : ℕ) :
    ⦃∃ h : offset < state.stack.length, offset ≠ state.stack.length - 1 ∧
      state.isSurplus ⟨offset, h⟩ ∧ state.isSwapReachable ⟨offset, h⟩⦄
    state.swapWith offset
    ⦃fun next => next.stack.length = state.stack.length ∧ next.boundValue = state.boundValue ∧
      next.topSurplus; allowedErrors⦄ := by
  vcgen [State.swapWith, index]
  all_goals simp_all [State.isFinal, State.isSurplus, State.isSwapReachable, State.depthOf,
    Stack.offsetToDepth]
  all_goals first
    | omega
    | exact ⟨boundValue_swap state ⟨offset, by assumption⟩ ⟨state.stack.length - 1, by omega⟩ _,
        topSurplus_swap _ ⟨offset, by assumption⟩ (by simp_all [State.isSurplus]) _ _⟩

-- Popping a non-empty stack with a surplus top lowers the height by one and keeps every target's
-- value: only surplus slots are ever popped.
@[spec] theorem pop_spec (state : State source target spills) :
    ⦃0 < state.stack.length ∧ state.topSurplus⦄ state.pop
    ⦃fun next => next.stack.length = state.stack.length - 1 ∧ next.boundValue = state.boundValue;
      allowedErrors⦄ := by
  vcgen [State.pop]
  all_goals simp_all
  all_goals rename_i h; exact boundValue_pop _ h.1 h.2

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

-- The equal surplus slot lies below the top.
theorem lt_of_exists_lt {e n : ℕ} {P : e < n - 1 → Prop} (h : ∃ h, P h) : e < n := by
  obtain ⟨h, _⟩ := h
  omega

-- The shallowest surplus slot is the top: the top can be popped right away.
theorem SurplusScan.top_ready {state : State source target spills} {pref} {found : Option ℕ × Option ℕ}
    (h : SurplusScan state pref found) (hs : found.1 = some (state.stack.length - 1))
    (hne : state.stack ≠ []) : 0 < state.stack.length ∧ state.topSurplus := by
  obtain ⟨hlt, hsur, _⟩ := h.shallowest _ hs
  exact ⟨List.length_pos_iff.mpr hne, fun _ => hsur⟩

-- An equal surplus slot below the top takes over the top's destination: the top can then be popped,
theorem retag_ready (state : State source target spills) (e : ℕ) (he : e < state.stack.length)
    (ht : state.stack.length - 1 < state.stack.length)
    (h : ∃ _ : e < state.stack.length - 1, state.isSurplus ⟨e, by omega⟩ ∧
      state.stack[e]'(by omega) = state.stack[state.stack.length - 1]'(by omega)) :
    0 < state.stack.length ∧
      State.topSurplus { state with mapping := state.mapping.swapDestinations ⟨e, he⟩ ⟨_, ht⟩ } := by
  obtain ⟨_, hsur, _⟩ := h
  exact ⟨by omega, topSurplus_retag state ⟨e, he⟩ hsur ht⟩

-- and every target keeps its value.
theorem retag_bound (state : State source target spills) (e : ℕ) (he : e < state.stack.length)
    (ht : state.stack.length - 1 < state.stack.length)
    (h : ∃ _ : e < state.stack.length - 1, state.isSurplus ⟨e, by omega⟩ ∧
      state.stack[e]'(by omega) = state.stack[state.stack.length - 1]'(by omega)) :
    { state with mapping := state.mapping.swapDestinations ⟨e, he⟩ ⟨_, ht⟩ }.boundValue =
      state.boundValue := by
  obtain ⟨_, _, heq⟩ := h
  exact boundValue_retag state ⟨e, he⟩ ⟨_, ht⟩ heq

-- The outer loop: either nothing is surplus (so the loop stops), or every pass so far has popped a slot.
theorem outer_pop {old : State source target spills} {k n : ℕ} {P : Prop} (hinv : old.noSurplus ∨ old.stack.length + k ≤ n) (hsur : ¬ old.noSurplus)
    (hne : old.stack ≠ []) : P ∨ old.stack.length - 1 + (k + 1) ≤ n := by
  have := List.length_pos_iff.mpr hne
  rcases hinv with h | h
  · exact absurd h hsur
  · right; omega

-- `vcgen` can state the scan result as a literal pair, so its projections can need `rfl`.
local macro "hyp" : term => `(by first | assumption | rfl)

theorem removeSurplus_triple (initial : State source target spills) :
    ⦃True⦄ (((removeSurplus initial) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state)
    ⦃fun res => res.noSurplus ∧ res.boundValue = initial.boundValue; allowedErrors⦄ := by
  vcgen [removeSurplus, index, slotAt]
  case inv1 =>
    exact fun pref remaining result =>
      match result.1 with
      | some r => r.blocked.isSome = true ∧ remaining = []
      | none => (result.2.noSurplus ∨ result.2.stack.length + pref.length ≤ initial.stack.length) ∧
        result.2.boundValue = initial.boundValue
  case inv2 =>
    rename_i state _ _
    -- No reachable surplus slot was seen if the second scan result is empty.
    exact fun pref _ found => SurplusScan state pref found ∧
      (found.2 = none → ∀ pos ∈ pref, state.isSurplus pos → ¬ state.isSwapReachable pos)
  case inv3 =>
    rename_i state _ _ _ _ _ _ _ _ _ _
    exact fun _ _ equal => ∀ e, equal = some e → ∃ h : e < state.stack.length - 1,
      state.isSurplus ⟨e, by omega⟩ ∧ state.stack[e]'(by omega) = state.stack[state.stack.length - 1]'(by omega)
  all_goals try casesm* Option (Result _ _ _)
  all_goals try dsimp only at *
  all_goals try casesm* _ ∧ _
  all_goals try simp_all [allowedErrors]
  all_goals try subst_vars
  all_goals try simp_all
  all_goals first
    | (apply_assumption
       exact (SurplusScan.shallowest hyp _ hyp).choose_spec.1)
    | (constructor
       · first
           | exact SurplusScan.skip hyp hyp
           | exact SurplusScan.first_unreachable hyp hyp hyp hyp
           | exact SurplusScan.later_unreachable hyp hyp
       · aesop)
    | exact SurplusScan.top_ready hyp hyp hyp
    | exact SurplusScan.start _
    | exact SurplusScan.first_reachable hyp hyp hyp hyp hyp
    | exact SurplusScan.later_reachable hyp hyp hyp hyp
    | exact Or.inl (SurplusScan.noSurplus_of_none hyp hyp)
    | exact outer_pop hyp (SurplusScan.not_noSurplus hyp hyp) hyp
    | exact Or.inl (noSurplus_of_nil _ hyp)
    | exact outer_end hyp
    | exact SurplusScan.deepest_swappable hyp hyp hyp hyp
    | exact absurd (SurplusScan.shallowest_lt hyp hyp) (by omega)
    | exact List.length_pos_iff.mpr hyp
    | exact range_lt hyp
    | (have := List.length_pos_iff.mpr (hyp : _ ≠ []); omega)
    | (have := range_lt hyp; omega)
    | exact lt_of_exists_lt hyp
    | (rename_i hchoice
       exact retag_ready _ _ _ _ (hchoice _ rfl))
    | (rename_i st shallowest deepest equal popped outer nonempty nontop hlen scan unreach hchoice hpopped
       first
       | (have hbad := outer.2; contradiction)
       | exact ⟨outer_pop outer.1 (SurplusScan.not_noSurplus scan rfl) (by simpa using nonempty),
           (retag_bound _ _ _ _ (hchoice _ rfl)).trans outer.2⟩)


end Shuffler.Emission
