module

public import Shuffler.Permute.Normalization
import Shuffler.Permute.Cycles
import Shuffler.Emission.Lemmas

@[expose] public section

namespace Shuffler.Permute

open Emission

theorem support_swap_subset_away {n : ℕ} (p : Equiv.Perm (Fin n)) (top pos i : Fin n)
    (hpos : p pos ≠ pos) (hi : i ≠ top) (hm : i ∈ (p * Equiv.swap top pos).support) :
    i ∈ p.support := by
  by_cases hip : i = pos
  · simpa [hip] using hpos
  · simpa [Equiv.Perm.mem_support, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hi hip] using hm

-- `go` either exchanges a misplaced `pos` with the top and continues, or stops once every slot is in place.
-- `pos` is the destination of a misplaced top, or the slot that a top in place exchanges with to start a cycle.
theorem go_induct {n : ℕ} (hne : n > 0)
    (motive : State source target spills → Permutation n →
      Except ShuffleErr (Result source target spills) → Prop)
    (step : ∀ (top : Fin n), top.val = n - 1 → ∀ state (p : Permutation n) (pos : Fin n), pos ≠ top →
      p pos ≠ pos → (p top = pos ∨ p top = top) →
      (∀ result : Result source target spills, motive result.state (p * Equiv.swap top pos)
        (permute.go result.state (p * Equiv.swap top pos) hne)) →
      motive state p (do
        let result ← permute.exchangeWithTop state pos
        if result.blocked.isSome then pure result
        else permute.go result.state (p * Equiv.swap top pos) hne))
    (done : ∀ state, motive state 1 (pure ⟨none, state⟩)) :
    ∀ state p, motive state p (permute.go state p hne) := by
  refine permute.go.induct_unfolding hne motive ?_ ?_ ?_
  · intro state p top ht _ ih
    exact step top rfl state p (p top) ht (fun h => ht (p.injective h)) (Or.inl rfl) ih
  · intro state p top ht _ pos hpos _ _ ih
    exact step top rfl state p pos (fun h => hpos (h ▸ not_not.mp ht)) hpos (Or.inr (not_not.mp ht)) ih
  · intro state p _ _ _ hsearch
    obtain rfl := foldl_find_out_of_place_eq_one p hsearch
    exact done state

theorem getElem_list_swap (stack : Stack) (a b : Fin stack.length)
    (i : ℕ) (hi : i < (stack.swap a.val b.val).length) (j : Fin stack.length) (hij : i = j.val) :
    (stack.swap a.val b.val)[i] = stack[Equiv.swap a b j] := by
  subst hij
  by_cases ha : j = a
  · subst ha; simp
  by_cases hb : j = b
  · subst hb; simp
  · simpa [Equiv.swap_apply_of_ne_of_ne ha hb] using
      List.getElem_swap_of_ne (fun h => ha (Fin.ext h)) (fun h => hb (Fin.ext h)) hi

theorem Trace.swapCount_cast (h : result = other) (trace : Trace spills source result) :
    (h ▸ trace).swapCount = trace.swapCount := by
  subst h; rfl

-- `next` is `state` with the slots at `top` and `pos` swapped together with their destinations.
structure Exchanged (state next : State source target spills) (top pos : Fin state.stack.length) : Prop where
  length : next.stack.length = state.stack.length
  stack : ∀ i : Fin state.stack.length, next.stack[i.val]? = some state.stack[Equiv.swap top pos i]
  mapping : ∀ (i : Fin next.stack.length) (j : Fin state.stack.length), i.val = j.val →
    next.mapping i = state.mapping (Equiv.swap top pos j)
  perm : next.stack.Perm state.stack
  reach : state.isSwapReachable pos
  swapCount : next.trace.swapCount = state.trace.swapCount + 1
  planned : next.planned_mapping = state.planned_mapping
  pending : next.pending_generations = state.pending_generations

-- Exchanging `pos` with the top blocks on an unequal slot out of reach, fails the assertion on an equal or final
-- slot, or swaps the two slots.
theorem exchangeWithTop_cases (state : State source target spills) (top pos : Fin state.stack.length)
    (htop : top.val = state.stack.length - 1) (hpos : pos ≠ top) :
    (state.stack[top] ≠ state.stack[pos] ∧ ¬ state.isSwapReachable pos ∧
      permute.exchangeWithTop state pos =
        .ok ⟨some ⟨pos.val, (state.depthOf pos).val - MAX_SWAP_DEPTH⟩, state⟩) ∨
    ((state.stack[top] = state.stack[pos] ∨ state.isFinal pos) ∧
      ∃ reason, permute.exchangeWithTop state pos = .error (.assertion reason)) ∨
    (∃ next, Exchanged state next top pos ∧ permute.exchangeWithTop state pos = .ok ⟨none, next⟩) := by
  have hlast : state.stack.length - 1 = top.val := htop.symm
  simp only [permute.exchangeWithTop, hlast, slotAt_index, except_ok_bind]
  by_cases he : state.stack[top] = state.stack[pos]
  · right; left
    exact ⟨Or.inl he, _, by simp [requires, he, throw, throwThe, MonadExceptOf.throw]; rfl⟩
  rw [requires_of_true _ (Ne.symm he), except_ok_bind]
  simp only [index_eq, except_ok_bind]
  by_cases hreach : state.isSwapReachable pos
  · simp only [hreach, not_true_eq_false, ↓reduceIte, State.swapWith, index_eq, except_ok_bind]
    by_cases hfinal : state.isFinal pos
    · right; left
      exact ⟨Or.inr hfinal, _, by simp [requires, hfinal, throw, throwThe, MonadExceptOf.throw]; rfl⟩
    right; right
    have hvalid : state.stack.isValidSwapTarget pos := by
      refine ⟨?_, hreach⟩
      have := Fin.val_ne_of_ne hpos
      dsimp only [Stack.offsetToDepth]
      omega
    rw [requires_of_true _ hfinal, except_ok_bind, requires_of_true _ hvalid, except_ok_bind]
    refine ⟨_, ?_, rfl⟩
    refine ⟨by simp, fun i => ?_, fun i j hij => ?_, List.swap_perm _ _ _, hreach, ?_, rfl, rfl⟩
    · rw [List.getElem?_eq_getElem (by simp)]
      simp only [hlast, Equiv.swap_comm top pos]
      exact congrArg some (getElem_list_swap state.stack pos top i _ i rfl)
    · refine (Mapping.cast_apply _ List.length_swap.symm i).trans ?_
      have ht : state.stack.topOffset pos.pos = top := Fin.ext hlast
      simp only [Mapping.swapDestinations_apply, ht, Equiv.swap_comm pos]
      exact congrArg (fun k => state.mapping (Equiv.swap top pos k)) (Fin.ext hij)
    · exact Trace.swapCount_cast _ _
  · left
    refine ⟨he, hreach, ?_⟩
    simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state pos hreach]
    rw [hlast]

structure RunSpec (state : State source target spills) {n : ℕ} (p : Permutation n)
    (hlen : state.stack.length = n) (result : Result source target spills) : Prop where
  length : result.state.stack.length = state.stack.length
  applies : result.blocked = none → result.state.stack = apply_permutation' state.stack p hlen
  deep : ∀ i : Fin state.stack.length, ¬ state.isSwapReachable i →
    result.state.stack[i.val]? = state.stack[i.val]?
  blocked : ∀ b, result.blocked = some b →
    ∃ i : Fin state.stack.length, b.offset = i.val ∧ 0 < b.excess ∧
      Fin.cast hlen i ∈ p.support ∧ (state.depthOf i).val = b.excess + MAX_SWAP_DEPTH

theorem RunSpec.exchange {state next : State source target spills} {p : Permutation state.stack.length}
    {top pos : Fin state.stack.length} (htop : top.val = state.stack.length - 1) (hmoved : p pos ≠ pos)
    (hx : Exchanged state next top pos) {result : Result source target spills}
    (h : RunSpec next (p * Equiv.swap top pos) hx.length result) : RunSpec state p rfl result := by
  refine ⟨h.length.trans hx.length, fun hb => ?_, fun i hi => ?_, fun b hb => ?_⟩
  · rw [h.applies hb]
    exact apply_permutation'_exchange _ _ _ _ _ _ hx.stack
  · have hit : i ≠ top := by
      rintro rfl
      simp only [Stack.isSwapReachable] at hi
      omega
    have hd := h.deep (Fin.cast hx.length.symm i) (by
      simp only [Stack.isSwapReachable] at hi ⊢; simpa [hx.length] using hi)
    rw [Fin.val_cast] at hd
    rw [hd, hx.stack i, List.getElem?_eq_getElem i.isLt]
    by_cases hip : i = pos
    · subst hip
      exact absurd hx.reach hi
    · simp [Equiv.swap_apply_of_ne_of_ne hit hip]
  · obtain ⟨i, hi, hp, hm, hd⟩ := h.blocked b hb
    refine ⟨Fin.cast hx.length i, hi, hp, support_swap_subset_away p top pos _ hmoved ?_ hm, ?_⟩
    · intro he
      have hiv := congrArg Fin.val he
      have := hx.length
      simp only [Fin.val_cast] at hiv
      dsimp only at hd
      omega
    · simpa [hx.length] using hd

theorem go_spec (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) :
    ∀ result, permute.go state p hne = .ok result → RunSpec state p hlen result := by
  refine go_induct hne (motive := fun state p run =>
      ∀ hlen : state.stack.length = n, ∀ result, run = .ok result → RunSpec state p hlen result)
    ?_ ?_ state p hlen
  · intro top htop state p pos hpos hmoved hcase ih hlen result hr
    subst hlen
    rcases exchangeWithTop_cases state top pos htop hpos with
      ⟨_, hreach, he⟩ | ⟨_, _, he⟩ | ⟨next, hx, he⟩
    · simp only [he, except_ok_bind, Option.isSome_some, ↓reduceIte] at hr
      cases hr
      refine ⟨rfl, by simp, fun _ _ => rfl, fun b hb => ?_⟩
      cases hb
      simp only [Stack.isSwapReachable] at hreach ⊢
      exact ⟨pos, rfl, by omega, by simpa using hmoved, by omega⟩
    · rw [he, except_error_bind] at hr
      cases hr
    · simp only [he, except_ok_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
      exact RunSpec.exchange htop hmoved hx (ih ⟨none, next⟩ hx.length result hr)
  · intro state hlen result hr
    cases hr
    exact ⟨rfl, fun _ => (apply_permutation'_one state.stack hlen).symm, fun _ _ => rfl, by simp⟩

-- `expected x` is the value that offset `x` must receive. Every slot holds the value of its
-- destination, every bound offset expects the value of the slot's destination, a slot below
-- the top that already holds its expected value stays, and no cycle away from the top moves an offset expecting the
-- top's value.
structure GoInv (state : State source target spills) {n : ℕ} (p : Permutation n)
    (expected : ℕ → Option Value) : Prop where
  assigns : ∀ i : Fin n, expected (p i) = state.stack[i.val]?
  bound : ∀ (i : Fin state.stack.length) (j : Fin n) (d : Fin target.length), i.val = j.val →
    state.mapping i = some d → d.val < n → expected d = expected (p j)
  settled : ∀ i : Fin n, i.val + 1 ≠ n → expected i = state.stack[i.val]? → p i = i
  away : ∀ i top : Fin n, top.val + 1 = n → expected i = expected top →
    ∀ c ∈ Permutation.cyclesAwayFromTop p top, c i = i

-- With the top in place, no moving offset expects the top's value.
theorem GoInv.expected_ne_top {state : State source target spills} {n : ℕ} {p : Permutation n}
    {expected : ℕ → Option Value} (h : GoInv state p expected) {top i : Fin n} (htop : top.val + 1 = n)
    (hfix : p top = top) (hi : p i ≠ i) : expected i ≠ expected top := by
  intro he
  have hc : p.cycleOf i ∈ Permutation.cyclesAwayFromTop p top := by
    rw [Permutation.cyclesAwayFromTop_of_fixed p top hfix]
    exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hi)
  exact hi ((Equiv.Perm.cycleOf_apply_self p i).symm.trans (h.away i top htop he _ hc))

-- One step exchanges the destinations of `top` and `pos` in both the mapping and the permutation.
-- The step either places the top (`p top = pos`) or starts a new cycle from a fixed top.
theorem GoInv.step {state next : State source target spills} {p : Permutation state.stack.length}
    {expected : ℕ → Option Value} (h : GoInv state p expected) {top pos : Fin state.stack.length}
    (htop : top.val = state.stack.length - 1) (hcase : p top = pos ∨ p top = top) (hmoved : p pos ≠ pos)
    (hx : Exchanged state next top pos) : GoInv next (p * Equiv.swap top pos) expected := by
  refine ⟨fun i => ?_, fun i j d hij hd hdl => ?_, fun i hi he => ?_, fun i t ht he c hc => ?_⟩
  · rw [Equiv.Perm.mul_apply, h.assigns, hx.stack]
    simp
  · rw [hx.mapping i j hij] at hd
    exact h.bound _ _ d rfl hd hdl
  · rw [hx.stack i] at he
    by_cases hip : i = pos
    · subst hip
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      -- starting a cycle would give `i` the top's value, which no moving offset expects
      refine hcase.resolve_right fun hc => h.expected_ne_top (by omega) hc hmoved ?_
      have ht := h.assigns top
      rw [hc] at ht
      rw [ht]
      simpa using he
    · have hit : i ≠ top := fun e => hi (by rw [e]; omega)
      simp only [Equiv.swap_apply_of_ne_of_ne hit hip] at he
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hit hip]
      exact h.settled i hi (by simp [he])
  · obtain rfl : t = top := Fin.ext (by omega)
    refine h.away i t (by omega) he c ?_
    rcases hcase with hpl | hfix
    · rwa [← hpl, Permutation.cyclesAwayFromTop_place_top] at hc
    · rw [Permutation.cyclesAwayFromTop_swap_pos p t pos hfix] at hc
      rw [Permutation.cyclesAwayFromTop_of_fixed p t hfix]
      exact Finset.mem_of_mem_filter _ hc

-- A slot that `go` swaps with the top is not final: it moves, and a slot below the top that holds its expected value
-- stays.
theorem GoInv.not_final {state : State source target spills} {p : Permutation state.stack.length}
    {expected : ℕ → Option Value} (h : GoInv state p expected) {top pos : Fin state.stack.length}
    (htop : top.val = state.stack.length - 1) (hpos : pos ≠ top) (hmoved : p pos ≠ pos) : ¬state.isFinal pos := by
  intro hf
  obtain ⟨d, hd, hdv⟩ := Option.map_eq_some_iff.mp hf
  have hb := h.bound pos pos d rfl hd (by omega)
  rw [hdv] at hb
  exact hmoved (h.settled pos (fun he => hpos (Fin.ext (by omega))) (hb.trans (h.assigns pos)))

-- `go` never exchanges equal slots. The top's destination expects the top's value, so it would stay if it held that
-- value; a top in place holds its expected value, which the moving destination of a misplaced slot does not expect.
theorem GoInv.ne {state : State source target spills} {p : Permutation state.stack.length}
    {expected : ℕ → Option Value} (h : GoInv state p expected) {top pos : Fin state.stack.length}
    (htop : top.val = state.stack.length - 1) (hpos : pos ≠ top) (hcase : p top = pos ∨ p top = top)
    (hmoved : p pos ≠ pos) : state.stack[top] ≠ state.stack[pos] := by
  intro he
  have hs : state.stack[top.val]? = state.stack[pos.val]? := by
    rw [List.getElem?_eq_getElem top.isLt, List.getElem?_eq_getElem pos.isLt]
    exact congrArg some he
  rcases hcase with hc | hc
  · have ht := h.assigns top
    rw [hc, hs] at ht
    exact hmoved (h.settled pos (fun he => hpos (Fin.ext (by omega))) ht)
  · refine h.expected_ne_top (i := p pos) (by omega) hc (fun h' => hmoved (p.injective h')) ?_
    rw [h.assigns pos, ← hs, ← h.assigns top, hc]

theorem go_ok (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) (expected : ℕ → Option Value)
    (h : GoInv state p expected) : ∃ result, permute.go state p hne = .ok result := by
  refine go_induct hne (motive := fun state p run =>
      state.stack.length = n → GoInv state p expected → ∃ result, run = .ok result)
    ?_ ?_ state p hlen h
  · intro top htop state p pos hpos hmoved hcase ih hlen h
    subst hlen
    rcases exchangeWithTop_cases state top pos htop hpos with
      ⟨_, _, he⟩ | ⟨hbad, _⟩ | ⟨next, hx, he⟩
    · simp only [he, except_ok_bind, Option.isSome_some, ↓reduceIte]
      exact ⟨_, rfl⟩
    · rcases hbad with he | hfinal
      · exact (h.ne htop hpos hcase hmoved he).elim
      · exact (h.not_final htop hpos hmoved hfinal).elim
    · simp only [he, except_ok_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact ih ⟨none, next⟩ hx.length (h.step htop hcase hmoved hx)
  · intro state _ _
    exact ⟨_, rfl⟩

theorem RunSpec.values_of_success {state : State source target spills}
    {p : Permutation state.stack.length} {result : Result source target spills}
    (h : RunSpec state p rfl result) (hs : result.blocked = none) : values_reachable p := by
  intro i hne
  by_contra hd
  have hv := h.deep i hd
  rw [h.applies hs] at hv
  have he : state.stack[p.symm i] = state.stack[i] := by
    simpa [apply_permutation', List.getElem?_eq_getElem i.isLt] using hv
  exact hne he.symm

theorem RunSpec.success_of_reachable {state : State source target spills}
    {p : Permutation state.stack.length} {result : Result source target spills}
    (h : RunSpec state p rfl result) (hr : all_swaps_reachable p) : result.blocked = none := by
  cases hb : result.blocked with
  | none => rfl
  | some b =>
    obtain ⟨i, _, hp, hi, hd⟩ := h.blocked b hb
    have := hr i hi
    simp only [Stack.isSwapReachable] at this hd
    omega

theorem go_count (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) (top : Fin n) (htop : top.val = n - 1) {result : State source target spills}
    (hr : permute.go state p hne = .ok ⟨none, result⟩) :
    result.trace.swapCount ≤ state.trace.swapCount + Permutation.swapCount p top ∧
    (state.stack.Nodup →
      result.trace.swapCount = state.trace.swapCount + Permutation.swapCount p top) := by
  obtain rfl : top = ⟨n - 1, Nat.sub_lt hne Nat.one_pos⟩ := Fin.ext htop
  refine go_induct hne (motive := fun state p run => state.stack.length = n →
      ∀ {result : State source target spills}, run = .ok ⟨none, result⟩ →
      result.trace.swapCount ≤ state.trace.swapCount + Permutation.swapCount p ⟨n - 1, by omega⟩ ∧
      (state.stack.Nodup →
        result.trace.swapCount = state.trace.swapCount + Permutation.swapCount p ⟨n - 1, by omega⟩))
    ?_ ?_ state p hlen hr
  · intro top htop state p pos hpos hmoved hcase ih hlen result hr
    have ht : (⟨n - 1, by omega⟩ : Fin n) = top := Fin.ext htop.symm
    simp only [ht] at ih ⊢
    subst hlen
    have hs : Permutation.swapCount (p * Equiv.swap top pos) top + 1 = Permutation.swapCount p top := by
      rcases hcase with hc | hc
      · rw [← hc]
        exact Permutation.swapCount_place_top p top (by rw [hc]; exact hpos)
      · exact Permutation.swapCount_swap_pos p top pos hc hmoved
    rcases exchangeWithTop_cases state top pos htop hpos with
      ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨next, hx, he⟩
    · simp only [he, except_ok_bind, Option.isSome_some, ↓reduceIte] at hr
      cases hr
    · rw [he, except_error_bind] at hr
      cases hr
    · simp only [he, except_ok_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
      obtain ⟨hle, heq⟩ := ih ⟨none, next⟩ hx.length hr
      dsimp only at hle heq
      have hc := hx.swapCount
      refine ⟨by omega, fun hn => ?_⟩
      have := heq (hx.perm.nodup_iff.mpr hn)
      omega
  · intro state _ result hr
    cases hr
    simp

-- Normalization establishes the invariant of `go` when the bindings agree with `perm`.
theorem normalize_goInv (initial : State source target spills) (perm : Permutation initial.stack.length)
    (hagree : bindings_agree initial perm) :
    GoInv initial (normalize initial.stack perm) (fun x => (apply_permutation initial.stack perm)[x]?) := by
  obtain ⟨ha, hc, hj⟩ := normalize_assigns initial.stack perm
    (fun i => initial.stack[perm.symm i]) (by intro i; simp)
  generalize normalize initial.stack perm = q at *
  have hassigns (i : Fin initial.stack.length) :
      (apply_permutation initial.stack perm)[(q i).val]? = initial.stack[i.val]? := by
    simpa [apply_permutation] using (ha i).symm
  refine ⟨hassigns, ?_, ?_, ?_⟩
  · intro i j d hij hd hlt
    obtain rfl : i = j := Fin.ext hij
    rw [hassigns i]
    simpa [apply_permutation, hlt] using hagree i d hlt hd
  · intro i hi he
    exact hc i hi (by simpa [apply_permutation] using he.symm)
  · -- the slots bound for `i` and the top hold equal values, so they share a cycle with the top
    intro i t ht he c hc
    by_contra hci
    obtain ⟨hcf, hct⟩ := Finset.mem_filter.mp hc
    have hsup := Equiv.Perm.mem_support.mpr hci
    have hiq := Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hcf hsup)
    rw [← Equiv.apply_symm_apply q i, ← Equiv.apply_symm_apply q t, hassigns, hassigns] at he
    have hit := hj (q.symm i) (q.symm t)
      (Or.inl (by rw [Equiv.apply_symm_apply]; exact fun h' => hiq ((Equiv.symm_apply_eq q).mp h'.symm).symm))
      (by by_cases h' : q.symm t = t
          · exact Or.inr (by rw [h']; omega)
          · exact Or.inl fun h'' => h' (by rwa [Equiv.apply_symm_apply, eq_comm] at h''))
      (by simpa using he)
    rw [Equiv.Perm.sameCycle_symm_apply_left, Equiv.Perm.sameCycle_symm_apply_right] at hit
    rw [Equiv.Perm.cycle_is_cycleOf hsup hcf] at hct
    exact Equiv.Perm.mem_support.mp (Equiv.Perm.mem_support_cycleOf_iff.mpr ⟨hit, Equiv.Perm.mem_support.mpr hiq⟩) hct

end Shuffler.Permute
