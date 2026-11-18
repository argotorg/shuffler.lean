module

public import Shuffler.Permute.Normalization
import Shuffler.Permute.Cycles
import Shuffler.Emission.Lemmas

@[expose] public section

namespace Shuffler.Permute

open Emission

theorem apply_permutation'_equal_exchange (stack : Stack) (p : Permutation stack.length)
    (a b : Fin stack.length) (he : stack[a] = stack[b]) :
    apply_permutation' stack (p * Equiv.swap a b) rfl = apply_permutation' stack p rfl := by
  simpa only [swap_eq_of_equal stack a b he] using apply_permutation'_swap stack p rfl a b

theorem support_swap_subset_away {n : ℕ} (p : Equiv.Perm (Fin n)) (top pos i : Fin n)
    (hpos : p pos ≠ pos) (hi : i ≠ top) (hm : i ∈ (p * Equiv.swap top pos).support) :
    i ∈ p.support := by
  by_cases hip : i = pos
  · simpa [hip] using hpos
  · simpa [Equiv.Perm.mem_support, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hi hip] using hm

structure RunSpec (state : State source target spills) {n : ℕ} (p : Permutation n)
    (hlen : state.stack.length = n) (result : Result source target spills) : Prop where
  length : result.state.stack.length = state.stack.length
  applies : result.blocked = none → result.state.stack = apply_permutation' state.stack p hlen
  deep : ∀ i : Fin state.stack.length, ¬ state.isSwapReachable i →
    result.state.stack[i.val]? = state.stack[i.val]?
  blocked : ∀ b, result.blocked = some b →
    ∃ i : Fin state.stack.length, b.offset = i.val ∧ 0 < b.excess ∧
      Fin.cast hlen i ∈ p.support ∧ (state.depthOf i).val = b.excess + MAX_SWAP_DEPTH

theorem RunSpec.equal (state : State source target spills) (p : Permutation state.stack.length)
    (top pos : Fin state.stack.length) (hpos : p pos ≠ pos)
    (htop : top.val = state.stack.length - 1) (he : state.stack[top] = state.stack[pos])
    (next : State source target spills) (hn : next.stack = state.stack)
    (result : Result source target spills)
    (h : RunSpec next (p * Equiv.swap top pos) (congrArg List.length hn) result) :
    RunSpec state p rfl result := by
  cases next with
  | mk planned stack trace mapping pending =>
    dsimp at hn
    subst stack
    refine ⟨h.length, ?_, h.deep, ?_⟩
    · intro hr
      exact (h.applies hr).trans (apply_permutation'_equal_exchange _ _ _ _ he)
    · intro b hb
      obtain ⟨i, hi, hp, hm, hd⟩ := h.blocked b hb
      refine ⟨i, hi, hp, support_swap_subset_away p top pos i hpos ?_ hm, hd⟩
      intro heq
      subst i
      dsimp only at hd
      omega

theorem RunSpec.swap (state : State source target spills) (p : Permutation state.stack.length)
    (top pos : Fin state.stack.length) (hpos : p pos ≠ pos)
    (htop : top.val = state.stack.length - 1) (hreach : state.isSwapReachable pos)
    (next : State source target spills)
    (hn : next.stack = state.stack.swap top.val pos.val)
    (result : Result source target spills)
    (h : RunSpec next (p * Equiv.swap top pos) (by simp [hn]) result) :
    RunSpec state p rfl result := by
  have hlen : next.stack.length = state.stack.length := by simp [hn]
  refine ⟨h.length.trans hlen, ?_, ?_, ?_⟩
  · intro hr
    have ha := h.applies hr
    simpa [hn] using ha.trans (by
      simpa [hn] using apply_permutation'_swap state.stack p rfl top pos)
  · intro i hi
    simp only [Stack.isSwapReachable] at hi
    have hd := h.deep (Fin.cast hlen.symm i) (by
      simp only [Stack.isSwapReachable]; simpa [hlen] using hi)
    have hia : i.val ≠ top.val := by omega
    have hib : i.val ≠ pos.val := by
      simp only [Stack.isSwapReachable] at hreach; omega
    simpa [hn, List.getElem?_eq_getElem i.isLt, hia, hib] using hd
  · intro b hb
    obtain ⟨i, hi, hp, hm, hd⟩ := h.blocked b hb
    dsimp only at hd
    refine ⟨Fin.cast hlen i, hi, hp, ?_, by simpa [hlen] using hd⟩
    apply support_swap_subset_away p top pos _ hpos
    · intro he
      have hiv := congrArg Fin.val he
      simp only [Fin.val_cast] at hiv
      omega
    · exact hm

theorem go_spec (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) :
    ∀ result, permute.go state p hne = .ok result → RunSpec state p hlen result := by
  refine permute.go.induct_unfolding hne
    (motive := fun state p run =>
      ∀ hlen : state.stack.length = n, ∀ result, run = .ok result → RunSpec state p hlen result)
    ?top ?pos ?done state p hlen
  case top =>
    intro state p top ht perm' ih hlen result hr
    subst hlen
    have htop : top.val = state.stack.length - 1 := rfl
    simp only [slotAt_index, except_ok_bind] at hr
    by_cases he : state.stack[p top] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind] at hr
      exact RunSpec.equal state p top (p top) (fun h => ht (p.injective h)) htop he.symm
        { state with mapping := state.mapping.swapDestinations (p top) top } rfl result
        (ih { state with mapping := state.mapping.swapDestinations (p top) top } rfl result hr)
    simp only [he, ↓reduceIte, index_eq, except_ok_bind] at hr
    by_cases hreach : state.isSwapReachable (p top)
    · have hvalid : state.stack.isValidSwapTarget (p top) :=
        ⟨by have := (p top).isLt; have := Fin.val_ne_of_ne ht; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte] at hr
      by_cases hfinal : state.isFinal (p top)
      · obtain ⟨_, hf⟩ := swapWith_final state _ hfinal
        rw [hf, except_error_bind] at hr
        cases hr
      rw [swapWith_result state _ hfinal hvalid, except_ok_bind] at hr
      exact RunSpec.swap state p top (p top) (fun h => ht (p.injective h)) htop hreach _
        (by rw [htop, List.swap_comm]) result (ih _ (by simp) result hr)
    · simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state (p top) hreach] at hr
      cases hr
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp
      · intros; rfl
      · intro b hb
        cases hb
        simp only [Stack.isSwapReachable] at hreach ⊢
        exact ⟨p top, rfl, by omega, by simpa using ht, by omega⟩
  case pos =>
    intro state p top ht search pos hpos hsearch perm' ih hlen result hr
    subst hlen
    have htop : top.val = state.stack.length - 1 := rfl
    simp only [slotAt_index, except_ok_bind] at hr
    by_cases he : state.stack[pos] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind] at hr
      exact RunSpec.equal state p top pos hpos htop he.symm
        { state with mapping := state.mapping.swapDestinations pos top } rfl result
        (ih { state with mapping := state.mapping.swapDestinations pos top } rfl result hr)
    simp only [he, ↓reduceIte, index_eq, except_ok_bind] at hr
    by_cases hreach : state.isSwapReachable pos
    · have hpos_ne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
      have hvalid : state.stack.isValidSwapTarget pos :=
        ⟨by have := pos.isLt; have := Fin.val_ne_of_ne hpos_ne; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte] at hr
      by_cases hfinal : state.isFinal pos
      · obtain ⟨_, hf⟩ := swapWith_final state _ hfinal
        rw [hf, except_error_bind] at hr
        cases hr
      rw [swapWith_result state _ hfinal hvalid, except_ok_bind] at hr
      exact RunSpec.swap state p top pos hpos htop hreach _
        (by rw [htop, List.swap_comm]) result (ih _ (by simp) result hr)
    · simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state pos hreach] at hr
      cases hr
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp
      · intros; rfl
      · intro b hb
        cases hb
        simp only [Stack.isSwapReachable] at hreach ⊢
        exact ⟨pos, rfl, by omega, by simpa using hpos, by omega⟩
  case done =>
    intro state p _ _ search hsearch hlen result hr
    cases hr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro _
      simpa [foldl_find_out_of_place_eq_one p hsearch] using (apply_permutation'_one state.stack hlen).symm
    · intros; rfl
    · simp

-- `expected x` is the value that offset `x` must receive. Every slot holds the value of its
-- destination, every bound offset expects the value of the slot's destination, and a slot below
-- the top that already holds its expected value stays or is the one the top's cycle returns to.
structure GoInv (state : State source target spills) {n : ℕ} (p : Permutation n)
    (expected : ℕ → Option Value) : Prop where
  assigns : ∀ i : Fin n, expected (p i) = state.stack[i.val]?
  bound : ∀ (i : Fin state.stack.length) (j : Fin n) (d : Fin target.length), i.val = j.val →
    state.mapping i = some d → d.val < n → expected d = expected (p j)
  settled : ∀ i : Fin n, i.val + 1 ≠ n →
    expected i = state.stack[i.val]? → (p i).val = i.val ∨ (p i).val + 1 = n

-- One step exchanges the destinations of `top` and `pos` in both the mapping and the permutation.
-- The step either places the top (`p top = pos`) or starts a new cycle from a fixed top.
theorem GoInv.step {state : State source target spills} {p : Permutation state.stack.length}
    {expected : ℕ → Option Value} (h : GoInv state p expected) (top pos : Fin state.stack.length)
    (htop : top.val + 1 = state.stack.length) (hcase : p top = pos ∨ p top = top)
    (next : State source target spills)
    (hlen : next.stack.length = state.stack.length)
    (hstack : ∀ (i : Fin next.stack.length) (j : Fin state.stack.length), i.val = j.val →
      next.stack[i] = state.stack[Equiv.swap top pos j])
    (hmap : ∀ (i : Fin next.stack.length) (j : Fin state.stack.length), i.val = j.val →
      next.mapping i = state.mapping (Equiv.swap top pos j)) :
    GoInv next (p * Equiv.swap top pos) expected := by
  refine ⟨fun i => ?_, fun i j d hij hd hdl => ?_, fun i hi he => ?_⟩
  · have hi : i.val < next.stack.length := by omega
    rw [Equiv.Perm.mul_apply, h.assigns, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (Equiv.swap top pos i).isLt]
    exact congrArg some (hstack ⟨i.val, hi⟩ i rfl).symm
  · rw [hmap i j hij] at hd
    exact h.bound _ _ d rfl hd hdl
  · have hi' : i.val < next.stack.length := by omega
    rw [List.getElem?_eq_getElem hi', ← Fin.getElem_fin (i := ⟨i.val, hi'⟩), hstack ⟨i.val, hi'⟩ i rfl] at he
    rw [Equiv.Perm.mul_apply]
    have hjt : i ≠ top := fun e => hi (by rw [e]; omega)
    by_cases hjp : i = pos
    · subst hjp
      rw [Equiv.swap_apply_right]
      rcases hcase with hc | hc <;> rw [hc] <;> omega
    · simp only [Equiv.swap_apply_of_ne_of_ne hjt hjp] at he ⊢
      have := h.settled i (by omega) (by simp [he])
      omega

theorem GoInv.not_final_top {state : State source target spills} {p : Permutation state.stack.length}
    {expected : ℕ → Option Value} (h : GoInv state p expected) (top : Fin state.stack.length)
    (hne : ¬state.stack[p top] = state.stack[top]) : ¬state.isFinal (p top) := by
  intro hf
  obtain ⟨d, hd, hdv⟩ := Option.map_eq_some_iff.mp hf
  have hb := h.bound (p top) (p top) d rfl hd (by omega)
  rw [hdv] at hb
  have ht := h.assigns top
  rw [hb, h.assigns (p top), List.getElem?_eq_getElem (p top).isLt, List.getElem?_eq_getElem top.isLt] at ht
  exact hne (Option.some.inj ht)

theorem GoInv.not_final_pos {state : State source target spills} {p : Permutation state.stack.length}
    {expected : ℕ → Option Value} (h : GoInv state p expected) (top pos : Fin state.stack.length)
    (htop : top.val + 1 = state.stack.length) (ht : p top = top) (hpos : p pos ≠ pos) :
    ¬state.isFinal pos := by
  intro hf
  obtain ⟨d, hd, hdv⟩ := Option.map_eq_some_iff.mp hf
  have hb := h.bound pos pos d rfl hd (by omega)
  rw [hdv] at hb
  have hpt : pos ≠ top := fun he => hpos (he ▸ ht)
  rcases h.settled pos (fun he => hpt (Fin.ext (by omega))) (hb.trans (h.assigns pos)) with hs | hs
  · exact hpos (Fin.ext hs)
  · exact hpt (p.injective ((Fin.ext (by omega) : p pos = top).trans ht.symm))

theorem getElem_swap_of_eq (stack : Stack) (a b j : Fin stack.length) (he : stack[a] = stack[b]) :
    stack[Equiv.swap a b j] = stack[j] := by
  by_cases ha : j = a
  · subst ha; simpa using he.symm
  by_cases hb : j = b
  · subst hb; simpa using he
  · simp [Equiv.swap_apply_of_ne_of_ne ha hb]

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

theorem go_ok (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) (expected : ℕ → Option Value) (h : GoInv state p expected) :
    ∃ result, permute.go state p hne = .ok result := by
  refine permute.go.induct_unfolding hne
    (motive := fun state p run => state.stack.length = n → GoInv state p expected → ∃ result, run = .ok result)
    ?top ?pos ?done state p hlen h
  case top =>
    intro state p top ht perm' ih hlen h
    subst hlen
    have htop : top.val = state.stack.length - 1 := rfl
    simp only [slotAt_index, except_ok_bind]
    by_cases he : state.stack[p top] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind]
      exact ih { state with mapping := state.mapping.swapDestinations (p top) top } rfl
        (h.step top (p top) (by omega) (Or.inl rfl)
        { state with mapping := state.mapping.swapDestinations (p top) top } rfl
        (fun i j hij => by
          obtain rfl : i = j := Fin.ext hij
          exact (getElem_swap_of_eq state.stack top (p top) i he.symm).symm)
        (fun i j hij => by
          obtain rfl : i = j := Fin.ext hij
          simp [Equiv.swap_comm]))
    simp only [he, ↓reduceIte, index_eq, except_ok_bind]
    by_cases hreach : state.isSwapReachable (p top)
    · have hvalid : state.stack.isValidSwapTarget (p top) :=
        ⟨by have := (p top).isLt; have := Fin.val_ne_of_ne ht; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte,
        swapWith_result state _ (h.not_final_top top he) hvalid, except_ok_bind]
      exact ih _ (by simp) (h.step top (p top) (by omega) (Or.inl rfl) _ (by simp)
        (fun i j hij => by
          simp only [Equiv.swap_comm top (p top)]
          exact getElem_list_swap state.stack (p top) top i _ j hij)
        (fun i j hij => by
          refine (Mapping.cast_apply _ List.length_swap.symm i).trans ?_
          simp only [Mapping.swapDestinations_apply, Equiv.swap_comm (p top)]
          exact congrArg (fun k => state.mapping (Equiv.swap top (p top) k)) (Fin.ext hij)))
    · simp only [hreach, not_false_eq_true, ↓reduceIte]
      exact ⟨_, blockSwapUnreachable_eq state (p top) hreach⟩
  case pos =>
    intro state p top ht search pos hpos hsearch perm' ih hlen h
    subst hlen
    have htop : top.val = state.stack.length - 1 := rfl
    simp only [slotAt_index, except_ok_bind]
    by_cases he : state.stack[pos] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind]
      exact ih { state with mapping := state.mapping.swapDestinations pos top } rfl
        (h.step top pos (by omega) (Or.inr (not_not.mp ht))
        { state with mapping := state.mapping.swapDestinations pos top } rfl
        (fun i j hij => by
          obtain rfl : i = j := Fin.ext hij
          exact (getElem_swap_of_eq state.stack top pos i he.symm).symm)
        (fun i j hij => by
          obtain rfl : i = j := Fin.ext hij
          simp [Equiv.swap_comm]))
    simp only [he, ↓reduceIte, index_eq, except_ok_bind]
    by_cases hreach : state.isSwapReachable pos
    · have hpos_ne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
      have hvalid : state.stack.isValidSwapTarget pos :=
        ⟨by have := pos.isLt; have := Fin.val_ne_of_ne hpos_ne; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte,
        swapWith_result state _ (h.not_final_pos top pos (by omega) (not_not.mp ht) hpos) hvalid,
        except_ok_bind]
      exact ih _ (by simp) (h.step top pos (by omega) (Or.inr (not_not.mp ht)) _ (by simp)
        (fun i j hij => by
          simp only [Equiv.swap_comm top pos]
          exact getElem_list_swap state.stack pos top i _ j hij)
        (fun i j hij => by
          refine (Mapping.cast_apply _ List.length_swap.symm i).trans ?_
          simp only [Mapping.swapDestinations_apply, Equiv.swap_comm pos]
          exact congrArg (fun k => state.mapping (Equiv.swap top pos k)) (Fin.ext hij)))
    · simp only [hreach, not_false_eq_true, ↓reduceIte]
      exact ⟨_, blockSwapUnreachable_eq state pos hreach⟩
  case done =>
    intro state _ _ _ _ _ _ _
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

theorem Trace.swapCount_cast (h : result = other) (trace : Trace spills source result) :
    (h ▸ trace).swapCount = trace.swapCount := by
  subst h; rfl

theorem go_count (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) (top : Fin n) (htop : top.val = n - 1) {result : State source target spills}
    (hr : permute.go state p hne = .ok ⟨none, result⟩) :
    result.trace.swapCount ≤ state.trace.swapCount + Permutation.swapCount p top ∧
    (state.stack.Nodup → result.trace.swapCount = state.trace.swapCount + Permutation.swapCount p top) := by
  obtain rfl : top = ⟨n - 1, Nat.sub_lt hne Nat.one_pos⟩ := Fin.ext htop
  refine permute.go.induct_unfolding hne
    (motive := fun state p run => state.stack.length = n → ∀ {result : State source target spills},
      run = .ok ⟨none, result⟩ →
      result.trace.swapCount ≤ state.trace.swapCount + Permutation.swapCount p ⟨n - 1, by omega⟩ ∧
      (state.stack.Nodup → result.trace.swapCount = state.trace.swapCount +
        Permutation.swapCount p ⟨n - 1, by omega⟩))
    ?top ?pos ?done state p hlen hr
  case top =>
    intro state p top ht perm' ih hlen result hr
    have ht' : (⟨n - 1, by omega⟩ : Fin n) = top := rfl
    simp only [ht'] at ih ⊢
    subst hlen
    simp only [slotAt_index, except_ok_bind] at hr
    have hs : Permutation.swapCount perm' top + 1 = Permutation.swapCount p top :=
      Permutation.swapCount_place_top p top ht
    by_cases he : state.stack[p top] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind] at hr
      have hle : result.trace.swapCount ≤ state.trace.swapCount + Permutation.swapCount perm' top :=
        (ih { state with mapping := state.mapping.swapDestinations (p top) top } rfl hr).1
      refine ⟨by omega, ?_⟩
      intro hn
      exact (ht (Fin.ext (hn.getElem_inj_iff.mp he))).elim
    simp only [he, ↓reduceIte, index_eq, except_ok_bind] at hr
    by_cases hreach : state.isSwapReachable (p top)
    · have hvalid : state.stack.isValidSwapTarget (p top) :=
        ⟨by have := (p top).isLt; have := Fin.val_ne_of_ne ht; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte] at hr
      by_cases hfinal : state.isFinal (p top)
      · obtain ⟨_, hf⟩ := swapWith_final state _ hfinal
        rw [hf, except_error_bind] at hr
        cases hr
      rw [swapWith_result state _ hfinal hvalid, except_ok_bind] at hr
      obtain ⟨hle, heq⟩ := ih _ (by simp) hr
      have hc : (state.swap (p top) hvalid).trace.swapCount = state.trace.swapCount + 1 :=
        Trace.swapCount_cast _ _
      rw [hc] at hle heq
      refine ⟨by omega, ?_⟩
      intro hn
      have heq := heq ((List.swap_perm _ _ _).nodup_iff.mpr hn)
      omega
    · simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state (p top) hreach] at hr
      cases hr
  case pos =>
    intro state p top ht search pos hpos hsearch perm' ih hlen result hr
    have ht' : (⟨n - 1, by omega⟩ : Fin n) = top := rfl
    simp only [ht'] at ih ⊢
    subst hlen
    simp only [slotAt_index, except_ok_bind] at hr
    have hs : Permutation.swapCount perm' top + 1 = Permutation.swapCount p top :=
      Permutation.swapCount_swap_pos p top pos (not_not.mp ht) hpos
    by_cases he : state.stack[pos] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind] at hr
      have hle : result.trace.swapCount ≤ state.trace.swapCount + Permutation.swapCount perm' top :=
        (ih { state with mapping := state.mapping.swapDestinations pos top } rfl hr).1
      refine ⟨by omega, ?_⟩
      intro hn
      have hp : pos = top := Fin.ext (hn.getElem_inj_iff.mp he)
      exact hpos (by simpa [hp] using not_not.mp ht) |>.elim
    simp only [he, ↓reduceIte, index_eq, except_ok_bind] at hr
    by_cases hreach : state.isSwapReachable pos
    · have hpos_ne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
      have hvalid : state.stack.isValidSwapTarget pos :=
        ⟨by have := pos.isLt; have := Fin.val_ne_of_ne hpos_ne; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte] at hr
      by_cases hfinal : state.isFinal pos
      · obtain ⟨_, hf⟩ := swapWith_final state _ hfinal
        rw [hf, except_error_bind] at hr
        cases hr
      rw [swapWith_result state _ hfinal hvalid, except_ok_bind] at hr
      obtain ⟨hle, heq⟩ := ih _ (by simp) hr
      have hc : (state.swap pos hvalid).trace.swapCount = state.trace.swapCount + 1 :=
        Trace.swapCount_cast _ _
      rw [hc] at hle heq
      refine ⟨by omega, ?_⟩
      intro hn
      have heq := heq ((List.swap_perm _ _ _).nodup_iff.mpr hn)
      omega
    · simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state pos hreach] at hr
      cases hr
  case done =>
    intro state p _ _ search hsearch hlen result hr
    cases hr
    simp [foldl_find_out_of_place_eq_one p hsearch]


-- Normalization establishes the invariant of `go` when the bindings agree with `perm`.
theorem normalize_goInv (initial : State source target spills) (perm : Permutation initial.stack.length)
    (hagree : bindings_agree initial perm) :
    GoInv initial (normalize initial.stack perm) (fun x => (apply_permutation initial.stack perm)[x]?) := by
  obtain ⟨ha, hc⟩ := normalize_assigns initial.stack perm
    (fun i => initial.stack[perm.symm i]) (by intro i; simp)
  generalize normalize initial.stack perm = q at *
  have hassigns (i : Fin initial.stack.length) :
      (apply_permutation initial.stack perm)[(q i).val]? = initial.stack[i.val]? := by
    simpa [apply_permutation] using (ha i).symm
  refine ⟨hassigns, ?_, ?_⟩
  · intro i j d hij hd hlt
    obtain rfl : i = j := Fin.ext hij
    rw [hassigns i]
    simpa [apply_permutation, hlt] using hagree i d hlt hd
  · intro i hi he
    left
    exact congrArg Fin.val (hc i hi (by simpa [apply_permutation] using he.symm))

end Shuffler.Permute
