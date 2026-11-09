module

public import Shuffler.Permute.Normalization
import Shuffler.Permute.Cycles
import Shuffler.Emission.Lemmas

@[expose] public section

namespace Shuffler.Permute

open Emission

theorem swap_equal_values (stack : Stack) (a b : Fin stack.length)
    (he : stack[a] = stack[b]) : stack.swap a.val b.val = stack := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    by_cases ha : i = a.val
    · subst i; simpa using he.symm
    by_cases hb : i = b.val
    · subst i; simpa using he
    · simp [ha, hb]

theorem apply_permutation'_equal_exchange (stack : Stack) (p : Permutation stack)
    (a b : Fin stack.length) (he : stack[a] = stack[b]) :
    apply_permutation' stack (p * Equiv.swap a b) rfl = apply_permutation' stack p rfl := by
  simpa only [swap_equal_values stack a b he] using apply_permutation'_swap stack p rfl a b

theorem support_swap_subset_away {n : ℕ} (p : Equiv.Perm (Fin n)) (top pos i : Fin n)
    (hpos : p pos ≠ pos) (hi : i ≠ top) (hm : i ∈ (p * Equiv.swap top pos).support) :
    i ∈ p.support := by
  by_cases hip : i = pos
  · simpa [hip] using hpos
  · simpa [Equiv.Perm.mem_support, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hi hip] using hm

structure RunSpec (state : State source target spills) (p : Permutation state.stack)
    (result : Result source target spills) : Prop where
  length : result.state.stack.length = state.stack.length
  applies : result.blocked = none → result.state.stack = apply_permutation' state.stack p rfl
  deep : ∀ i : Fin state.stack.length, MAX_SWAP_DEPTH < i.rev.val →
    result.state.stack[i.val]? = state.stack[i.val]?
  blocked : ∀ b, result.blocked = some b →
    ∃ i : Fin state.stack.length, b.offset = i.val ∧ 0 < b.excess ∧
      i ∈ p.support ∧ i.rev.val = b.excess + MAX_SWAP_DEPTH

theorem RunSpec.equal (state : State source target spills) (p : Permutation state.stack)
    (top pos : Fin state.stack.length) (hpos : p pos ≠ pos)
    (htop : top.val = state.stack.length - 1) (he : state.stack[top] = state.stack[pos])
    (next : State source target spills) (hn : next.stack = state.stack)
    (result : Result source target spills)
    (h : RunSpec next (hn.symm ▸ (p * Equiv.swap top pos)) result) : RunSpec state p result := by
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
      dsimp [Fin.rev] at hd
      omega

theorem RunSpec.swap (state : State source target spills) (p : Permutation state.stack)
    (top pos : Fin state.stack.length) (hpos : p pos ≠ pos)
    (htop : top.val = state.stack.length - 1) (hdepth : pos.rev.val ≤ MAX_SWAP_DEPTH)
    (next : State source target spills)
    (hn : next.stack = state.stack.swap top.val pos.val)
    (result : Result source target spills)
    (h : RunSpec next (by simpa [Permutation, hn] using p * Equiv.swap top pos) result) :
    RunSpec state p result := by
  have hlen : next.stack.length = state.stack.length := by simp [hn]
  refine ⟨h.length.trans hlen, ?_, ?_, ?_⟩
  · intro hr
    have ha := h.applies hr
    simp only [eq_mpr_eq_cast] at ha
    rw [apply_permutation'_cast _ hlen.symm] at ha
    simpa [hn] using ha.trans (by
      simpa [hn] using apply_permutation'_swap state.stack p rfl top pos)
  · intro i hi
    have hd := h.deep (Fin.cast hlen.symm i) (by simpa [Fin.rev, hlen] using hi)
    have hia : i.val ≠ top.val := by dsimp [Fin.rev] at hi; omega
    have hib : i.val ≠ pos.val := by intro he; have := Fin.ext he; subst i; omega
    simpa [hn, List.getElem?_eq_getElem i.isLt, hia, hib] using hd
  · intro b hb
    obtain ⟨i, hi, hp, hm, hd⟩ := h.blocked b hb
    refine ⟨Fin.cast hlen i, hi, hp, ?_, by simpa [Fin.rev, hlen] using hd⟩
    apply support_swap_subset_away p top pos _ hpos
    · intro he
      have hiv := congrArg Fin.val he
      simp only [Fin.val_cast] at hiv
      dsimp [Fin.rev] at hd
      omega
    · exact (Permutation.mem_support_cast hlen.symm _ _).mp hm

theorem go_spec (state : State source target spills) (p : Permutation state.stack)
    (hne : 0 < state.stack.length) :
    ∀ result, permute.go state p hne = .ok result → RunSpec state p result := by
  refine permute.go.induct_unfolding
    (motive := fun state p _ run => ∀ result, run = .ok result → RunSpec state p result)
    ?equal_top ?blocked_top ?assert_top ?swap_top ?equal_pos ?blocked_pos ?assert_pos ?swap_pos ?done
    state p hne
    <;> intro state p hne top htop <;> intros
  case equal_top ht perm' he ih result hr =>
    exact RunSpec.equal state p top (p top) (by simpa using ht) htop he.symm
      { state with mapping := state.mapping.swapDestinations (p top) top } rfl result (ih result hr)
  case equal_pos ht search pos hpos hsearch perm' he ih result hr =>
    exact RunSpec.equal state p top pos hpos htop he.symm
      { state with mapping := state.mapping.swapDestinations pos top } rfl result (ih result hr)
  case swap_top ht perm' he hreach hfinal hvalid ih result hr =>
    exact RunSpec.swap state p top (p top) (by simpa using ht) htop
      (by have := not_not.mp hreach; simp only [Stack.isSwapReachable, Fin.val_rev] at this ⊢; omega) _
      (by rw [htop, List.swap_comm]) result (ih result hr)
  case swap_pos ht search pos hpos hsearch perm' he hreach hfinal hpos_ne hvalid ih result hr =>
    exact RunSpec.swap state p top pos hpos htop
      (by have := not_not.mp hreach; simp only [Stack.isSwapReachable, Fin.val_rev] at this ⊢; omega) _
      (by rw [htop, List.swap_comm]) result (ih result hr)
  case assert_top result hr | assert_pos result hr => cases hr
  case blocked_top ht he hreach result hr =>
    rw [blockSwapUnreachable_eq state (p top) hreach] at hr
    cases hr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp
    · intros; rfl
    · intro b hb
      cases hb
      simp only [Stack.isSwapReachable] at hreach ⊢
      exact ⟨p top, rfl, by omega, by simpa using ht, by simp only [Fin.val_rev]; omega⟩
  case blocked_pos ht search pos hpos hsearch he hreach result hr =>
    rw [blockSwapUnreachable_eq state pos hreach] at hr
    cases hr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp
    · intros; rfl
    · intro b hb
      cases hb
      simp only [Stack.isSwapReachable] at hreach ⊢
      exact ⟨pos, rfl, by omega, by simpa using hpos, by simp only [Fin.val_rev]; omega⟩
  case done ht search hsearch result hr =>
    cases hr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro _
      simpa [foldl_find_out_of_place_eq_one p hsearch] using (apply_permutation'_one state.stack rfl).symm
    · intros; rfl
    · simp

-- `expected x` is the value that offset `x` must receive. Every slot holds the value of its
-- destination, every bound offset expects the value of the slot's destination, and a slot below
-- the top that already holds its expected value stays or is the one the top's cycle returns to.
structure GoInv (state : State source target spills) (p : Permutation state.stack)
    (expected : ℕ → Option Value) : Prop where
  assigns : ∀ i, expected (p i) = some state.stack[i]
  bound : ∀ i (d : Fin target.length), state.mapping i = some d → d.val < state.stack.length →
    expected d = expected (p i)
  settled : ∀ i : Fin state.stack.length, i.val + 1 ≠ state.stack.length →
    expected i = some state.stack[i] → (p i).val = i.val ∨ (p i).val + 1 = state.stack.length

-- One step exchanges the destinations of `top` and `pos` in both the mapping and the permutation.
-- The step either places the top (`p top = pos`) or starts a new cycle from a fixed top.
theorem GoInv.step {state : State source target spills} {p : Permutation state.stack}
    {expected : ℕ → Option Value} (h : GoInv state p expected) (top pos : Fin state.stack.length)
    (htop : top.val + 1 = state.stack.length) (hcase : p top = pos ∨ p top = top)
    (next : State source target spills) (p' : Permutation next.stack)
    (hlen : next.stack.length = state.stack.length)
    (hstack : ∀ (i : Fin next.stack.length) (j : Fin state.stack.length), i.val = j.val →
      next.stack[i] = state.stack[Equiv.swap top pos j])
    (hmap : ∀ (i : Fin next.stack.length) (j : Fin state.stack.length), i.val = j.val →
      next.mapping i = state.mapping (Equiv.swap top pos j))
    (hperm : ∀ (i : Fin next.stack.length) (j : Fin state.stack.length), i.val = j.val →
      (p' i).val = (p (Equiv.swap top pos j)).val) :
    GoInv next p' expected := by
  refine ⟨fun i => ?_, fun i d hd hdl => ?_, fun i hi he => ?_⟩
  · rw [hperm i (Fin.cast hlen i) rfl, hstack i (Fin.cast hlen i) rfl]
    exact h.assigns _
  · rw [hmap i (Fin.cast hlen i) rfl] at hd
    rw [hperm i (Fin.cast hlen i) rfl]
    exact h.bound _ d hd (by omega)
  · obtain ⟨j, hj⟩ : ∃ j : Fin state.stack.length, i.val = j.val := ⟨Fin.cast hlen i, rfl⟩
    rw [hperm i j hj]
    rw [hstack i j hj, hj] at he
    have hjt : j ≠ top := fun e => hi (by rw [hj, e]; omega)
    by_cases hjp : j = pos
    · subst hjp
      rw [Equiv.swap_apply_right]
      rcases hcase with hc | hc <;> rw [hc] <;> omega
    · simp only [Equiv.swap_apply_of_ne_of_ne hjt hjp] at he ⊢
      have := h.settled j (by omega) he
      omega

theorem GoInv.not_final_top {state : State source target spills} {p : Permutation state.stack}
    {expected : ℕ → Option Value} (h : GoInv state p expected) (top : Fin state.stack.length)
    (hne : ¬state.stack[p top] = state.stack[top]) : ¬state.isFinal (p top) := by
  intro hf
  obtain ⟨d, hd, hdv⟩ := Option.map_eq_some_iff.mp hf
  have hb := h.bound (p top) d hd (by omega)
  rw [hdv] at hb
  exact hne (Option.some.inj ((h.assigns (p top)).symm.trans (hb.symm.trans (h.assigns top))))

theorem GoInv.not_final_pos {state : State source target spills} {p : Permutation state.stack}
    {expected : ℕ → Option Value} (h : GoInv state p expected) (top pos : Fin state.stack.length)
    (htop : top.val + 1 = state.stack.length) (ht : p top = top) (hpos : p pos ≠ pos) :
    ¬state.isFinal pos := by
  intro hf
  obtain ⟨d, hd, hdv⟩ := Option.map_eq_some_iff.mp hf
  have hb := h.bound pos d hd (by omega)
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

theorem Permutation.cast_apply_val {n m : ℕ} (h : Equiv.Perm (Fin n) = Equiv.Perm (Fin m))
    (hnm : n = m) (perm : Equiv.Perm (Fin n)) (i : Fin m) :
    (cast h perm i).val = (perm (Fin.cast hnm.symm i)).val := by
  subst hnm
  rfl

theorem go_ok (state : State source target spills) (p : Permutation state.stack)
    (hne : 0 < state.stack.length) (expected : ℕ → Option Value) (h : GoInv state p expected) :
    ∃ result, permute.go state p hne = .ok result := by
  refine permute.go.induct_unfolding
    (motive := fun state p _ run => GoInv state p expected → ∃ result, run = .ok result)
    ?equal_top ?blocked_top ?assert_top ?swap_top ?equal_pos ?blocked_pos ?assert_pos ?swap_pos ?done
    state p hne h
    <;> intro state p hne top htop <;> intros
  case equal_top ht perm' he ih h =>
    exact ih (h.step top (p top) (by omega) (Or.inl rfl)
      { state with mapping := state.mapping.swapDestinations (p top) top } perm' rfl
      (fun i j hij => by
        obtain rfl : i = j := Fin.ext hij
        exact (getElem_swap_of_eq state.stack top (p top) i he.symm).symm)
      (fun i j hij => by
        obtain rfl : i = j := Fin.ext hij
        simp [Equiv.swap_comm])
      (fun i j hij => by
        obtain rfl : i = j := Fin.ext hij
        rfl))
  case equal_pos ht search pos hpos hsearch perm' he ih h =>
    exact ih (h.step top pos (by omega) (Or.inr (not_not.mp ht))
      { state with mapping := state.mapping.swapDestinations pos top } perm' rfl
      (fun i j hij => by
        obtain rfl : i = j := Fin.ext hij
        exact (getElem_swap_of_eq state.stack top pos i he.symm).symm)
      (fun i j hij => by
        obtain rfl : i = j := Fin.ext hij
        simp [Equiv.swap_comm])
      (fun i j hij => by
        obtain rfl : i = j := Fin.ext hij
        rfl))
  case swap_top ht perm' he hreach hfinal hvalid ih h =>
    exact ih (h.step top (p top) (by omega) (Or.inl rfl) _ _ (State.swap_length _ _ _)
      (fun i j hij => by
        simp only [Equiv.swap_comm top (p top)]
        exact getElem_list_swap state.stack (p top) top i _ j hij)
      (fun i j hij => by
        refine (Mapping.cast_apply _ List.length_swap.symm i).trans ?_
        simp only [Mapping.swapDestinations_apply, Equiv.swap_comm (p top)]
        exact congrArg (fun k => state.mapping (Equiv.swap top (p top) k)) (Fin.ext hij))
      (fun i j hij => by
        simp only [eq_mpr_eq_cast]
        exact (Permutation.cast_apply_val _ (State.swap_length _ _ _).symm perm' i).trans
          (congrArg (fun k => (perm' k).val) (Fin.ext hij))))
  case swap_pos ht search pos hpos hsearch perm' he hreach hfinal hpos_ne hvalid ih h =>
    exact ih (h.step top pos (by omega) (Or.inr (not_not.mp ht)) _ _ (State.swap_length _ _ _)
      (fun i j hij => by
        simp only [Equiv.swap_comm top pos]
        exact getElem_list_swap state.stack pos top i _ j hij)
      (fun i j hij => by
        refine (Mapping.cast_apply _ List.length_swap.symm i).trans ?_
        simp only [Mapping.swapDestinations_apply, Equiv.swap_comm pos]
        exact congrArg (fun k => state.mapping (Equiv.swap top pos k)) (Fin.ext hij))
      (fun i j hij => by
        simp only [eq_mpr_eq_cast]
        exact (Permutation.cast_apply_val _ (State.swap_length _ _ _).symm perm' i).trans
          (congrArg (fun k => (perm' k).val) (Fin.ext hij))))
  case assert_top ht he hreach hfinal h =>
    exact (h.not_final_top top he hfinal).elim
  case assert_pos ht search pos hpos hsearch he hreach hfinal h =>
    exact (h.not_final_pos top pos (by omega) (not_not.mp ht) hpos hfinal).elim
  case blocked_top ht he hreach h =>
    exact ⟨_, blockSwapUnreachable_eq state (p top) hreach⟩
  case blocked_pos ht search pos hpos hsearch he hreach h =>
    exact ⟨_, blockSwapUnreachable_eq state pos hreach⟩
  case done ht search hsearch h => exact ⟨_, rfl⟩

theorem RunSpec.values_of_success {state : State source target spills}
    {p : Permutation state.stack} {result : Result source target spills}
    (h : RunSpec state p result) (hs : result.blocked = none) : values_reachable p := by
  intro i hne
  by_contra hd
  have hv := h.deep i (by simp only [Stack.isSwapReachable, Fin.val_rev] at hd ⊢; omega)
  rw [h.applies hs] at hv
  have he : state.stack[p.symm i] = state.stack[i] := by
    simpa [apply_permutation', List.getElem?_eq_getElem i.isLt] using hv
  exact hne he.symm

theorem RunSpec.success_of_reachable {state : State source target spills}
    {p : Permutation state.stack} {result : Result source target spills}
    (h : RunSpec state p result) (hr : all_swaps_reachable p) : result.blocked = none := by
  cases hb : result.blocked with
  | none => rfl
  | some b =>
    obtain ⟨i, _, hp, hi, hd⟩ := h.blocked b hb
    have := hr i hi
    simp only [Stack.isSwapReachable, Fin.val_rev] at this hd
    omega

theorem Permutation.swapCount_cast {n m : ℕ} (h : n = m) (p : Equiv.Perm (Fin n))
    (hne : 0 < n) :
    Permutation.swapCount (cast (congrArg (fun k => Equiv.Perm (Fin k)) h) p)
        ⟨m - 1, by omega⟩ =
      Permutation.swapCount p ⟨n - 1, by omega⟩ := by
  subst m
  rfl

theorem Trace.swapCount_cast (h : result = other) (trace : Trace spills source result) :
    (h ▸ trace).swapCount = trace.swapCount := by
  subst h; rfl

theorem go_count (state : State source target spills) (p : Permutation state.stack)
    (hne : 0 < state.stack.length) {result : State source target spills}
    (hr : permute.go state p hne = .ok ⟨none, result⟩) :
    result.trace.swapCount ≤ state.trace.swapCount +
      Permutation.swapCount p (state.stack.topOffset hne) ∧
    (state.stack.Nodup → result.trace.swapCount = state.trace.swapCount +
      Permutation.swapCount p (state.stack.topOffset hne)) := by
  refine permute.go.induct_unfolding
    (motive := fun state p hne run => ∀ {result : State source target spills},
      run = .ok ⟨none, result⟩ →
      result.trace.swapCount ≤ state.trace.swapCount +
        Permutation.swapCount p (state.stack.topOffset hne) ∧
      (state.stack.Nodup → result.trace.swapCount = state.trace.swapCount +
        Permutation.swapCount p (state.stack.topOffset hne)))
    ?equal_top ?blocked_top ?assert_top ?swap_top ?equal_pos ?blocked_pos ?assert_pos ?swap_pos ?done
    state p hne hr
    <;> intro state p hne top htop <;> intros
  case equal_top ht perm' he ih result hr =>
    obtain ⟨hle, heq⟩ := ih hr
    have hs := Permutation.swapCount_place_top p top ht
    change result.trace.swapCount ≤ state.trace.swapCount +
      Permutation.swapCount (p * Equiv.swap top (p top)) top at hle
    refine ⟨by change result.trace.swapCount ≤
      state.trace.swapCount + Permutation.swapCount p top; omega, ?_⟩
    intro hn
    exact (ht (Fin.ext (hn.getElem_inj_iff.mp he))).elim
  case equal_pos ht search pos hpos hsearch perm' he ih result hr =>
    obtain ⟨hle, heq⟩ := ih hr
    have hs := Permutation.swapCount_swap_pos p top pos (not_not.mp ht) hpos
    change result.trace.swapCount ≤ state.trace.swapCount +
      Permutation.swapCount (p * Equiv.swap top pos) top at hle
    refine ⟨by change result.trace.swapCount ≤
      state.trace.swapCount + Permutation.swapCount p top; omega, ?_⟩
    intro hn
    have hp : pos = top := Fin.ext (hn.getElem_inj_iff.mp he)
    exact hpos (by simpa [hp] using not_not.mp ht) |>.elim
  case blocked_top ht he hreach result hr =>
    rw [blockSwapUnreachable_eq state (p top) hreach] at hr
    cases hr
  case blocked_pos ht search pos hpos hsearch he hreach result hr =>
    rw [blockSwapUnreachable_eq state pos hreach] at hr
    cases hr
  case assert_top result hr | assert_pos result hr => cases hr
  case swap_top ht perm' he hreach hfinal hvalid ih result hr =>
    obtain ⟨hle, heq⟩ := ih hr
    have hc : (state.swap (p top) hvalid).trace.swapCount = state.trace.swapCount + 1 :=
      Trace.swapCount_cast _ _
    rw [hc] at hle heq
    simp only [eq_mpr_eq_cast] at hle heq
    rw [Permutation.swapCount_cast (State.swap_length _ _ _).symm _ hne] at hle heq
    have hs := Permutation.swapCount_place_top p top ht
    change result.trace.swapCount ≤ (state.trace.swapCount + 1) +
      Permutation.swapCount (p * Equiv.swap top (p top)) top at hle
    refine ⟨by change result.trace.swapCount ≤ state.trace.swapCount + Permutation.swapCount p top; omega, ?_⟩
    intro hn
    have heq := heq ((List.swap_perm _ _ _).nodup_iff.mpr hn)
    change result.trace.swapCount = (state.trace.swapCount + 1) +
      Permutation.swapCount (p * Equiv.swap top (p top)) top at heq
    change result.trace.swapCount = state.trace.swapCount + Permutation.swapCount p top
    omega
  case swap_pos ht search pos hpos hsearch perm' he hreach hfinal hpos_ne hvalid ih result hr =>
    obtain ⟨hle, heq⟩ := ih hr
    have hc : (state.swap pos hvalid).trace.swapCount = state.trace.swapCount + 1 :=
      Trace.swapCount_cast _ _
    rw [hc] at hle heq
    simp only [eq_mpr_eq_cast] at hle heq
    rw [Permutation.swapCount_cast (State.swap_length _ _ _).symm _ hne] at hle heq
    have hs := Permutation.swapCount_swap_pos p top pos (not_not.mp ht) hpos
    change result.trace.swapCount ≤ (state.trace.swapCount + 1) +
      Permutation.swapCount (p * Equiv.swap top pos) top at hle
    refine ⟨by change result.trace.swapCount ≤ state.trace.swapCount + Permutation.swapCount p top; omega, ?_⟩
    intro hn
    have heq := heq ((List.swap_perm _ _ _).nodup_iff.mpr hn)
    change result.trace.swapCount = (state.trace.swapCount + 1) +
      Permutation.swapCount (p * Equiv.swap top pos) top at heq
    change result.trace.swapCount = state.trace.swapCount + Permutation.swapCount p top
    omega
  case done ht search hsearch result hr =>
    cases hr
    simp [foldl_find_out_of_place_eq_one p hsearch]


-- Normalization establishes the invariant of `go` when the bindings agree with `perm`.
theorem normalize_goInv (initial : State source target spills) (perm : Permutation initial.stack)
    (hagree : bindings_agree initial perm) :
    ∃ q, normalize initial.stack perm = .ok q ∧
      GoInv initial q (fun x => (apply_permutation initial.stack perm)[x]?) := by
  obtain ⟨q, hq, ha, _, hc⟩ := normalize_assigns initial.stack perm
    (fun i => initial.stack[perm.symm i]) (by intro i; simp)
  have hassigns (i : Fin initial.stack.length) :
      (apply_permutation initial.stack perm)[(q i).val]? = some initial.stack[i] := by
    simpa [apply_permutation] using (ha i).symm
  refine ⟨q, hq, ⟨hassigns, ?_, ?_⟩⟩
  · intro i d hd hlt
    rw [hassigns i]
    simpa [apply_permutation, hlt] using hagree i d hlt hd
  · intro i _ he
    left
    exact congrArg Fin.val (hc i (by simpa [apply_permutation] using he.symm))

end Shuffler.Permute
