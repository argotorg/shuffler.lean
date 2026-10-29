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
    ∃ result, permute.go state p hne = .ok result ∧ RunSpec state p result := by
  refine permute.go.induct_unfolding
    (motive := fun state p _ run => ∃ result, run = .ok result ∧ RunSpec state p result)
    ?equal_top ?blocked_top ?swap_top ?equal_pos ?blocked_pos ?swap_pos ?done state p hne
    <;> intro state p hne top htop <;> intros
  case equal_top ht perm' he ih =>
    obtain ⟨result, hr, hs⟩ := ih
    exact ⟨result, hr, RunSpec.equal state p top (p top) (by simpa using ht) htop he.symm
      { state with mapping := state.mapping.swapDestinations (p top) top } rfl result hs⟩
  case equal_pos ht search pos hpos hsearch perm' he ih =>
    obtain ⟨result, hr, hs⟩ := ih
    exact ⟨result, hr, RunSpec.equal state p top pos hpos htop he.symm
      { state with mapping := state.mapping.swapDestinations pos top } rfl result hs⟩
  case swap_top ht perm' he idx hdepth stack' h1 h2 h3 trace' ih =>
    obtain ⟨result, hr, hs⟩ := ih
    refine ⟨result, hr, RunSpec.swap state p top (p top) (by simpa using ht) htop
      (by omega) _ ?_ result hs⟩
    dsimp [stack', idx, Fin.rev]
    congr 1; omega
  case swap_pos ht search pos hpos hsearch perm' he idx hdepth hpos_ne hlt stack' h1 h2 h3 trace' ih =>
    obtain ⟨result, hr, hs⟩ := ih
    refine ⟨result, hr, RunSpec.swap state p top pos hpos htop (by omega) _ ?_ result hs⟩
    dsimp [stack', idx, Fin.rev]
    congr 1; omega
  case blocked_top ht he idx hdepth =>
    refine ⟨⟨some ⟨(p top).val, idx - MAX_SWAP_DEPTH⟩, state⟩, ?_, rfl, ?_, ?_, ?_⟩
    · simpa only [depthOf_eq_rev] using blockSwapUnreachable_eq state (p top)
        (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)
    · simp
    · intros; rfl
    · intro b hb
      cases hb
      exact ⟨p top, rfl, by change 0 < idx - MAX_SWAP_DEPTH; omega,
        by simpa using ht, by change (p top).rev.val = idx - MAX_SWAP_DEPTH + MAX_SWAP_DEPTH; omega⟩
  case blocked_pos ht search pos hpos hsearch he idx hdepth =>
    refine ⟨⟨some ⟨pos.val, idx - MAX_SWAP_DEPTH⟩, state⟩, ?_, rfl, ?_, ?_, ?_⟩
    · simpa only [depthOf_eq_rev] using blockSwapUnreachable_eq state pos
        (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)
    · simp
    · intros; rfl
    · intro b hb
      cases hb
      exact ⟨pos, rfl, by change 0 < idx - MAX_SWAP_DEPTH; omega,
        by simpa using hpos, by change pos.rev.val = idx - MAX_SWAP_DEPTH + MAX_SWAP_DEPTH; omega⟩
  case done ht search hsearch =>
    refine ⟨⟨none, state⟩, rfl, rfl, ?_, ?_, ?_⟩
    · intro _
      simpa [foldl_find_out_of_place_eq_one p hsearch] using (apply_permutation'_one state.stack rfl).symm
    · intros; rfl
    · simp

theorem RunSpec.values_of_success {state : State source target spills}
    {p : Permutation state.stack} {result : Result source target spills}
    (h : RunSpec state p result) (hs : result.blocked = none) : values_reachable p := by
  intro i hne
  by_contra hd
  have hv := h.deep i (by omega)
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
    omega

theorem Permutation.swapCount_cast {n m : ℕ} (h : n = m) (p : Equiv.Perm (Fin n))
    (hne : 0 < n) :
    Permutation.swapCount (cast (congrArg (fun k => Equiv.Perm (Fin k)) h) p)
        ⟨m - 1, by omega⟩ =
      Permutation.swapCount p ⟨n - 1, by omega⟩ := by
  subst m
  rfl

theorem go_count (state : State source target spills) (p : Permutation state.stack)
    (hne : 0 < state.stack.length) {result : State source target spills}
    (hr : permute.go state p hne = .ok ⟨none, result⟩) :
    result.trace.swapCount ≤ state.trace.swapCount +
      Permutation.swapCount p ⟨state.stack.length - 1, by omega⟩ ∧
    (state.stack.Nodup → result.trace.swapCount = state.trace.swapCount +
      Permutation.swapCount p ⟨state.stack.length - 1, by omega⟩) := by
  refine permute.go.induct_unfolding
    (motive := fun state p hne run => ∀ {result : State source target spills},
      run = .ok ⟨none, result⟩ →
      result.trace.swapCount ≤ state.trace.swapCount +
        Permutation.swapCount p ⟨state.stack.length - 1, by omega⟩ ∧
      (state.stack.Nodup → result.trace.swapCount = state.trace.swapCount +
        Permutation.swapCount p ⟨state.stack.length - 1, by omega⟩))
    ?equal_top ?blocked_top ?swap_top ?equal_pos ?blocked_pos ?swap_pos ?done state p hne hr
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
  case blocked_top ht he idx hdepth result hr =>
    rw [blockSwapUnreachable_eq state (p top)
      (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)] at hr
    cases hr
  case blocked_pos ht search pos hpos hsearch he idx hdepth result hr =>
    rw [blockSwapUnreachable_eq state pos
      (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth)] at hr
    cases hr
  case swap_top ht perm' he idx hdepth stack' h1 h2 h3 trace' ih result hr =>
    obtain ⟨hle, heq⟩ := ih hr
    simp only [eq_mpr_eq_cast] at hle heq
    rw [Permutation.swapCount_cast List.length_swap.symm _ hne] at hle heq
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
  case swap_pos ht search pos hpos hsearch perm' he idx hdepth hpos_ne hlt stack' h1 h2 h3 trace' ih result hr =>
    obtain ⟨hle, heq⟩ := ih hr
    simp only [eq_mpr_eq_cast] at hle heq
    rw [Permutation.swapCount_cast List.length_swap.symm _ hne] at hle heq
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

end Shuffler.Permute
