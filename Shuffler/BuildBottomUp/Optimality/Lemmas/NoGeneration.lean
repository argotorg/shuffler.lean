import Shuffler.BuildBottomUp.Optimality.Lemmas.ActionCounts
import Shuffler.BuildBottomUp.Optimality.Lemmas.PermuteBound
import Shuffler.BuildBottomUp.Lemmas.StaticTerminal

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp Shuffler.Permute

-- When every target offset is final, the stack already has the target order.
private theorem toPermutation_eq_one {state : State source target spills}
    (inv : state.invariant cursor) (hdone : target.length ≤ cursor)
    (hlen : state.stack.length = target.length) (hsource : ∀ i, (state.mapping i).isSome) :
    state.mapping.toPermutation hlen hsource = 1 := by
  ext i
  let j : Fin target.length := Fin.cast hlen i
  have hb : state.mapping.symm j = some i :=
    state.boundOfVal j i (by
      have hf := inv.processed j (by change i.val < cursor; omega)
      rw [State.exists_isFinal_iff, dite_eq_left j.isLt] at hf
      exact hf)
  have he := Mapping.toPermutation_apply state.mapping hlen hsource i
  rw [state.mapping.eq_some_iff.mp hb] at he
  have hv := congrArg Fin.val (Option.some.inj he)
  exact hv

private theorem permute_one_swapCount (spills : SpillSet) (stack : Stack)
    {res : Stack} {trace : Trace spills stack res}
    (hrun : permute spills stack 1 = .ok ⟨res, trace⟩) : trace.swapCount = 0 := by
  by_cases hne : 0 < stack.length
  · rw [permute_swapCount spills stack 1 hne hrun, Permutation.swapCount_one]
  · rw [permute, dite_eq_right hne] at hrun
    cases hrun
    rfl

-- With no pending generation, the loop skips final offsets and then runs
-- Permute once on the unchanged stack, or returns the unchanged state.
theorem loop_permute_trace (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor) (hz : state.pending_generations = 0)
    (hlen : state.stack.length = target.length) (hsource : ∀ i, (state.mapping i).isSome) :
    Spec (buildBottomUp.loop cursor state) (fun result =>
      ∃ (res : Stack) (trace : Trace spills state.stack res),
        permute spills state.stack (state.mapping.toPermutation hlen hsource) =
          .ok ⟨res, trace⟩ ∧
        result.2.swapCount = state.trace.swapCount + trace.swapCount) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    dsimp [Spec, pure, Except.pure]
    have hone := toPermutation_eq_one inv hdone hlen hsource
    have hr : all_swaps_reachable (state.mapping.toPermutation hlen hsource) := by
      intro i hi
      simp [hone] at hi
    obtain ⟨res, trace, hrun, _⟩ :=
      permute_applies_permutation_reachable spills state.stack _ hr
    refine ⟨res, trace, hrun, ?_⟩
    rw [hone] at hrun
    rw [permute_one_swapCount spills state.stack hrun, Nat.add_zero]
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact loop_permute_trace (cursor + 1) state (inv.advance hfinal) hz hlen hsource
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  simp only [hz, ↓reduceIte, requires_of_true _ hlen, except_ok_bind]
  rw [requires_of_true (∀ i, (state.destinationOf i).isSome) hsource, except_ok_bind]
  cases hperm : permute spills state.stack (state.mapping.toPermutation hlen hsource) with
  | error err =>
    cases err
    simp [Except.mapError, Spec]
  | ok result =>
    obtain ⟨res, trace⟩ := result
    simp only [Except.mapError, except_ok_bind, Spec, pure, Except.pure]
    exact ⟨res, trace, rfl, swapCount_concat _ _⟩
termination_by target.length - cursor

private theorem complete_of_pending_zero {initial : State source target spills}
    (h : initial.Valid) (hz : initial.pending_generations = 0) :
    initial.stack.length = target.length ∧ ∀ i, (initial.mapping i).isSome := by
  have ht : ∀ j, (initial.mapping.symm j).isSome :=
    (Mapping.unmapped_target_slots_eq_zero initial.mapping).mp (h.pending.trans hz)
  have hs := h.size
  exact initial.mapping.complete_of_target_total (by omega) ht

-- A successful run with no pending generation appends exactly the Permute
-- trace of the initial mapping.
theorem buildBottomUp_permute_trace_of_pending_zero (initial : State source target spills)
    (h : initial.Valid) (hz : initial.pending_generations = 0)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result,trace⟩) :
    ∃ (hlen : initial.stack.length = target.length) (hsource : ∀ i, (initial.mapping i).isSome)
      (res : Stack) (suffix : Trace spills initial.stack res),
      permute spills initial.stack (initial.mapping.toPermutation hlen hsource) =
        .ok ⟨res, suffix⟩ ∧
      trace.swapCount = initial.trace.swapCount + suffix.swapCount := by
  obtain ⟨hlen, hsource⟩ := complete_of_pending_zero h hz
  have hs := loop_permute_trace 0 initial (State.invariant.initial h) hz hlen hsource
  rw [loop_eq_of_ok hrun] at hs
  exact ⟨hlen, hsource, hs⟩

-- With no pending generation, a successful run emits at most s + s / 2 new
-- swaps, where s = min initial.stack.length 17 - 1.
theorem buildBottomUp_swap_le_of_pending_zero (initial : State source target spills)
    (h : initial.Valid) (hz : initial.pending_generations = 0)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result,trace⟩) :
    trace.swapCount ≤ initial.trace.swapCount + permuteSwapBound initial.stack.length := by
  obtain ⟨_, _, _, suffix, hperm, hcount⟩ :=
    buildBottomUp_permute_trace_of_pending_zero initial h hz hrun
  have hb := permute_swapCount_le_window spills initial.stack _ hperm
  omega

-- Appending a swap of two fixed slots below a fixed top adds one two-cycle away from the top.
private theorem swapCount_mul_swap_of_fixed {ι : Type} [Fintype ι] [DecidableEq ι]
    (perm : Equiv.Perm ι) (top a b : ι) (hab : a ≠ b) (hta : top ≠ a) (htb : top ≠ b)
    (ht : perm top = top) (ha : perm a = a) (hb : perm b = b) :
    Permutation.swapCount (perm * Equiv.swap a b) top = Permutation.swapCount perm top + 3 := by
  have h1 := Permutation.swapCount_swap_pos (perm * Equiv.swap a b) top a
    (by simp [Equiv.swap_apply_of_ne_of_ne hta htb, ht]) (by simp [hb, hab.symm])
  have e2 : (perm * Equiv.swap a b * Equiv.swap top a) top = b := by simp [hb]
  have h2 := Permutation.swapCount_place_top (perm * Equiv.swap a b * Equiv.swap top a) top
    (by rw [e2]; exact htb.symm)
  rw [e2] at h2
  have e3 : (perm * Equiv.swap a b * Equiv.swap top a * Equiv.swap top b) top = a := by
    simp [Equiv.swap_apply_of_ne_of_ne htb.symm hab.symm, ha]
  have h3 := Permutation.swapCount_place_top
    (perm * Equiv.swap a b * Equiv.swap top a * Equiv.swap top b) top (by rw [e3]; exact hta.symm)
  rw [e3] at h3
  have e4 : perm * Equiv.swap a b * Equiv.swap top a * Equiv.swap top b * Equiv.swap top a =
      perm := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  rw [e4] at h3
  omega

-- The swap of the slots at depths a and b, or the identity when one is out of range.
def depthSwap (length a b : Nat) : Equiv.Perm (Fin length) :=
  if h : a < length ∧ b < length then
    Equiv.swap ⟨length - 1 - a, by omega⟩ ⟨length - 1 - b, by omega⟩
  else 1

private theorem depthSwap_apply_of_ne (length a b : Nat) (i : Fin length)
    (ha : length - 1 - i.val ≠ a) (hb : length - 1 - i.val ≠ b) :
    depthSwap length a b i = i := by
  unfold depthSwap
  split_ifs with h
  · apply Equiv.swap_apply_of_ne_of_ne <;>
    · intro he
      rw [Fin.ext_iff] at he
      dsimp only at he
      omega
  · rfl

-- k swaps of the depth pairs (2m + 1 + e, 2m + 2 + e) for m < k.
def depthPairs (length e : Nat) : Nat → Equiv.Perm (Fin length)
  | 0 => 1
  | k + 1 => depthPairs length e k * depthSwap length (2 * k + 1 + e) (2 * k + 2 + e)

private theorem depthPairs_apply (length e k : Nat) (i : Fin length)
    (hi : length - 1 - i.val ≤ e ∨ 2 * k + e < length - 1 - i.val) :
    depthPairs length e k i = i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [depthPairs, Equiv.Perm.mul_apply, depthSwap_apply_of_ne _ _ _ i (by omega) (by omega)]
    exact ih (by omega)

private theorem depthPairs_swapCount (length e k : Nat) (hk : 2 * k + e < length) :
    Permutation.swapCount (depthPairs length e k) ⟨length - 1, by omega⟩ = 3 * k := by
  induction k with
  | zero => simp [depthPairs]
  | succ k ih =>
    have hpair : depthSwap length (2 * k + 1 + e) (2 * k + 2 + e) =
        Equiv.swap ⟨length - 1 - (2 * k + 1 + e), by omega⟩
          ⟨length - 1 - (2 * k + 2 + e), by omega⟩ := by
      rw [depthSwap, dite_eq_left (by omega)]
    rw [depthPairs, hpair, swapCount_mul_swap_of_fixed, ih (by omega)]
    all_goals first
      | omega
      | (apply Fin.ne_of_val_ne; dsimp only; omega)
      | (apply depthPairs_apply; dsimp only; omega)

-- Pair the s = min length 17 - 1 non-top slots inside reach. For odd s,
-- the top and depth one form one more pair.
def worstPermutation (length : Nat) : Equiv.Perm (Fin length) :=
  let reach := min length (MAX_SWAP_DEPTH + 1) - 1
  depthPairs length (reach % 2) (reach / 2) * depthSwap length 0 (reach % 2)

theorem worstPermutation_swapCount (length : Nat) (hne : 0 < length) :
    Permutation.swapCount (worstPermutation length) ⟨length - 1, by omega⟩ =
      permuteSwapBound length := by
  unfold worstPermutation permuteSwapBound
  dsimp only
  have hreach : min length (MAX_SWAP_DEPTH + 1) - 1 < length := by omega
  generalize min length (MAX_SWAP_DEPTH + 1) - 1 = reach at hreach ⊢
  rcases Nat.mod_two_eq_zero_or_one reach with he | he
  · have hone : depthSwap length 0 (reach % 2) = 1 := by
      rw [he, depthSwap, dite_eq_left (by omega), Equiv.swap_self]
      rfl
    rw [hone, mul_one, he, depthPairs_swapCount length 0 (reach / 2) (by omega)]
    omega
  · let top : Fin length := ⟨length - 1, by omega⟩
    let next : Fin length := ⟨length - 1 - 1, by omega⟩
    have hswap : depthSwap length 0 (reach % 2) = Equiv.swap top next := by
      rw [he, depthSwap, dite_eq_left (by omega)]
      rfl
    have hpairs : Permutation.swapCount (depthPairs length 1 (reach / 2)) top = 3 * (reach / 2) :=
      depthPairs_swapCount length 1 (reach / 2) (by omega)
    have htop : depthPairs length 1 (reach / 2) top = top :=
      depthPairs_apply length 1 _ top (by dsimp only [top]; omega)
    have hnext : depthPairs length 1 (reach / 2) next = next :=
      depthPairs_apply length 1 _ next (by dsimp only [next]; omega)
    have hmoved : (depthPairs length 1 (reach / 2) * Equiv.swap top next) top = next := by
      simp [hnext]
    have hplace := Permutation.swapCount_place_top
      (depthPairs length 1 (reach / 2) * Equiv.swap top next) top
      (by rw [hmoved]; apply Fin.ne_of_val_ne; dsimp only [top, next]; omega)
    rw [hmoved, mul_assoc, Equiv.swap_mul_self, mul_one] at hplace
    rw [hswap, he]
    change Permutation.swapCount (depthPairs length 1 (reach / 2) * Equiv.swap top next) top = _
    omega

theorem worstPermutation_reachable (source : Stack) :
    all_swaps_reachable (source := source) (worstPermutation source.length) := by
  intro i hi
  rw [Equiv.Perm.mem_support] at hi
  rw [Fin.val_rev]
  by_contra hdeep
  apply hi
  unfold worstPermutation
  dsimp only
  rw [Equiv.Perm.mul_apply, depthSwap_apply_of_ne _ _ _ i (by omega) (by omega)]
  exact depthPairs_apply _ _ _ i (by omega)

-- The target places source[perm.symm j] at offset j, so slot i moves to perm i.
def permTarget (source : Stack) (perm : Equiv.Perm (Fin source.length)) : Stack :=
  List.ofFn fun j => source[perm.symm j]

def permMapping (source : Stack) (perm : Equiv.Perm (Fin source.length)) :
    Mapping source.length (permTarget source perm).length :=
  (perm.trans (finCongr (by simp [permTarget]))).toPEquiv

def permState (source : Stack) (perm : Equiv.Perm (Fin source.length)) :
    State source (permTarget source perm) ∅ where
  planned_mapping := permMapping source perm
  stack := source
  trace := .Lit source
  mapping := permMapping source perm
  pending_generations := 0

theorem permTarget_length (source : Stack) (perm : Equiv.Perm (Fin source.length)) :
    (permTarget source perm).length = source.length := by
  simp [permTarget]

theorem permTarget_getElem (source : Stack) (perm : Equiv.Perm (Fin source.length))
    (j : Nat) (hj : j < (permTarget source perm).length) :
    (permTarget source perm)[j] =
      source[perm.symm ⟨j, by rw [permTarget_length] at hj; exact hj⟩] := by
  simp [permTarget]

theorem permMapping_apply (source : Stack) (perm : Equiv.Perm (Fin source.length))
    (i : Fin source.length) :
    permMapping source perm i = some (Fin.cast (permTarget_length source perm).symm (perm i)) := by
  rw [permMapping, Equiv.toPEquiv_apply]
  rfl

theorem permMapping_respects (source : Stack) (perm : Equiv.Perm (Fin source.length))
    (i : Fin source.length) (j : Fin (permTarget source perm).length)
    (h : permMapping source perm i = some j) : source[i] = (permTarget source perm)[j] := by
  rw [permMapping_apply, Option.some.injEq] at h
  subst j
  simp [permTarget_getElem]

theorem permState_valid (source : Stack) (perm : Equiv.Perm (Fin source.length)) :
    (permState source perm).Valid := by
  refine ⟨by simp [permState, permTarget_length], ?_, ?_⟩
  · apply (Mapping.unmapped_target_slots_eq_zero _).mpr
    intro j
    change ((permMapping source perm).symm j).isSome
    rw [permMapping, ← Equiv.toPEquiv_symm]
    simp
  · intro j
    refine Or.inr (Or.inr ((Stack.shallowestCopyPosition_isSome _ _).mpr ?_))
    change (permTarget source perm)[j] ∈ source
    rw [Fin.getElem_fin, permTarget_getElem]
    exact List.getElem_mem _

theorem permMapping_toPermutation (source : Stack) (perm : Equiv.Perm (Fin source.length))
    (hlen : source.length = (permTarget source perm).length)
    (hsource : ∀ i, (permMapping source perm i).isSome) :
    (permMapping source perm).toPermutation hlen hsource = perm := by
  ext i
  have he := Mapping.toPermutation_apply (permMapping source perm) hlen hsource i
  rw [permMapping_apply, Option.some.injEq, Fin.ext_iff] at he
  exact he

-- A state whose target is a reachable permutation of the stack succeeds. Its
-- run emits exactly the swaps of one Permute call.
theorem buildBottomUp_permState (source : Stack) (perm : Equiv.Perm (Fin source.length))
    (hr : all_swaps_reachable (source := source) perm) :
    ∃ (result : Stack) (trace : Trace ∅ source result) (res : Stack)
      (suffix : Trace ∅ source res),
      buildBottomUp (permState source perm) (permState_valid source perm) =
        .ok ⟨result, trace⟩ ∧
      permute ∅ source perm = .ok ⟨res, suffix⟩ ∧ trace.swapCount = suffix.swapCount := by
  have hvalid := permState_valid source perm
  obtain ⟨hlen, hsource⟩ := complete_of_pending_zero hvalid rfl
  have hperm : (permState source perm).mapping.toPermutation hlen hsource = perm :=
    permMapping_toPermutation source perm hlen hsource
  obtain ⟨⟨result, trace⟩, hrun, _⟩ := (buildBottomUp_success_iff_loop _ hvalid).mpr
    ((loop_success_iff_permutation 0 (permState source perm)
      (State.invariant.initial hvalid) rfl hlen hsource).mpr (by rw [hperm]; exact hr))
  obtain ⟨_, _, res, suffix, hp, hcount⟩ :=
    buildBottomUp_permute_trace_of_pending_zero _ hvalid rfl hrun
  rw [hperm] at hp
  exact ⟨result, trace, res, suffix, hrun, hp,
    by simpa [permState, Trace.swapCount] using hcount⟩

theorem permute_worstPermutation_swapCount (spills : SpillSet) (source : Stack)
    {res : Stack} {trace : Trace spills source res}
    (hrun : permute spills source (worstPermutation source.length) = .ok ⟨res, trace⟩) :
    trace.swapCount = permuteSwapBound source.length := by
  by_cases hne : 0 < source.length
  · rw [permute_swapCount spills source _ hne hrun, worstPermutation_swapCount _ hne]
  · rw [permute, dite_eq_right hne] at hrun
    cases hrun
    have hz : source.length = 0 := by omega
    rw [hz]
    rfl

-- n distinct variables.
def distinctStack (n : Nat) : Stack := List.ofFn fun i : Fin n => .Var ⟨i⟩

-- For each stack length n, distinct variables in the order of worstPermutation
-- give a value-respecting state whose run emits exactly the bound.
theorem permuteSwapBound_attained (n : Nat) :
    ∃ (source target : Stack) (initial : State source target ∅) (hvalid : initial.Valid),
      initial.stack.length = n ∧ initial.pending_generations = 0 ∧
      (∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) ∧
      ∃ (result : Stack) (trace : Trace ∅ source result),
        buildBottomUp initial hvalid = .ok ⟨result, trace⟩ ∧
        trace.swapCount = initial.trace.swapCount + permuteSwapBound n := by
  let source := distinctStack n
  have hl : source.length = n := by simp [source, distinctStack]
  let perm := worstPermutation source.length
  obtain ⟨result, trace, res, suffix, hrun, hp, hcount⟩ :=
    buildBottomUp_permState source perm (worstPermutation_reachable source)
  refine ⟨source, permTarget source perm, permState source perm, permState_valid source perm, hl,
    rfl, permMapping_respects source perm, result, trace, hrun, ?_⟩
  rw [hcount, permute_worstPermutation_swapCount ∅ source hp, hl]
  simp [permState, Trace.swapCount]

end Shuffler.Optimality.BBU
