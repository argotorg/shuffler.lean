import Shuffler.BuildBottomUp.Optimality.Defs
import Shuffler.BuildBottomUp.Optimality.Lemmas.Excess

/-!
On F1 BBU has excess (2k + 16) · SWAP over B. A trace that permutes the source
first and then loads has excess 16 · SWAP. No factor c gives
C(BBU) - B ≤ c · (OPT - B) for every k.
-/

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

def f1LoadPrice (address : PushEncoding) (weights : Weights) : Nat :=
  (⟨6, address.cost.bytes + 1⟩ : Cost).score weights

def f1SwapPrice (weights : Weights) : Nat := (⟨3, 1⟩ : Cost).score weights

-- With nodup additions absent from the source, B charges a direct price to each.
theorem baseline_of_fresh (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value)
    (hnodup : missing.Nodup) (hfresh : ∀ value ∈ missing, value ∉ source) :
    baseline costs weights spills source missing =
      (missing.map (directPrice costs weights spills)).sum := by
  unfold baseline
  rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, hnodup.dedup, ← Multiset.sum_map_add]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro value hm
  have := unitPrice_le_direct costs weights spills value
  simp only [hfresh value hm, ite_false]
  omega

theorem f1_noPop_additions (trace : Trace (f1Spills k) f1Source (f1Target k)) (hp : trace.noPop) :
    trace.additions.Nodup ∧ trace.additions.card = k ∧
      ∀ value ∈ trace.additions, value ∉ f1Source ∧ ∃ j < 17 + k, value = .Var ⟨j⟩ := by
  have hb := trace.noPop_balance hp
  have hn : ((f1Target k : Stack) : Multiset Value).Nodup := f1Target_nodup k
  rw [hb, Multiset.nodup_add] at hn
  have hl := trace.noPop_length hp
  simp only [f1Source_length, f1Target_length] at hl
  refine ⟨hn.2.1, by omega, fun value hm => ⟨fun hs => Multiset.disjoint_left.mp hn.2.2 (Multiset.mem_coe.mpr hs) hm, ?_⟩⟩
  have ht : value ∈ ((f1Target k : Stack) : Multiset Value) := by
    rw [hb]
    exact Multiset.mem_add.mpr (Or.inr hm)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp ht)
  exact ⟨j.val, j.isLt, rfl⟩

theorem f1_baseline (address : PushEncoding)
    (weights : Weights) (trace : Trace (f1Spills k) f1Source (f1Target k)) (hp : trace.noPop) :
    baseline (f1Costs address) weights (f1Spills k) f1Source trace.additions =
      k * f1LoadPrice address weights := by
  obtain ⟨hnodup, hcard, hvalues⟩ := f1_noPop_additions trace hp
  rw [baseline_of_fresh _ _ _ _ _ hnodup fun value hm => (hvalues value hm).1]
  rw [Multiset.map_congr rfl (g := fun _ => f1LoadPrice address weights), Multiset.map_const',
    Multiset.sum_replicate, hcard, smul_eq_mul]
  intro value hm
  obtain ⟨j, hj, rfl⟩ := (hvalues value hm).2
  have hs : (⟨j⟩ : VarId) ∈ f1Spills k := by simp [f1Spills, hj]
  simp [directPrice, hs, f1Costs, f1LoadPrice, PrimitiveCosts.cppEstimate]

-- Every trace without POP on F1 has only SWAPs and LOADs, so its excess is
-- the SWAP price times its SWAP count.
theorem f1_noPop_excess (address : PushEncoding)
    (weights : Weights) (trace : Trace (f1Spills k) f1Source (f1Target k)) (hp : trace.noPop) :
    (traceCost (f1Costs address) trace).score weights =
      baseline (f1Costs address) weights (f1Spills k) f1Source trace.additions +
        f1SwapPrice weights * trace.swapCount := by
  have hdup := dupCount_eq_zero trace hp (f1Target_nodup k)
  have hpush := pushCount_eq_zero trace hp (by
    intro value hm
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
    exact id)
  have hload : loadCount trace = k := by
    have := births_eq_sum trace
    have := (f1_noPop_additions trace hp).2.1
    omega
  rw [f1_baseline address weights trace hp, f1Costs,
    cpp_cost_of_loads address trace hp hdup hpush, hload]
  simp only [Cost.score, f1LoadPrice, f1SwapPrice]
  ring

private def swapStack (stack : Stack) (idx : Nat) : Stack :=
  stack.swap (stack.length - 1) (stack.length - 1 - idx)

private theorem exists_swaps {origin : Stack} (idxs : List Nat) (prev : Stack)
    (hidx : ∀ idx ∈ idxs, 1 ≤ idx ∧ idx ≤ MAX_SWAP_DEPTH ∧ idx < prev.length)
    (trace : Trace spills origin prev) (hp : trace.noPop) :
    ∃ next : Trace spills origin (idxs.foldl swapStack prev),
      next.noPop ∧ next.swapCount = trace.swapCount + idxs.length := by
  induction idxs generalizing prev with
  | nil => exact ⟨trace, hp, rfl⟩
  | cons idx rest ih =>
      obtain ⟨hlo, hhi, hlen⟩ := hidx idx (by simp)
      obtain ⟨next, hn, hs⟩ := ih (swapStack prev idx)
        (fun i hi => by
          have := hidx i (by simp [hi])
          simpa [swapStack, List.length_swap] using this)
        (.Swap idx hlen hlo hhi trace) hp
      exact ⟨next, hn, hs.trans (by simp only [Trace.swapCount, List.length_cons]; omega)⟩

private theorem f1Target_succ (j : Nat) :
    f1Target (j + 1) = f1Target j ++ [.Var ⟨17 + j⟩] := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [f1Target_getElem]
  rw [List.getElem_append]
  split
  next => simp
  next h =>
    have : i = 17 + j := by simp at h₂ h; omega
    subst this
    simp

-- Sixteen SWAPs order the source. Then one LOAD adds each pending target.
theorem f1_permuteFirst (k : Nat) :
    ∃ trace : Trace (f1Spills k) f1Source (f1Target k), trace.noPop ∧ trace.swapCount = 16 := by
  have hsorted : (List.range' 1 16).reverse.foldl swapStack f1Source = f1Target 0 := by decide
  have hswaps := exists_swaps (spills := f1Spills k) (List.range' 1 16).reverse
    f1Source (by decide) (.Lit f1Source) trivial
  rw [hsorted] at hswaps
  obtain ⟨sorted, hp, hs⟩ := hswaps
  suffices h : ∀ j ≤ k, ∃ trace : Trace (f1Spills k) f1Source (f1Target j),
      trace.noPop ∧ trace.swapCount = 16 from h k le_rfl
  intro j hj
  induction j with
  | zero => exact ⟨sorted, hp, by simpa [Trace.swapCount] using hs⟩
  | succ j ih =>
      obtain ⟨trace, hp, hs⟩ := ih (by omega)
      have hspill : (⟨17 + j⟩ : VarId) ∈ f1Spills k := by simp [f1Spills]; omega
      rw [f1Target_succ]
      exact ⟨.Load _ hspill trace, hp, hs⟩

end Shuffler.Optimality.BBU
