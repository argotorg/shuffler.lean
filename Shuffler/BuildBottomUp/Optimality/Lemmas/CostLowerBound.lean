import Shuffler.BuildBottomUp.Optimality.Lemmas.Births
import Shuffler.BuildBottomUp.Optimality.Lemmas.GenerationLowerBound

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

-- Without POP every added value stays on the stack, so a DUP repeats a value.
theorem dupCount_eq_zero (trace : Trace spills source result) (hp : trace.noPop)
    (hn : result.Nodup) : dupCount trace = 0 := by
  induction trace with
  | Lit => rfl
  | Pop _ _ => exact False.elim hp
  | Swap _ _ _ _ _ ih => exact ih hp ((List.swap_perm _ _ _).nodup_iff.mp hn)
  | Dup _ _ _ _ _ _ =>
      simp only [List.nodup_append, List.nodup_singleton, true_and] at hn
      exact False.elim (hn.2 _ (List.getElem_mem _) _ (List.mem_singleton_self _) rfl)
  | Push _ _ _ ih | Load _ _ _ ih => exact ih hp (List.nodup_append.mp hn).1

-- Without POP a pushed literal or wildcard stays on the stack.
theorem pushCount_eq_zero (trace : Trace spills source result) (hp : trace.noPop)
    (hv : ∀ value ∈ result, ¬ value.can_be_freely_generated) : pushCount trace = 0 := by
  induction trace with
  | Lit => rfl
  | Pop _ _ => exact False.elim hp
  | Swap _ _ _ _ _ ih =>
      exact ih hp fun value hm => hv value ((List.swap_perm _ _ _).mem_iff.mpr hm)
  | Push _ hfree _ _ => exact False.elim (hv _ (by simp) hfree)
  | Dup _ _ _ _ _ ih | Load _ _ _ ih =>
      exact ih hp fun value hm => hv value (List.mem_append_left _ hm)

-- With one address width for every spill, a trace of SWAPs and LOADs has an exact cost.
theorem cpp_cost_of_loads (address : PushEncoding)
    (trace : Trace spills source result) (hp : trace.noPop)
    (hdup : dupCount trace = 0) (hpush : pushCount trace = 0) :
    traceCost (PrimitiveCosts.cppEstimate fun _ => address) trace =
      ⟨3 * trace.swapCount + 6 * loadCount trace,
        trace.swapCount + (address.cost.bytes + 1) * loadCount trace⟩ := by
  induction trace with
  | Lit => rfl
  | Pop _ _ => exact False.elim hp
  | Dup _ _ _ _ _ _ => simp [dupCount] at hdup
  | Push _ _ _ _ => simp [pushCount] at hpush
  | Swap _ _ _ _ _ ih | Load _ _ _ ih =>
      simp only [dupCount, pushCount] at hdup hpush
      rw [traceCost, ih hp hdup hpush]
      simp only [Trace.swapCount, loadCount, Cost.add,
        PrimitiveCosts.cppEstimate, PrimitiveCosts.evm, Cost.mk.injEq]
      constructor <;> ring

end Shuffler.Optimality.BBU
