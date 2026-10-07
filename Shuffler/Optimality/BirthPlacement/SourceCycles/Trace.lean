import Shuffler.Optimality.BirthPlacement.SourceCycles.Theorems
import Shuffler.Optimality.BirthPlacement.TracePlan.Extract

namespace Shuffler.Optimality.BirthPlacement.SourceCycles

open Shuffler.Permute.Permutation

-- Record absolute SWAP endpoints in the final token domain.
def traceSwaps (size : Nat) (trace : Trace spills source target)
    (hpop : trace.noPop) (hbound : target.length ≤ size) : List (Fin size × Fin size) := by
  cases trace with
  | Lit => exact []
  | @Swap previous depth hlen hlo hhi earlier =>
    let earlierSwaps := traceSwaps size earlier hpop (by simpa only [List.length_swap] using hbound)
    exact earlierSwaps ++ [(⟨previous.length - 1, by simp only [List.length_swap] at hbound; omega⟩,
      ⟨previous.length - 1 - depth, by simp only [List.length_swap] at hbound; omega⟩)]
  | @Dup previous depth hlen hlo hhi earlier =>
    exact traceSwaps size earlier hpop (by simp only [List.length_append, List.length_singleton] at hbound; omega)
  | Pop _ _ => exact False.elim hpop
  | @Push previous value hfree earlier =>
    exact traceSwaps size earlier hpop (by simp only [List.length_append, List.length_singleton] at hbound; omega)
  | @Load previous id hspill earlier =>
    exact traceSwaps size earlier hpop (by simp only [List.length_append, List.length_singleton] at hbound; omega)
termination_by structural trace

theorem traceSwaps_length (size : Nat) (trace : Trace spills source target)
    (hpop : trace.noPop) (hbound : target.length ≤ size) :
    (traceSwaps size trace hpop hbound).length = trace.swapCount := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ earlier ih =>
    simp only [traceSwaps, Trace.swapCount, List.length_append, List.length_singleton]
    exact congrArg (· + 1) (ih hpop _)
  | Dup _ _ _ _ earlier ih | Push _ _ earlier ih | Load _ _ earlier ih =>
    simpa only [traceSwaps, Trace.swapCount] using ih hpop _
  | Pop _ _ => exact False.elim hpop

theorem traceSwaps_top (size : Nat) (trace : Trace spills source target)
    (hpop : trace.noPop) (hbound : target.length ≤ size) :
    ∀ step ∈ traceSwaps size trace hpop hbound, source.length - 1 ≤ step.1.val := by
  induction trace with
  | Lit => simp [traceSwaps]
  | @Swap previous depth hlen hlo hhi earlier ih =>
    intro step hs
    simp only [traceSwaps, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact ih hpop _ step hs
    · have hl := earlier.noPop_length_le hpop
      change source.length - 1 ≤ previous.length - 1
      omega
  | Dup _ _ _ _ earlier ih | Push _ _ earlier ih | Load _ _ earlier ih =>
    simpa only [traceSwaps] using ih hpop _
  | Pop _ _ => exact False.elim hpop

private theorem permutation_cast_births {births otherBirths current : Stack} {swaps size : Nat}
    (hb : births = otherBirths)
    (ht : TokenFrame births current swaps size = TokenFrame otherBirths current swaps size)
    (frame : TokenFrame births current swaps size) :
    (cast ht frame).permutation = frame.permutation := by
  subst otherBirths
  rfl

theorem traceSwaps_permutation (size : Nat) (trace : Trace spills source target)
    (hpop : trace.noPop) (hbound : target.length ≤ size) :
    ((traceSwaps size trace hpop hbound).map fun step => Equiv.swap step.1 step.2).prod =
      (extractTokens size trace hpop hbound).permutation := by
  induction trace with
  | Lit =>
    rw [traceSwaps, extractTokens]
    simp only [List.map_nil, List.prod_nil, eq_mpr_eq_cast]
    erw [permutation_cast_births (List.append_nil source).symm]
    rfl
  | Swap depth hlen hlo hhi earlier ih =>
    simp only [traceSwaps, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    rw [ih hpop _]
    rfl
  | Dup _ _ _ _ earlier ih | Push _ _ earlier ih | Load _ _ earlier ih =>
    rw [traceSwaps, extractTokens]
    dsimp only [id]
    simp only [eq_mp_eq_cast]
    erw [permutation_cast_births (List.append_assoc _ _ _)]
    exact ih hpop _
  | Pop _ _ => exact False.elim hpop

-- This is the production-trace first-touch bound. It does not supply a
-- source plan realizer or an optimizer for the source-entry potential.
theorem trace_selected_pairs_lower_bound (trace : Trace spills source target) (hpop : trace.noPop)
    (pairs : Finset (Fin target.length × Fin target.length))
    (hcycles : ∀ pair ∈ pairs, IsPair (traceAssignment trace hpop) pair)
    (hsource : ∀ pair ∈ pairs, pair.2.val < source.length - 1) :
    arbitrarySwapCount (traceAssignment trace hpop) + 2 * pairs.card ≤ trace.swapCount := by
  let swaps := traceSwaps target.length trace hpop (Nat.le_refl _)
  have hbound := selected_pairs_lower_bound (traceAssignment trace hpop) pairs hcycles swaps
  have htops : ∀ step ∈ swaps, ∀ pair ∈ pairs, Avoids step.1 pair := by
    intro step hs pair hp
    have ht := traceSwaps_top target.length trace hpop (Nat.le_refl _) step hs
    have hpmax := hsource pair hp
    have horder := (hcycles pair hp).1
    constructor <;> intro he
    · have heval := congrArg Fin.val he
      change pair.1.val < pair.2.val at horder
      omega
    · have heval := congrArg Fin.val he
      omega
  have hfinish : traceAssignment trace hpop * (swaps.map fun step => Equiv.swap step.1 step.2).prod = 1 := by
    rw [traceSwaps_permutation]
    exact inv_mul_cancel _
  have hl := traceSwaps_length target.length trace hpop (Nat.le_refl _)
  exact (hbound htops hfinish).trans_eq hl

end Shuffler.Optimality.BirthPlacement.SourceCycles
