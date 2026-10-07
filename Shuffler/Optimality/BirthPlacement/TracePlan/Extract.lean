import Shuffler.Optimality.BirthPlacement.TracePlan.Frame
import Shuffler.Optimality.SwapRuns

namespace Shuffler.Optimality.BirthPlacement

-- Append a fresh token at each birth. SWAP moves token identities with values.
-- All untouched future positions remain fixed in the ambient permutation.
def extractTokens (size : Nat) (trace : Trace spills source target)
    (hpop : trace.noPop) (hbound : target.length ≤ size) :
    TokenFrame (source ++ SwapRuns.births trace) target trace.swapCount size := by
  cases trace with
  | Lit =>
      simpa only [SwapRuns.births, Trace.swapCount, List.append_nil] using
        TokenFrame.initial source size hbound
  | Swap depth hlen hlo hhi earlier =>
      let frame := extractTokens size earlier hpop (by simpa only [List.length_swap] using hbound)
      exact frame.swap depth hlen hlo (by simpa only [MAX_SWAP_DEPTH] using hhi)
  | @Dup previous depth hlen hlo hhi earlier =>
      have hb : previous.length + 1 ≤ size := by simpa using hbound
      let frame := extractTokens size earlier hpop (by omega)
      let grown := frame.grow previous[previous.length - depth] hb
      simpa only [SwapRuns.births, Trace.swapCount, List.append_assoc] using grown
  | Pop _ _ => exact False.elim hpop
  | @Push previous value hfree earlier =>
      have hb : previous.length + 1 ≤ size := by simpa using hbound
      let frame := extractTokens size earlier hpop (by omega)
      simpa only [SwapRuns.births, Trace.swapCount, List.append_assoc] using frame.grow value hb
  | @Load previous id hspill earlier =>
      have hb : previous.length + 1 ≤ size := by simpa using hbound
      let frame := extractTokens size earlier hpop (by omega)
      simpa only [SwapRuns.births, Trace.swapCount, List.append_assoc] using frame.grow (.Var id) hb
termination_by structural trace

def traceAssignment (trace : Trace spills source target) (hpop : trace.noPop) :
    Equiv.Perm (Fin target.length) :=
  (extractTokens target.length trace hpop (Nat.le_refl _)).permutation.symm

theorem traceAssignment_deadlines (trace : Trace spills source target) (hpop : trace.noPop) :
    BirthDeadlines 16 (traceAssignment trace hpop) := by
  intro index
  let frame := extractTokens target.length trace hpop (Nat.le_refl _)
  have h := frame.backwards (frame.permutation.symm index)
  simpa only [Equiv.apply_symm_apply, frame, traceAssignment] using h

theorem traceAssignment_moved_le (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceAssignment trace hpop).support.card ≤ 2 * trace.swapCount := by
  change ((extractTokens target.length trace hpop (Nat.le_refl _)).permutation⁻¹).support.card ≤ _
  rw [Equiv.Perm.support_inv]
  exact (extractTokens target.length trace hpop (Nat.le_refl _)).moved

theorem traceAssignment_birthWord (trace : Trace spills source target) (hpop : trace.noPop) :
    birthWord target (traceAssignment trace hpop) = source ++ SwapRuns.births trace := by
  let frame := extractTokens target.length trace hpop (Nat.le_refl _)
  apply List.ext_getElem
  · simpa only [birthWord_length] using frame.length.symm
  · intro index hi hj
    have hn : index < target.length := by simpa only [birthWord_length] using hi
    let slot : Fin target.length := ⟨index, hn⟩
    have hv := frame.values (frame.permutation.symm slot)
    simp only [Equiv.apply_symm_apply, slot] at hv
    rw [List.getElem?_eq_getElem (frame.permutation.symm slot).isLt,
      List.getElem?_eq_getElem hj] at hv
    simpa only [birthWord, List.getElem_ofFn, traceAssignment, frame, slot, Fin.getElem_fin] using
      Option.some.inj hv

end Shuffler.Optimality.BirthPlacement
