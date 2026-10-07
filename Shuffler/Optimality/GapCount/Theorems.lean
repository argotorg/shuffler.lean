import Shuffler.Optimality.GapCount.Movement
import Shuffler.Optimality.Lineage.Theorems

namespace Shuffler.Optimality.GapCount

theorem potential_le_of_no_direct (value : Value) (trace : Trace spills source target)
    (hpop : trace.noPop) (hno : Lineage.directCount value trace = 0) :
    potential value target ≤ potential value source + Lineage.upwardCount value trace := by
  induction trace with
  | Lit => simp [Lineage.upwardCount]
  | @Swap previous depth hlen hlo hhi trace ih =>
      have hs := potential_swap value previous (previous.length - 1)
        (previous.length - 1 - depth) (by omega) (by omega)
        (by unfold MAX_SWAP_DEPTH at hhi; omega)
      have hp := ih hpop hno
      simp only [Lineage.upwardCount]
      omega
  | @Dup previous depth hlen hlo hhi trace ih =>
      have hp := ih hpop hno
      simp only [Lineage.upwardCount]
      by_cases hv : previous[previous.length - depth]'(by omega) = value
      · rw [hv, potential_append_dup value previous (previous.length - depth) (by omega) hv
          (by unfold MAX_DUP_DEPTH at hhi; omega)]
        exact hp
      · rw [potential_append_other value _ previous hv]
        exact hp
  | Pop _ _ => exact False.elim hpop
  | Push added hfree trace ih =>
      have hz : Lineage.directCount value trace = 0 := by
        simp only [Lineage.directCount] at hno
        omega
      have hn : added ≠ value := by
        intro he
        simp [Lineage.directCount, he] at hno
      rw [potential_append_other value added _ hn]
      exact ih hpop hz
  | Load id hspill trace ih =>
      have hz : Lineage.directCount value trace = 0 := by
        simp only [Lineage.directCount] at hno
        omega
      have hn : Value.Var id ≠ value := by
        intro he
        simp [Lineage.directCount, he] at hno
      rw [potential_append_other value (.Var id) _ hn]
      exact ih hpop hz

theorem requiredSwaps_le_upwardCount (value : Value) (trace : Trace spills source target)
    (hpop : trace.noPop) (hno : Lineage.directCount value trace = 0) :
    requiredSwaps value source target ≤ Lineage.upwardCount value trace := by
  have hp := potential_le_of_no_direct value trace hpop hno
  unfold requiredSwaps
  omega

end Shuffler.Optimality.GapCount
