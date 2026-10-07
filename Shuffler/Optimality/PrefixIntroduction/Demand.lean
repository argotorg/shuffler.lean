import Shuffler.Optimality.PrefixIntroduction.LateDup
import Shuffler.Optimality.Lineage.Theorems

namespace Shuffler.Optimality.PrefixIntroduction

open Lineage Shuffler.Placement

private theorem count_take_drop (value : Value) (stack : Stack) (cut : Nat) :
    (stack.take cut).count value + (stack.drop cut).count value = stack.count value := by
  rw [← List.count_append, List.take_append_drop]

theorem prefixDemand_le_count (value : Value) (stack : Stack) (cut : Nat) :
    prefixDemand value stack cut ≤ stack.count value := by
  have hc := count_take_drop value stack cut
  unfold prefixDemand
  split
  · rename_i hm
    have := List.count_pos_iff.mpr hm
    omega
  · omega

theorem LateDup.dupCount_eq_zero_of_short (trace : Trace spills source target)
    (hpop : trace.noPop) (hlate : LateDup cut value trace)
    (hshort : target.length ≤ cut + 16) : dupCount value trace = 0 := by
  induction trace with
  | Lit => rfl
  | Pop _ _ => exact False.elim hpop
  | Swap _ _ _ _ trace ih =>
      exact ih hpop hlate (by simpa using hshort)
  | @Dup previous depth hd hlo hhi trace ih =>
      have hs : previous.length ≤ cut + 16 := by simp only [List.length_append, List.length_singleton] at hshort; omega
      have hz := ih hpop hlate.1 hs
      have hn : previous[previous.length - depth]'(by omega) ≠ value := by
        intro he
        have := hlate.2 he
        omega
      simp [dupCount, hz, hn]
  | Push _ _ trace ih | Load _ _ trace ih =>
      apply ih hpop hlate
      simp only [List.length_append, List.length_singleton] at hshort
      omega

theorem count_eq_of_no_dup (value : Value) (trace : Trace spills source target)
    (hpop : trace.noPop) (hdup : dupCount value trace = 0) :
    target.count value = source.count value + directCount value trace := by
  have hb := congrArg (Multiset.count value) (trace.noPop_balance hpop)
  simp only [Multiset.count_add, Multiset.coe_count, additions_count_eq, hdup, zero_add] at hb
  exact hb

private theorem prefixDemand_eq_of_counts (value : Value) (first second : Stack) (cut : Nat)
    (hp : (first.take cut).count value = (second.take cut).count value)
    (hc : first.count value = second.count value) :
    prefixDemand value first cut = prefixDemand value second cut := by
  have hf := count_take_drop value first cut
  have hs := count_take_drop value second cut
  have hd : (first.drop cut).count value = (second.drop cut).count value := by omega
  have hm : value ∈ first.drop cut ↔ value ∈ second.drop cut := by
    rw [← List.count_pos_iff, ← List.count_pos_iff, hd]
  simp only [prefixDemand, hp, hm]

theorem prefixDemand_swap (value : Value) (stack : Stack) (cut a b : Nat)
    (ha : cut ≤ a) (hb : cut ≤ b) :
    prefixDemand value (stack.swap a b) cut = prefixDemand value stack cut := by
  apply prefixDemand_eq_of_counts
  · rw [take_swap_of_le stack cut a b ha hb]
  · exact (List.swap_perm stack a b).count_eq value

theorem prefixDemand_append_le (value added : Value) (stack : Stack) (cut : Nat) :
    prefixDemand value (stack ++ [added]) cut ≤
      prefixDemand value stack cut + if added = value then 1 else 0 := by
  by_cases hc : cut ≤ stack.length
  · simp only [prefixDemand, List.take_append_of_le_length hc,
      List.drop_append_of_le_length hc, List.mem_append, List.mem_singleton]
    by_cases ha : added = value <;> by_cases hm : value ∈ stack.drop cut <;>
      simp [ha, eq_comm, hm]
    exact Ne.symm ha
  · have hs : stack.length ≤ cut := by omega
    have ht : (stack ++ [added]).length ≤ cut := by simp; omega
    simp only [prefixDemand, List.take_of_length_le hs, List.take_of_length_le ht,
      List.drop_eq_nil_of_le hs, List.drop_eq_nil_of_le ht, List.not_mem_nil, ite_false,
      Nat.add_zero, List.count_append, List.count_singleton]
    simp only [beq_iff_eq]
    exact Nat.le_refl _

theorem prefixDemand_append_of_mem_suffix (value : Value) (stack : Stack) (cut : Nat)
    (hc : cut ≤ stack.length) (hm : value ∈ stack.drop cut) :
    prefixDemand value (stack ++ [value]) cut = prefixDemand value stack cut := by
  simp [prefixDemand, List.take_append_of_le_length hc,
    List.drop_append_of_le_length hc, hm]

theorem prefixDemand_le_directCount (value : Value) (trace : Trace spills source target)
    (hpop : trace.noPop) (hlate : LateDup cut value trace) :
    prefixDemand value target cut ≤ source.count value + directCount value trace := by
  induction trace with
  | Lit => exact prefixDemand_le_count value source cut
  | Pop _ _ => exact False.elim hpop
  | @Swap previous depth hd hlo hhi trace ih =>
      by_cases hs : previous.length ≤ cut + 16
      · have hz := LateDup.dupCount_eq_zero_of_short trace hpop hlate hs
        have hc := count_eq_of_no_dup value trace hpop hz
        have he := (List.swap_perm previous (previous.length - 1) (previous.length - 1 - depth)).count_eq value
        have hp := prefixDemand_le_count value (previous.swap (previous.length - 1)
          (previous.length - 1 - depth)) cut
        simp only [directCount]
        omega
      · rw [prefixDemand_swap]
        · exact ih hpop hlate
        · omega
        · unfold MAX_SWAP_DEPTH at hhi
          omega
  | @Dup previous depth hd hlo hhi trace ih =>
      have hp := ih hpop hlate.1
      by_cases he : previous[previous.length - depth]'(by omega) = value
      · have hh := hlate.2 he
        have hm : value ∈ previous.drop cut := by
          rw [← he]
          exact getElem_mem_drop_of_le previous ⟨previous.length - depth, by omega⟩ cut
            (by dsimp; unfold MAX_DUP_DEPTH at hhi; omega)
        change prefixDemand value (previous ++ [previous[previous.length - depth]'(by omega)]) cut ≤
          source.count value + directCount value trace
        rw [he, prefixDemand_append_of_mem_suffix value previous cut (by omega) hm]
        exact hp
      · have ha := prefixDemand_append_le value (previous[previous.length - depth]'(by omega)) previous cut
        simp only [he, ite_false, Nat.add_zero] at ha
        exact ha.trans hp
  | @Push previous added hfree trace ih =>
      have hp := ih hpop hlate
      have ha := prefixDemand_append_le value added previous cut
      simp only [directCount]
      omega
  | @Load previous id hspill trace ih =>
      have hp := ih hpop hlate
      have ha := prefixDemand_append_le value (.Var id) previous cut
      simp only [directCount]
      omega

end Shuffler.Optimality.PrefixIntroduction
