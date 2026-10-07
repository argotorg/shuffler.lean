import Shuffler.Optimality.PrefixIntroduction.Demand

namespace Shuffler.Optimality.PrefixIntroduction

theorem cutoff_oldCount_le (old source target : Stack) :
    oldCount old (target.take (cutoff old source target)) ≤ oldCount old source - 16 := by
  unfold cutoff oldCount
  rw [← List.countPBefore_eq_countP_take]
  by_cases h : oldCount old source - 16 < oldCount old target
  · have he := List.countPBefore_findIdxNth_of_lt_countP h
    exact Nat.le_of_eq he
  · have hh : oldCount old target ≤ oldCount old source - 16 := by omega
    unfold oldCount at hh
    rw [List.findIdxNth_eq_length_of_ge_countP hh, List.countPBefore_length]
    exact hh

theorem prefixDemand_le_count_add_directCount (old : Stack) (value : Value)
    (trace : Trace spills source target) (hpop : trace.noPop)
    (hlarge : 16 ≤ oldCount old source) (hnotOld : value ∉ old)
    (hbound : oldCount old (target.take cut) ≤ oldCount old source - 16) :
    prefixDemand value target cut ≤ source.count value + Lineage.directCount value trace := by
  have hl := lateDup_of_prefix_bound old value trace hpop hlarge hnotOld (.Lit target)
    (by trivial) hbound
  exact prefixDemand_le_directCount value trace hpop hl

theorem requiredDirect_le_directCount (value : Value) (trace : Trace spills source target)
    (hpop : trace.noPop) :
    requiredDirect value source target ≤ Lineage.directCount value trace := by
  unfold requiredDirect
  dsimp only
  split
  · rename_i hlarge
    have hnot : value ∉ protectedValues value source := by simp [protectedValues]
    have hb := prefixDemand_le_count_add_directCount (protectedValues value source) value trace hpop
      hlarge hnot (cutoff_oldCount_le _ _ _)
    omega
  · exact Nat.zero_le _

end Shuffler.Optimality.PrefixIntroduction
