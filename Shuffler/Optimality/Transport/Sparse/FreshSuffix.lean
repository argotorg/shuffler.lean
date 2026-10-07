import Shuffler.Optimality.Transport.Sparse.Theorems

namespace Shuffler.Optimality.Transport

private theorem sum_min_remaining (q m : Nat) (hq : q ≤ 16) :
    (Finset.range (m / 16 + 1)).sum (fun k => min q (m - 16 * k)) =
      q * (m / 16) + min q (m % 16) := by
  rw [Finset.sum_range_succ]
  have hs : (Finset.range (m / 16)).sum (fun k => min q (m - 16 * k)) = (m / 16) * q := by
    have hconstant : ∀ k ∈ Finset.range (m / 16), min q (m - 16 * k) = q := by
      intro k hk
      have := Finset.mem_range.mp hk
      apply Nat.min_eq_left
      omega
    simpa only [Finset.card_range] using Finset.sum_const_nat hconstant
  rw [hs]
  have hm : m - 16 * (m / 16) = m % 16 := by omega
  rw [hm, Nat.mul_comm (m / 16) q]

private theorem fresh_suffix_surplus (value : Value) (fresh : Stack)
    (hfresh : value ∉ fresh) (q k : Nat) (hq : 0 < q) :
    surplus value (fresh ++ List.replicate q value) (List.replicate q value)
      (q - 1 + 16 * k) = min q (fresh.length - 16 * k) := by
  have hz : (fresh.take (q - 1 + 16 * k + 1)).count value = 0 :=
    List.count_eq_zero_of_not_mem (fun hm => hfresh (List.mem_of_mem_take hm))
  simp only [surplus, List.take_append, List.count_append, List.take_replicate,
    List.count_replicate, beq_self_eq_true, ite_true, hz, Nat.zero_add]
  omega

theorem sparsePotential_fresh_suffix (value : Value) (fresh : Stack)
    (hfresh : value ∉ fresh) (q : Nat) (hpositive : 0 < q) (hq : q ≤ 16) :
    sparsePotential ⟨q - 1, by omega⟩ value (fresh ++ List.replicate q value)
      (List.replicate q value) = q * (fresh.length / 16) + min q (fresh.length % 16) := by
  rw [← sum_min_remaining q fresh.length hq]
  unfold sparsePotential
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun cut _ => cut / 16)
  · intro cut hc
    have hmem := Finset.mem_filter.mp hc
    have hlen := Finset.mem_range.mp hmem.1
    have hmod := hmem.2
    simp only [List.length_append, List.length_replicate] at hlen
    change cut % 16 = q - 1 at hmod
    apply Finset.mem_range.mpr
    omega
  · intro left hl right hr he
    have hleft := (Finset.mem_filter.mp hl).2
    have hright := (Finset.mem_filter.mp hr).2
    change left % 16 = q - 1 at hleft
    change right % 16 = q - 1 at hright
    omega
  · intro k hk
    have hbound := Finset.mem_range.mp hk
    refine ⟨q - 1 + 16 * k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        simp only [List.length_append, List.length_replicate]
        omega
      · change (q - 1 + 16 * k) % 16 = q - 1
        omega
    · omega
  · intro cut hc
    have hmod := (Finset.mem_filter.mp hc).2
    change cut % 16 = q - 1 at hmod
    have he : cut = q - 1 + 16 * (cut / 16) := by omega
    rw [he, fresh_suffix_surplus value fresh hfresh q (cut / 16) hpositive]
    congr 2
    omega

theorem fresh_suffix_old_swaps_le (value : Value) (fresh : Stack) (hfresh : value ∉ fresh)
    (q : Nat) (hq : q ≤ 16)
    (trace : Trace spills (List.replicate q value) (fresh ++ List.replicate q value))
    (hpop : trace.noPop) :
    q * (fresh.length / 16) + min q (fresh.length % 16) ≤ Lineage.upwardCount value trace := by
  by_cases hz : q = 0
  · simp only [hz, Nat.zero_mul, Nat.zero_min, Nat.zero_add, Nat.zero_le]
  · have hp : 0 < q := by omega
    rw [← sparsePotential_fresh_suffix value fresh hfresh q hp hq]
    exact sparsePotential_le_upwardCount _ value trace hpop

end Shuffler.Optimality.Transport
