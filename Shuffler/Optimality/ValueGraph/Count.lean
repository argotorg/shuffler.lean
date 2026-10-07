import Shuffler.Optimality.ValueGraph.CertificateComplete
import Shuffler.Optimality.ValueGraph.CycleCount

namespace Shuffler.Optimality.ValueGraph

variable (source target : Stack) (hlen : source.length = target.length)
    (hcounts : (source : Multiset Value) = (target : Multiset Value))
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source))

include hcounts hprefix

theorem assignment_support :
    (assignment source target hlen).support = (edges source target hlen).toFinset := by
  have hs := circuits_spec source target hlen hcounts hprefix
  have hn := hs.2.nodup_iff.mpr (edges_nodup source target hlen)
  have hl : ∀ cycle ∈ circuits source target hlen, 2 ≤ cycle.length := by
    intro cycle hc
    obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    exact circuits_length source target hlen hcounts hprefix ⟨index, hi⟩
  change (((circuits source target hlen).map List.formPerm).prod)⁻¹.support = _
  rw [Equiv.Perm.support_inv, formPerm_product_support _ hn hl]
  ext i
  simpa only [List.mem_toFinset] using hs.2.mem_iff

omit hcounts in
theorem edges_erase_top (hne : 0 < source.length) :
    ((edges source target hlen).toFinset.erase ⟨source.length - 1, by omega⟩) =
      (mismatchPositions source target hlen).erase ⟨source.length - 1, by omega⟩ := by
  ext i
  simp only [Finset.mem_erase, List.mem_toFinset, mismatchPositions, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hi⟩
    refine ⟨hne, ?_⟩
    intro he
    exact hne (Fin.ext (correct_edge_is_top source target hlen i hi he).1)
  · rintro ⟨hne, hi⟩
    refine ⟨hne, mismatches_subset_edges source target hlen ?_⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange i, decide_eq_true ⟨?_, hi⟩⟩
    by_contra hr
    exact hi (value_eq_of_frozen source target hlen hprefix i hr)

theorem assignment_away_card (hne : 0 < source.length) :
    (Shuffler.Permute.Permutation.cyclesAwayFromTop (assignment source target hlen)
      ⟨source.length - 1, by omega⟩).card =
      (Finset.univ.filter fun group : Fin (circuits source target hlen).length =>
        some group ≠ labels source (circuits source target hlen) source[source.length - 1]).card := by
  have hs := circuits_spec source target hlen hcounts hprefix
  have hn := hs.2.nodup_iff.mpr (edges_nodup source target hlen)
  have hl : ∀ cycle ∈ circuits source target hlen, 2 ≤ cycle.length := by
    intro cycle hc
    obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    exact circuits_length source target hlen hcounts hprefix ⟨index, hi⟩
  change (Shuffler.Permute.Permutation.cyclesAwayFromTop
    (((circuits source target hlen).map List.formPerm).prod)⁻¹ _).card = _
  rw [formPerm_product_inv_away _ hn hl]
  congr 1
  apply Finset.filter_congr
  intro group _
  rw [ne_comm]
  exact (not_congr (circuits_top_label_iff source target hlen hcounts hprefix hne group)).symm

theorem assignment_swapCount (cert : LabelCertificate source target hlen)
    (hcert : certificate source target hlen = some cert) (hne : 0 < source.length) :
    Shuffler.Permute.Permutation.swapCount (assignment source target hlen)
      ⟨source.length - 1, by omega⟩ = cert.bound hne := by
  rw [Shuffler.Permute.Permutation.swapCount,
    assignment_support source target hlen hcounts hprefix,
    edges_erase_top source target hlen hprefix hne,
    assignment_away_card source target hlen hcounts hprefix hne,
    certificate_bound source target hlen cert hcert hne]

end Shuffler.Optimality.ValueGraph
