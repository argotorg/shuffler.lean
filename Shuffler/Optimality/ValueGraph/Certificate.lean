import Shuffler.Optimality.ValueGraph.CertificateDefs
import Shuffler.Optimality.ValueGraph.LowerBound
import Shuffler.Optimality.NoGrowthTrace
import Shuffler.Placement.Build

namespace Shuffler.Optimality.ValueGraph

theorem reverse_permutation_values (source target : Stack)
    (perm : Shuffler.Permute.Permutation source) (hlen : target.length = source.length)
    (h : Shuffler.Permute.apply_permutation' target perm hlen = source) (i : Fin source.length) :
    target[i.val]'(by omega) = source[perm i] := by
  have he := congrArg (fun stack : Stack => stack[(perm i).val]?) h
  simpa only [Shuffler.Permute.apply_permutation', List.getElem?_ofFn,
    dite_eq_left (perm i).isLt, Fin.eta, Equiv.symm_apply_apply,
    List.getElem?_eq_getElem (perm i).isLt, Fin.getElem_fin, Option.some.injEq] using he

-- This lower bound applies to every production trace in the no-POP, exact-H=0
-- comparison set. It does not assume the other trace comes from Permute.
theorem LabelCertificate.bound_le_swapCount (cert : LabelCertificate source target hlen)
    (hne : 0 < source.length) (trace : Trace spills source target)
    (hpop : trace.noPop) (hadd : trace.additions = 0) :
    cert.bound hne ≤ trace.swapCount := by
  obtain ⟨htlen, swaps, hcount, hperm⟩ := noGrowth_swaps trace hpop hadd hne
  let top : Fin source.length := ⟨source.length - 1, by omega⟩
  let perm := (swaps.map (Equiv.swap top)).prod
  have hcompatible (i : Fin source.length) : target[i.val]'(by omega) = source[perm i] :=
    reverse_permutation_values source target perm htlen hperm i
  have hmoved (i : Fin source.length)
      (hm : source[i] ≠ target[i.val]'(by omega)) : perm i ≠ i := by
    intro he
    have hv := hcompatible i
    have hx := congrArg (fun j : Fin source.length => source[j]) he
    exact hm (hv.trans hx).symm
  have hrequired : mismatchPositions source target hlen ⊆ perm.support := by
    intro i hi
    exact Equiv.Perm.mem_support.mpr (hmoved i (Finset.mem_filter.mp hi).2)
  have hstable (i : Fin source.length) : cert.label source[perm i] = cert.label source[i] :=
    (congrArg cert.label (hcompatible i).symm).trans (cert.position_label i).symm
  have hdifferent : Function.Injective (fun group => cert.label source[cert.representative group]) := by
    intro first second he
    simpa only [cert.representative_label, Option.some.injEq] using he
  rw [hcount]
  exact swaps_length_label_lowerBound perm top (mismatchPositions source target hlen) hrequired
    (fun i => cert.label source[i]) hstable cert.representative
    (fun group => hmoved _ (cert.representative_mismatch group)) hdifferent swaps rfl

theorem LabelCertificate.weightedOptimal_of_swapCount (cert : LabelCertificate source target hlen)
    (hne : 0 < source.length) (costs : PrimitiveCosts) (weights : Weights)
    (built : Shuffler.Placement.BuiltTrace spills source target 0)
    (he : built.trace.swapCount = cert.bound hne) :
    WeightedOptimal costs weights 0 built.trace := by
  refine ⟨⟨built.noPop, built.additions⟩, ?_⟩
  intro other hother
  rw [noGrowth_score costs weights built.trace built.noPop built.additions,
    noGrowth_score costs weights other hother.1 hother.2, he]
  exact Nat.mul_le_mul_right _ (cert.bound_le_swapCount hne other hother.1 hother.2)

end Shuffler.Optimality.ValueGraph
