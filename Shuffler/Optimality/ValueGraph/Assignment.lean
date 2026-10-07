import Shuffler.Optimality.ValueGraph.Euler
import Shuffler.Optimality.ValueGraph.Circuit
import Shuffler.Feasibility.Spec
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn

namespace Shuffler.Optimality.ValueGraph

section Filter

variable {ι : Type}

private theorem counts_cons (endpoint : ι → Value) (edge : ι) (edges : List ι) :
    vertexCounts endpoint (edge :: edges) = {endpoint edge} + vertexCounts endpoint edges := rfl

theorem filter_balance_identity (start finish : ι → Value) (keep : ι → Bool) (edges : List ι)
    (hloop : ∀ edge ∈ edges, keep edge = false → start edge = finish edge) :
    vertexCounts start edges + vertexCounts finish (edges.filter keep) =
      vertexCounts finish edges + vertexCounts start (edges.filter keep) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      have hi := ih (fun next hn => hloop next (List.mem_cons_of_mem _ hn))
      cases hk : keep edge with
      | false =>
          have hs := hloop edge List.mem_cons_self hk
          simp only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte, counts_cons, hs]
          simpa only [add_assoc] using congrArg ({finish edge} + ·) hi
      | true =>
          simp only [List.filter_cons, hk, ↓reduceIte, counts_cons]
          calc
            ({start edge} + vertexCounts start rest) +
                ({finish edge} + vertexCounts finish (rest.filter keep)) =
                ({start edge} + {finish edge}) +
                  (vertexCounts start rest + vertexCounts finish (rest.filter keep)) := by ac_rfl
            _ = ({start edge} + {finish edge}) +
                  (vertexCounts finish rest + vertexCounts start (rest.filter keep)) := by rw [hi]
            _ = _ := by ac_rfl

theorem balanced_filter (start finish : ι → Value) (keep : ι → Bool) (edges : List ι)
    (hb : Balanced start finish edges)
    (hloop : ∀ edge ∈ edges, keep edge = false → start edge = finish edge) :
    Balanced start finish (edges.filter keep) := by
  have hi := filter_balance_identity start finish keep edges hloop
  rw [hb] at hi
  exact (add_left_cancel hi).symm

end Filter

theorem value_eq_of_frozen (source target : Stack) (hlen : source.length = target.length)
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source))
    (i : Fin source.length) (hdeep : ¬i.rev.val ≤ MAX_SWAP_DEPTH) :
    source[i] = target[i.val]'(by omega) := by
  have hi : i.val < Shuffler.Placement.frozen source := by
    dsimp [Shuffler.Placement.frozen, Fin.rev, MAX_SWAP_DEPTH] at *
    omega
  have he := congrArg (fun stack : Stack => stack[i.val]?) hprefix
  simp only [List.getElem?_take_of_lt hi] at he
  simpa only [Fin.getElem_fin, List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem (show i.val < target.length by omega), Option.some.injEq] using he.symm

theorem map_positions (source target : Stack) (hlen : source.length = target.length) :
    (List.finRange source.length).map (fun i => target[i.val]'(by omega)) = target := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hleft hright
    simp

theorem mismatches_balanced (source target : Stack) (hlen : source.length = target.length)
    (hcounts : (source : Multiset Value) = (target : Multiset Value))
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source)) :
    Balanced (fun i : Fin source.length => source[i])
      (fun i => target[i.val]'(by omega)) (mismatches source target hlen) := by
  apply balanced_filter
  · unfold Balanced vertexCounts
    simp only [Fin.getElem_fin]
    rw [map_positions source source rfl, map_positions source target hlen]
    exact hcounts
  · intro i _ hi
    simp only [decide_eq_false_iff_not, not_and, not_not] at hi
    by_cases hreach : i.rev.val ≤ MAX_SWAP_DEPTH
    · exact hi hreach
    · exact value_eq_of_frozen source target hlen hprefix i hreach

theorem edges_balanced (source target : Stack) (hlen : source.length = target.length)
    (hcounts : (source : Multiset Value) = (target : Multiset Value))
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source)) :
    Balanced (fun i : Fin source.length => source[i])
      (fun i => target[i.val]'(by omega)) (edges source target hlen) := by
  have hm := mismatches_balanced source target hlen hcounts hprefix
  unfold edges
  split
  · dsimp only
    split
    · rename_i hn ht
      unfold Balanced vertexCounts at hm ⊢
      simp only [List.map_append, List.map_singleton, ← Multiset.coe_add,
        Multiset.coe_singleton, ht.1, hm]
    · exact hm
  · exact hm

theorem edges_nodup (source target : Stack) (hlen : source.length = target.length) :
    (edges source target hlen).Nodup := by
  have hm : (mismatches source target hlen).Nodup := (List.nodup_finRange _).filter _
  unfold edges
  split
  · dsimp only
    split
    · rename_i hn ht
      apply List.nodup_append.mpr
      refine ⟨hm, by simp, ?_⟩
      intro i hi j hj he
      simp only [List.mem_singleton] at hj
      subst j i
      exact (of_decide_eq_true (List.mem_filter.mp hi).2).2 ht.1
    · exact hm
  · exact hm

theorem circuits_spec (source target : Stack) (hlen : source.length = target.length)
    (hcounts : (source : Multiset Value) = (target : Multiset Value))
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source)) :
    (∀ circuit ∈ circuits source target hlen,
      Circuit (fun i : Fin source.length => source[i]) (fun i => target[i.val]'(by omega)) circuit) ∧
    (circuits source target hlen).flatten.Perm (edges source target hlen) := by
  exact decompose_spec _ _ _ _ (edges_balanced source target hlen hcounts hprefix)
    (edges_nodup source target hlen) le_rfl

theorem mismatches_subset_edges (source target : Stack) (hlen : source.length = target.length) :
    mismatches source target hlen ⊆ edges source target hlen := by
  unfold edges
  split
  · dsimp only
    split
    · exact List.subset_append_left _ _
    · exact List.Subset.refl _
  · exact List.Subset.refl _

theorem value_eq_of_notMem_edges (source target : Stack) (hlen : source.length = target.length)
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source))
    (i : Fin source.length) (hn : i ∉ edges source target hlen) :
    source[i] = target[i.val]'(by omega) := by
  by_cases hreach : i.rev.val ≤ MAX_SWAP_DEPTH
  · by_contra hne
    apply hn
    apply mismatches_subset_edges source target hlen
    exact List.mem_filter.mpr ⟨List.mem_finRange i, by exact decide_eq_true ⟨hreach, hne⟩⟩
  · exact value_eq_of_frozen source target hlen hprefix i hreach

theorem assignment_values (source target : Stack) (hlen : source.length = target.length)
    (hcounts : (source : Multiset Value) = (target : Multiset Value))
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source)) (i : Fin source.length) :
    source[(assignment source target hlen).symm i] = target[i.val]'(by omega) := by
  have hs := circuits_spec source target hlen hcounts hprefix
  have hn := hs.2.nodup_iff.mpr (edges_nodup source target hlen)
  change source[(((circuits source target hlen).map List.formPerm).prod : Equiv.Perm _) i] = _
  by_cases hi : i ∈ (circuits source target hlen).flatten
  · exact (formPerm_product_values _ _ _ hs.1 hn i hi).symm
  · have he := congrArg (fun j : Fin source.length => source[j]) (formPerm_product_fixed _ i hi)
    exact he.trans (value_eq_of_notMem_edges source target hlen hprefix i
      (fun he => hi (hs.2.mem_iff.mpr he)))

-- This theorem proves the executable graph assignment, including its equal
-- occurrences and the optional correct top, has the requested concrete result.
theorem assignment_applies (source target : Stack) (hlen : source.length = target.length)
    (hcounts : (source : Multiset Value) = (target : Multiset Value))
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source)) :
    Shuffler.Permute.apply_permutation source (assignment source target hlen) = target := by
  apply List.ext_getElem
  · simpa only [Shuffler.Permute.apply_permutation, List.length_ofFn] using hlen
  · intro i hi ht
    have his : i < source.length := by omega
    simpa only [Shuffler.Permute.apply_permutation, List.getElem_ofFn] using
      assignment_values source target hlen hcounts hprefix ⟨i, his⟩

end Shuffler.Optimality.ValueGraph
