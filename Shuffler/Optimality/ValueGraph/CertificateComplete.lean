import Shuffler.Optimality.ValueGraph.CertificateDefs
import Shuffler.Optimality.ValueGraph.Assignment
import Shuffler.Optimality.ValueGraph.Separation

namespace Shuffler.Optimality.ValueGraph

private theorem valueDisjoint_indices (source : Stack)
    (cycles : List (List (Fin source.length)))
    (hv : cycles.Pairwise (ValueDisjoint fun i => source[i]))
    (first second : Fin cycles.length) (hne : first ≠ second) :
    ValueDisjoint (fun i => source[i]) cycles[first] cycles[second] := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact List.pairwise_iff_get.mp hv first second h
  · intro i hi j hj he
    exact List.pairwise_iff_get.mp hv second first h j hj i hi he.symm

theorem labels_of_mem (source : Stack) (cycles : List (List (Fin source.length)))
    (hv : cycles.Pairwise (ValueDisjoint fun i => source[i]))
    (group : Fin cycles.length) (position : Fin source.length)
    (hp : position ∈ cycles[group]) : labels source cycles source[position] = some group := by
  have hex : ((List.finRange cycles.length).find? fun group =>
      (cycles[group]).any fun i => source[i] = source[position]).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨group, List.mem_finRange group, List.any_eq_true.mpr ⟨position, hp, by simp⟩⟩
  obtain ⟨other, ho⟩ := Option.isSome_iff_exists.mp hex
  have hi := List.find?_some ho
  obtain ⟨i, hi, he⟩ := List.any_eq_true.mp hi
  have he : source[i] = source[position] := of_decide_eq_true he
  have heq : other = group := by
    by_contra hn
    exact valueDisjoint_indices source cycles hv other group hn i hi position hp he
  simpa only [labels, heq] using ho

theorem decompose_nonempty (start finish : ι → Value) [DecidableEq ι]
    (fuel : Nat) (edges : List ι) (hn : edges.Nodup) :
    ∀ circuit ∈ decompose start finish fuel edges, circuit ≠ [] := by
  induction fuel generalizing edges with
  | zero => simp [decompose]
  | succ fuel ih =>
      cases edges with
      | nil => simp [decompose]
      | cons first rest =>
          intro circuit hc
          rcases List.mem_cons.mp hc with rfl | hc
          · have hp := (tour_partition start finish first (first :: rest)).length_eq
            have hl := tour_remaining_length_lt start finish first rest hn
            intro he
            rw [he] at hp
            simp only [List.nil_append] at hp
            omega
          · exact ih _ ((List.nodup_append.mp
              ((tour_partition start finish first (first :: rest)).nodup_iff.mpr hn)).2.1) _ hc

section Feasible

variable (source target : Stack) (hlen : source.length = target.length)
    (hcounts : (source : Multiset Value) = (target : Multiset Value))
    (hprefix : target.take (Shuffler.Placement.frozen source) =
      source.take (Shuffler.Placement.frozen source))

include hcounts hprefix

theorem circuits_valueDisjoint :
    (circuits source target hlen).Pairwise (ValueDisjoint fun i => source[i]) :=
  decompose_valueDisjoint _ _ _ _ (edges_balanced source target hlen hcounts hprefix)
    (edges_nodup source target hlen)

theorem circuits_label_of_mem (group : Fin (circuits source target hlen).length)
    (position : Fin source.length) (hp : position ∈ (circuits source target hlen)[group]) :
    labels source (circuits source target hlen) source[position] = some group :=
  labels_of_mem source _ (circuits_valueDisjoint source target hlen hcounts hprefix) group position hp

theorem circuits_position_label (position : Fin source.length) :
    labels source (circuits source target hlen) source[position] =
      labels source (circuits source target hlen) (target[position.val]'(by omega)) := by
  have hs := circuits_spec source target hlen hcounts hprefix
  by_cases hp : position ∈ edges source target hlen
  · obtain ⟨cycle, hc, hp⟩ := List.mem_flatten.mp (hs.2.mem_iff.mpr hp)
    obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    let group : Fin (circuits source target hlen).length := ⟨index, hi⟩
    have hn := (List.nodup_flatten.mp (hs.2.nodup_iff.mpr (edges_nodup source target hlen))).1
      _ (List.getElem_mem hi)
    have he := Circuit.formPerm _ _ _ (hs.1 _ (List.getElem_mem hi)) hn position hp
    have hm := List.formPerm_mem_iff_mem.mpr hp
    rw [circuits_label_of_mem source target hlen hcounts hprefix group position hp, he,
      circuits_label_of_mem source target hlen hcounts hprefix group _ hm]
  · rw [value_eq_of_notMem_edges source target hlen hprefix position hp]

omit hcounts hprefix in
theorem correct_edge_is_top (i : Fin source.length)
    (hm : i ∈ edges source target hlen) (he : source[i] = target[i.val]'(by omega)) :
    i.val = source.length - 1 ∧
      ∃ next ∈ mismatches source target hlen,
        source[next] = source[i] ∨ target[next.val]'(by omega) = source[i] := by
  have hnot : i ∉ mismatches source target hlen := by
    intro hi
    exact (of_decide_eq_true (List.mem_filter.mp hi).2).2 he
  unfold edges at hm
  split at hm
  · dsimp only at hm
    split at hm
    · rename_i hn ht
      have hitop := (List.mem_append.mp hm).resolve_left hnot
      simp only [List.mem_singleton] at hitop
      subst i
      exact ⟨rfl, by simpa only [List.any_eq_true, decide_eq_true_eq] using ht.2⟩
    · contradiction
  · contradiction

theorem circuits_has_mismatch (group : Fin (circuits source target hlen).length) :
    ∃ position ∈ (circuits source target hlen)[group],
      source[position] ≠ target[position.val]'(by omega) := by
  have hs := circuits_spec source target hlen hcounts hprefix
  have hnonempty := decompose_nonempty _ _ _ _ (edges_nodup source target hlen)
    _ (List.getElem_mem group.isLt)
  obtain ⟨position, hp⟩ := List.exists_mem_of_ne_nil _ hnonempty
  by_contra hex
  have hcorrect : ∀ i ∈ (circuits source target hlen)[group],
      source[i] = target[i.val]'(by omega) := by simpa using hex
  have he := hs.2.mem_iff.mp (List.mem_flatten.mpr ⟨_, List.getElem_mem group.isLt, hp⟩)
  obtain ⟨_, next, hn, hv⟩ := correct_edge_is_top source target hlen position he (hcorrect _ hp)
  have hnext := (of_decide_eq_true (List.mem_filter.mp hn).2).2
  have hne := mismatches_subset_edges source target hlen hn
  obtain ⟨cycle, hc, hm⟩ := List.mem_flatten.mp (hs.2.mem_iff.mpr hne)
  obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  let other : Fin (circuits source target hlen).length := ⟨index, hi⟩
  have hl : labels source (circuits source target hlen) source[next] =
      labels source (circuits source target hlen) source[position] := by
    rcases hv with hv | hv
    · rw [hv]
    · rw [circuits_position_label source target hlen hcounts hprefix next, hv]
  rw [circuits_label_of_mem source target hlen hcounts hprefix other next hm,
    circuits_label_of_mem source target hlen hcounts hprefix group position hp] at hl
  have hg : other = group := Option.some.inj hl
  have hm' : next ∈ (circuits source target hlen)[group] := hg ▸ hm
  exact hnext (hcorrect next hm')

theorem circuits_length (group : Fin (circuits source target hlen).length) :
    2 ≤ ((circuits source target hlen)[group]).length := by
  obtain ⟨position, hp, hm⟩ := circuits_has_mismatch source target hlen hcounts hprefix group
  have hs := circuits_spec source target hlen hcounts hprefix
  have hn := (List.nodup_flatten.mp (hs.2.nodup_iff.mpr (edges_nodup source target hlen))).1
    _ (List.getElem_mem group.isLt)
  apply (List.formPerm_apply_mem_ne_self_iff _ hn position hp).mp
  intro he
  have hv := Circuit.formPerm _ _ _ (hs.1 _ (List.getElem_mem group.isLt)) hn position hp
  rw [he] at hv
  exact hm hv.symm

omit hcounts hprefix in
theorem top_mem_edges_of_source (hne : 0 < source.length) (i : Fin source.length)
    (hi : i ∈ edges source target hlen)
    (he : source[i] = source[source.length - 1]) :
    (⟨source.length - 1, by omega⟩ : Fin source.length) ∈ edges source target hlen := by
  let top : Fin source.length := ⟨source.length - 1, by omega⟩
  by_cases ht : source[top] = target[top.val]'(by omega)
  · by_cases hm : source[i] = target[i.val]'(by omega)
    · have hitop := (correct_edge_is_top source target hlen i hi hm).1
      have hi' : i = top := Fin.ext hitop
      simpa only [hi'] using hi
    · have hmi : i ∈ mismatches source target hlen := by
        by_cases hreach : i.rev.val ≤ MAX_SWAP_DEPTH
        · exact List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true ⟨hreach, hm⟩⟩
        · have hr := edges_reachable source target hlen i hi
          exact False.elim (hreach hr)
      have ha : (mismatches source target hlen).any (fun i =>
          source[i] = source[top] ∨ target[i.val]'(by omega) = source[top]) :=
        List.any_eq_true.mpr ⟨i, hmi, decide_eq_true (Or.inl he)⟩
      dsimp only [top] at ht ha
      rw [edges, dite_eq_left hne, ite_eq_left ⟨ht, ha⟩]
      simp
  · apply mismatches_subset_edges source target hlen
    apply List.mem_filter.mpr
    exact ⟨List.mem_finRange top, decide_eq_true ⟨by dsimp [Fin.rev]; omega, ht⟩⟩

theorem circuits_top_label_iff (hne : 0 < source.length)
    (group : Fin (circuits source target hlen).length) :
    labels source (circuits source target hlen) source[source.length - 1] = some group ↔
      (⟨source.length - 1, by omega⟩ : Fin source.length) ∈ (circuits source target hlen)[group] := by
  constructor
  · intro hl
    have hw := List.find?_some hl
    obtain ⟨position, hp, he⟩ := List.any_eq_true.mp hw
    have he : source[position] = source[source.length - 1] := of_decide_eq_true he
    have hs := circuits_spec source target hlen hcounts hprefix
    have hpos := hs.2.mem_iff.mp (List.mem_flatten.mpr ⟨_, List.getElem_mem group.isLt, hp⟩)
    have ht := top_mem_edges_of_source source target hlen hne position hpos he
    obtain ⟨cycle, hc, ht⟩ := List.mem_flatten.mp (hs.2.mem_iff.mpr ht)
    obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    let other : Fin (circuits source target hlen).length := ⟨index, hi⟩
    have hother := circuits_label_of_mem source target hlen hcounts hprefix other _ ht
    have hg : other = group := Option.some.inj (hother.symm.trans hl)
    exact hg ▸ ht
  · exact circuits_label_of_mem source target hlen hcounts hprefix group _

theorem certificate_complete : (certificate source target hlen).isSome := by
  have hp : ∀ group : Fin (circuits source target hlen).length,
      (((circuits source target hlen)[group]).find? fun position =>
        source[position] ≠ target[position.val]'(by omega)).isSome := by
    intro group
    simpa only [List.find?_isSome, decide_eq_true_eq] using
      circuits_has_mismatch source target hlen hcounts hprefix group
  unfold certificate
  simp only [dite_eq_left hp]
  have hm : ∀ group : Fin (circuits source target hlen).length,
      source[((circuits source target hlen)[group].find? fun i =>
        source[i] ≠ target[i.val]'(by omega)).get (hp group)] ≠
      target[((circuits source target hlen)[group].find? fun i =>
        source[i] ≠ target[i.val]'(by omega)).get (hp group) |>.val]'(by omega) := by
    intro group
    have hh := List.find?_some (Option.some_get (hp group)).symm
    simpa only [decide_eq_true_eq] using hh
  simp only [dite_eq_left hm]
  have hr : ∀ group : Fin (circuits source target hlen).length,
      labels source (circuits source target hlen)
        source[((circuits source target hlen)[group].find? fun i =>
          source[i] ≠ target[i.val]'(by omega)).get (hp group)] = some group := by
    intro group
    exact circuits_label_of_mem source target hlen hcounts hprefix group _
      (List.mem_of_find?_eq_some (Option.some_get (hp group)).symm)
  simp only [dite_eq_left hr, dite_eq_left (circuits_position_label source target hlen hcounts hprefix),
    Option.isSome_some]

omit hcounts hprefix in
theorem certificate_bound (cert : LabelCertificate source target hlen)
    (hcert : certificate source target hlen = some cert) (hne : 0 < source.length) :
    cert.bound hne =
      ((mismatchPositions source target hlen).erase ⟨source.length - 1, by omega⟩).card +
        (Finset.univ.filter fun group : Fin (circuits source target hlen).length =>
          some group ≠ labels source (circuits source target hlen) source[source.length - 1]).card := by
  unfold certificate at hcert
  dsimp only at hcert
  split at hcert
  · split at hcert
    · split at hcert
      · split at hcert
        · rename_i hp hm hr hs
          cases hcert
          dsimp only [LabelCertificate.bound]
          congr 2
          apply Finset.filter_congr
          intro group _
          rw [hr group]
          simp only [Fin.getElem_fin]
        · contradiction
      · contradiction
    · contradiction
  · contradiction

end Feasible

end Shuffler.Optimality.ValueGraph
