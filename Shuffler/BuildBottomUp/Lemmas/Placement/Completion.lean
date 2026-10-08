import Shuffler.BuildBottomUp.Lemmas.Placement.Resources
import Shuffler.BuildBottomUp.Lemmas.Placement.Permute

namespace Shuffler.Placement

-- Once at most sixteen working slots remain, one seed per missing nonfree
-- value suffices. The fixed prefix stays in place throughout the construction.
theorem canPlace_complete (spills : SpillSet) (fixed working target : Stack)
    (missing : Multiset Value)
    (hsmall : working.length ≤ MAX_DUP_DEPTH + 1)
    (hbalance : (target : Multiset Value) = (working : Multiset Value) + missing)
    (hseeds : seeds spills missing ≤ (working : Multiset Value)) :
    CanPlace spills (fixed ++ working) (fixed ++ target) missing := by
  induction target generalizing fixed working missing with
  | nil =>
    have hc := congrArg Multiset.card hbalance
    simp only [Multiset.coe_nil, Multiset.card_zero, Multiset.card_add,
      Multiset.coe_card] at hc
    have hw : working = [] := List.length_eq_zero_iff.mp (by omega)
    have hm : missing = 0 := Multiset.card_eq_zero.mp (by omega)
    subst working missing
    exact CanPlace.refl spills _
  | cons value tail ih =>
    by_cases hv : value ∈ missing
    · have happend := CanPlace.append (available_of_suffix hseeds hsmall value hv (fixed := fixed))
      have hperm : (working ++ [value]).Perm (value :: working) := by
        exact List.perm_append_comm
      have hlen : (working ++ [value]).length ≤ MAX_SWAP_DEPTH + 1 := by
        simp only [List.length_append, List.length_singleton]
        unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
        omega
      have hplace := canPlace_perm_append spills hperm fixed hlen
      have hplace' : CanPlace spills ((fixed ++ working) ++ [value])
          ((fixed ++ [value]) ++ working) 0 := by
        simpa only [List.append_assoc, List.singleton_append] using hplace
      have hstep : CanPlace spills (fixed ++ working) ((fixed ++ [value]) ++ working) {value} := by
        simpa only [add_zero] using happend.trans hplace'
      have hnext := ih (fixed ++ [value]) working (missing.erase value) hsmall
        (balance_erase_missing hbalance hv)
        ((seeds_mono (Multiset.erase_le _ _)).trans hseeds)
      simpa only [List.append_assoc, List.singleton_append, Multiset.singleton_add,
        Multiset.cons_erase hv] using hstep.trans hnext
    · obtain ⟨hw, hbalance'⟩ := balance_erase_source hbalance hv
      have hperm := List.perm_cons_erase hw
      have hlen : working.length ≤ MAX_SWAP_DEPTH + 1 := by
        unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
        omega
      have hstep := canPlace_perm_append spills hperm fixed hlen
      have hsmall' : (working.erase value).length ≤ MAX_DUP_DEPTH + 1 :=
        (List.length_erase_le).trans hsmall
      have hnext := ih (fixed ++ [value]) (working.erase value) missing hsmall' hbalance'
        (seeds_erase_source hseeds hv)
      simpa only [List.append_assoc, List.singleton_append, zero_add] using
        hstep.trans (by simpa only [List.append_assoc, List.singleton_append] using hnext)

end Shuffler.Placement
