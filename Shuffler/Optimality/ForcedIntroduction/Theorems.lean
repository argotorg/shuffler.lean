import Shuffler.Optimality.ForcedIntroduction.Defs
import Shuffler.Optimality.ForcedIntroduction.FirstBirth

namespace Shuffler.Optimality.ForcedIntroduction

open Shuffler.Placement Lineage

private theorem window_append (stack : Stack) (value : Value) :
    window (stack ++ [value]) =
      stack.drop (stack.length - (MAX_DUP_DEPTH + 1)) ++ [value] := by
  have hc : frozen (stack ++ [value]) = stack.length - (MAX_DUP_DEPTH + 1) := by
    simp only [frozen, List.length_append, List.length_singleton]
    unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH
    omega
  simp [window, hc, List.drop_append]

theorem reserve_singleton_of_no_direct (value : Value)
    (trace : Trace spills source target) (hpop : trace.noPop)
    (hadded : value ∈ trace.additions) (hno : directCount value trace = 0) :
    boundary source target trace.additions + {value} ≤ (window source : Multiset Value) := by
  by_cases hg : trace.additions ≠ 0 ∧ MAX_SWAP_DEPTH + 1 ≤ source.length
  · obtain ⟨middle, first, before, tail, hb, hz, hv, htail, hn, he⟩ :=
      firstBirth value trace hpop hg.1 hno
    have hlen : middle.length = source.length := by
      simpa [hz] using before.noPop_length hb
    have hfixed := before.noPop_frozen hb
    have hbalance : (middle : Multiset Value) = (source : Multiset Value) := by
      simpa [hz] using before.noPop_balance hb
    have hi : frozen source < middle.length := by
      unfold frozen MAX_SWAP_DEPTH at *
      omega
    have hcut : frozen (middle ++ [first]) = frozen source + 1 := by
      simp only [frozen, List.length_append, List.length_singleton, hlen]
      unfold MAX_SWAP_DEPTH at *
      omega
    have hcutdup : middle.length - (MAX_DUP_DEPTH + 1) = frozen source + 1 := by
      unfold frozen MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    have htarget : target[frozen source]? = some middle[frozen source] := by
      have hp := tail.noPop_frozen htail
      rw [hcut, List.take_append_of_le_length (by omega)] at hp
      have hx := congrArg (fun stack : Stack => stack[frozen source]?) hp
      simpa [List.getElem?_eq_getElem hi] using hx
    have hfirst : first = value → value ∈ middle.drop (frozen source + 1) := by
      simpa [hcutdup] using hv
    have hseed : value ∈ middle.drop (frozen source + 1) := by
      rw [he] at hadded
      rcases Multiset.mem_add.mp hadded with ho | ho
      · exact hfirst (Multiset.mem_singleton.mp ho).symm
      · have hm := addition_mem_window_of_no_direct value tail htail hn ho
        rw [window_append, hcutdup] at hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hm
        · exact hfirst (by simpa [eq_comm] using hm)
    have hwindow : (middle.drop (frozen source) : Multiset Value) =
        (window source : Multiset Value) := by
      apply add_left_cancel (a := (source.take (frozen source) : Multiset Value))
      calc
        (source.take (frozen source) : Multiset Value) + middle.drop (frozen source) =
            (middle : Multiset Value) := by rw [← hfixed, Multiset.coe_add, List.take_append_drop]
        _ = (source : Multiset Value) := hbalance
        _ = (source.take (frozen source) : Multiset Value) + window source := by
          rw [Multiset.coe_add, window, List.take_append_drop]
    have hr : {middle[frozen source]} + {value} ≤
        (middle.drop (frozen source) : Multiset Value) := by
      rw [List.drop_eq_getElem_cons hi]
      change middle[frozen source] ::ₘ {value} ≤
        middle[frozen source] ::ₘ (middle.drop (frozen source + 1) : Multiset Value)
      exact Multiset.cons_le_cons _ (Multiset.singleton_le.mpr hseed)
    rw [hwindow] at hr
    simpa [boundary, hg, htarget] using hr
  · simpa only [boundary, ite_eq_right hg, zero_add] using
      Multiset.singleton_le.mpr (addition_mem_window_of_no_direct value trace hpop hno hadded)

theorem Required.directCount_pos (value : Value)
    (trace : Trace spills source target) (hpop : trace.noPop)
    (hrequired : Required value source target trace.additions) :
    0 < directCount value trace := by
  by_contra hn
  have hz : directCount value trace = 0 := by omega
  exact hrequired.2 (reserve_singleton_of_no_direct value trace hpop hrequired.1 hz)

end Shuffler.Optimality.ForcedIntroduction
