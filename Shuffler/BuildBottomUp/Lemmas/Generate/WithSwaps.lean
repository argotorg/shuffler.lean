import Shuffler.BuildBottomUp.Lemmas.Placement.Necessity
import Shuffler.BuildBottomUp.Lemmas.Placement.Sufficiency

namespace Shuffler.Generate.WithSwaps

open Shuffler.Placement

theorem CanGenerate.ready (h : CanGenerate spills source missing) :
    Ready spills source missing := by
  obtain ⟨target, hplan⟩ := h
  have hreserve := hplan.reserve
  have hseeds : seeds spills missing ≤ (window source : Multiset Value) := by
    obtain ⟨trace, hnoPop, rfl⟩ := hplan
    exact seeds_le_window trace hnoPop
  refine ⟨hseeds, ?_⟩
  by_cases hz : missing = 0
  · simp [hz, seeds]
  by_cases hsmall : source.length ≤ MAX_DUP_DEPTH + 1
  · have hc := Multiset.card_le_card hseeds
    simp only [Multiset.coe_card, window, List.length_drop] at hc
    omega
  · have hlarge : MAX_SWAP_DEPTH + 1 ≤ source.length := by
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    obtain ⟨_, working, _, _, _, hlength, _, hworking⟩ := hreserve.prepare hz hlarge
    have hc : (seeds spills missing).card ≤ working.length := by
      simpa only [Multiset.coe_card] using Multiset.card_le_card hworking
    exact hc.trans hlength

theorem Ready.canGenerate (h : Ready spills source missing) :
    CanGenerate spills source missing := by
  by_cases hz : missing = 0
  · subst missing
    exact ⟨source, CanPlace.refl spills source⟩
  by_cases hsmall : source.length ≤ MAX_DUP_DEPTH + 1
  · have hf : frozen source = 0 := by
      unfold frozen MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    have hlarge : ¬MAX_SWAP_DEPTH + 1 ≤ source.length := by
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    refine ⟨source ++ missing.toList, Reserve.canPlace ?_⟩
    refine ⟨?_, by simp [hf], ?_⟩
    · simp only [← Multiset.coe_add, Multiset.coe_toList]
    · simpa [boundary, hlarge, hf, window] using h.1
  · have hlarge : MAX_SWAP_DEPTH + 1 ≤ source.length := by
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    have hwindow : (window source).length = MAX_SWAP_DEPTH + 1 := by
      simp only [window, List.length_drop, frozen]
      omega
    have hne : seeds spills missing ≠ (window source : Multiset Value) := by
      intro he
      have hc := congrArg Multiset.card he
      simp only [Multiset.coe_card, hwindow] at hc
      have := h.2
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    obtain ⟨value, hreserve⟩ := Multiset.lt_iff_cons_le.mp (lt_of_le_of_ne h.1 hne)
    have hvalue : value ∈ window source :=
      Multiset.mem_of_le hreserve (by simp)
    let fixed := source.take (frozen source)
    let working := (window source).erase value
    let target := fixed ++ value :: (working ++ missing.toList)
    have hfixed : fixed.length = frozen source := by
      simp only [fixed, List.length_take]
      exact Nat.min_eq_left (by unfold frozen; omega)
    have hperm : (window source).Perm (value :: working) := List.perm_cons_erase hvalue
    have hsource : fixed ++ window source = source := List.take_append_drop _ _
    have hsourceValues : (source : Multiset Value) =
        (fixed : Multiset Value) + ((value :: working : Stack) : Multiset Value) := by
      rw [← hsource, ← Multiset.coe_add, Multiset.coe_eq_coe.mpr hperm]
    have hbalance : (target : Multiset Value) = (source : Multiset Value) + missing := by
      simp only [target, ← List.cons_append, ← List.append_assoc, ← Multiset.coe_add,
        Multiset.coe_toList, hsourceValues, add_assoc]
    have hprefix : target.take (frozen source) = source.take (frozen source) := by
      change (fixed ++ value :: (working ++ missing.toList)).take (frozen source) = fixed
      rw [← hfixed, List.take_left]
    have hboundary : boundary source target missing = {value} := by
      rw [boundary, ite_eq_left ⟨hz, hlarge⟩]
      change (((fixed ++ value :: (working ++ missing.toList))[frozen source]?).toList :
        Multiset Value) = {value}
      rw [← hfixed]
      simp
    refine ⟨target, Reserve.canPlace ⟨hbalance, hprefix, ?_⟩⟩
    simpa only [hboundary, Multiset.singleton_add] using hreserve

end Shuffler.Generate.WithSwaps
