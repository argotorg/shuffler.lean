import Shuffler.Optimality.Collective.HeightCut

namespace Shuffler.Optimality.Collective

def TracePrefix.packed (cut : TracePrefix spills source target) :
    (current : Stack) × Trace spills source current := ⟨cut.current, cut.before⟩

def TracePrefix.takePacked (height : Nat) (cut : TracePrefix spills source target) :
    (current : Stack) × Trace spills source current := (takeHeight height cut.before).packed

theorem takeHeight_nested (trace : Trace spills source target) (horder : low ≤ high) :
    (takeHeight high trace).takePacked low = (takeHeight low trace).packed := by
  induction trace with
  | Lit => rfl
  | @Swap previous depth hlen hlo hhi trace ih =>
      by_cases hh : previous.length ≤ high
      · rw [takeHeight_whole _ (by simpa only [List.length_swap] using hh)]
        rfl
      · have hl : ¬previous.length ≤ low := by omega
        simp only [takeHeight, dite_eq_right hh, dite_eq_right hl]
        exact ih
  | @Dup previous depth hlen hlo hhi trace ih =>
      by_cases hh : previous.length + 1 ≤ high
      · rw [takeHeight_whole _ (by simpa only [List.length_append, List.length_singleton] using hh)]
        rfl
      · have hl : ¬previous.length + 1 ≤ low := by omega
        simp only [takeHeight, dite_eq_right hh, dite_eq_right hl]
        exact ih
  | @Pop previous hlen trace ih =>
      by_cases hh : previous.dropLast.length ≤ high
      · rw [takeHeight_whole _ hh]
        rfl
      · have hl : ¬previous.dropLast.length ≤ low := by omega
        simp only [takeHeight, dite_eq_right hh, dite_eq_right hl]
        exact ih
  | @Push previous value hfree trace ih =>
      by_cases hh : previous.length + 1 ≤ high
      · rw [takeHeight_whole _ (by simpa only [List.length_append, List.length_singleton] using hh)]
        rfl
      · have hl : ¬previous.length + 1 ≤ low := by omega
        simp only [takeHeight, dite_eq_right hh, dite_eq_right hl]
        exact ih
  | @Load previous id hspill trace ih =>
      by_cases hh : previous.length + 1 ≤ high
      · rw [takeHeight_whole _ (by simpa only [List.length_append, List.length_singleton] using hh)]
        rfl
      · have hl : ¬previous.length + 1 ≤ low := by omega
        simp only [takeHeight, dite_eq_right hh, dite_eq_right hl]
        exact ih

theorem takeHeight_count_mono (trace : Trace spills source target) (hpop : trace.noPop)
    (horder : low ≤ high) (value : Value) :
    (takeHeight low trace).current.count value ≤
      (takeHeight high trace).current.count value := by
  have hcut := congrArg Sigma.fst (takeHeight_nested trace horder)
  change (takeHeight low (takeHeight high trace).before).current =
    (takeHeight low trace).current at hcut
  have hp := (takeHeight_noPop (height := high) trace hpop).1
  have hs := (takeHeight_noPop (height := low) (takeHeight high trace).before hp).2
  have hb := (takeHeight low (takeHeight high trace).before).after.noPop_balance hs
  have hc := congrArg (Multiset.count value) hb
  simp only [Multiset.count_add, Multiset.coe_count] at hc
  have hm : (takeHeight low (takeHeight high trace).before).current.count value ≤
      (takeHeight high trace).current.count value := by omega
  simpa only [hcut] using hm

theorem residual_count_mono (trace : Trace spills source target) (hpop : trace.noPop)
    (horder : low ≤ high) (value : Value)
    (hfixed : (target.take low).count value = (target.take high).count value) :
    (residual low trace).count value ≤ (residual high trace).count value := by
  have hc := takeHeight_count_mono trace hpop (Nat.add_le_add_right horder 16) value
  have hlo := congrArg (List.count value)
    (List.take_append_drop low (takeHeight (low + 16) trace).current)
  have hhi := congrArg (List.count value)
    (List.take_append_drop high (takeHeight (high + 16) trace).current)
  simp only [List.count_append, takeHeight_take trace hpop] at hlo hhi
  unfold residual
  omega

theorem residual_mem_of_mem (trace : Trace spills source target) (hpop : trace.noPop)
    (horder : low ≤ high) (value : Value)
    (hfixed : (target.take low).count value = (target.take high).count value)
    (hmem : value ∈ residual low trace) : value ∈ residual high trace := by
  have hc := residual_count_mono trace hpop horder value hfixed
  have hp : 0 < (residual low trace).count value := List.count_pos_iff.mpr hmem
  exact List.count_pos_iff.mp (by omega)

end Shuffler.Optimality.Collective
