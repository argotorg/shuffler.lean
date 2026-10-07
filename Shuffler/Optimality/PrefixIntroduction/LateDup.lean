import Shuffler.Optimality.PrefixIntroduction.Defs
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.PrefixIntroduction

open Shuffler.Placement

def LateDup (cut : Nat) (value : Value) : Trace spills source target → Prop
  | .Lit _ => True
  | .Swap _ _ _ _ trace => LateDup cut value trace
  | @Trace.Dup _ _ previous depth _ _ _ trace =>
      LateDup cut value trace ∧
        (previous[previous.length - depth]'(by omega) = value → cut + 17 ≤ previous.length)
  | .Pop _ trace => LateDup cut value trace
  | .Push _ _ trace => LateDup cut value trace
  | .Load _ _ trace => LateDup cut value trace

theorem oldCount_source (source : Stack) : oldCount source source = source.length := by
  apply List.countP_eq_length.mpr
  intro value hv
  exact decide_eq_true hv

theorem oldCount_mono (original : Stack) (trace : Trace spills source target) (h : trace.noPop) :
    oldCount original source ≤ oldCount original target := by
  induction trace with
  | Lit => exact Nat.le_refl _
  | Swap depth hlen hlo hhi trace ih =>
      unfold oldCount
      rw [List.Perm.countP_eq _ (List.swap_perm _ _ _)]
      exact ih h
  | Pop _ _ => exact False.elim h
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      have hh := ih h
      unfold oldCount at hh ⊢
      rw [List.countP_append]
      omega

private theorem oldCount_take_mono (source stack : Stack) (h : first ≤ second) :
    oldCount source (stack.take first) ≤ oldCount source (stack.take second) :=
  (List.take_sublist_take_left h).countP_le

private theorem no_early_dup (old : Stack) (value : Value) (before : Trace spills source previous)
    (hbefore : before.noPop) (hlarge : 16 ≤ oldCount old source) (habsent : value ∉ old)
    (depth : Nat) (hlen : depth ≤ previous.length) (hlo : 1 ≤ depth) (hhi : depth ≤ MAX_DUP_DEPTH + 1)
    (he : previous[previous.length - depth]'(by omega) = value)
    (tail : Trace spills (previous ++ [value]) target) (htail : tail.noPop)
    (hbound : oldCount old (target.take cut) ≤ oldCount old source - 16) :
    cut + 17 ≤ previous.length := by
  by_contra hn
  have hlenBefore := before.noPop_length_le hbefore
  have hsourceLength : oldCount old source ≤ source.length := List.countP_le_length
  have hcut : previous.length - 16 ≤ cut := by omega
  have hfrozen : frozen (previous ++ [value]) = previous.length - 16 := by
    simp only [frozen, List.length_append, List.length_singleton]
    unfold MAX_SWAP_DEPTH
    omega
  have hfixed := tail.noPop_frozen htail
  rw [hfrozen, List.take_append_of_le_length (by omega)] at hfixed
  have hp : oldCount old (previous.take (previous.length - 16)) ≤ oldCount old source - 16 := by
    rw [← hfixed]
    exact (oldCount_take_mono old target hcut).trans hbound
  have hmem : value ∈ previous.drop (previous.length - 16) := by
    rw [← he]
    exact getElem_mem_drop_of_le previous ⟨previous.length - depth, by omega⟩
      (previous.length - 16) (by dsimp; unfold MAX_DUP_DEPTH at hhi; omega)
  have hs : oldCount old (previous.drop (previous.length - 16)) < 16 := by
    have h := (List.countP_lt_length_iff (p := fun item => decide (item ∈ old))).mpr
      ⟨value, hmem, decide_eq_false habsent⟩
    have hlength : (previous.drop (previous.length - 16)).length = 16 := by
      simp only [List.length_drop]
      omega
    simpa only [hlength, oldCount] using h
  have ht := oldCount_mono old before hbefore
  have hsum : oldCount old (previous.take (previous.length - 16)) +
      oldCount old (previous.drop (previous.length - 16)) = oldCount old previous := by
    unfold oldCount
    rw [← List.countP_append, List.take_append_drop]
  omega

private theorem noPop_cast_source (he : source = other) (trace : Trace spills source target) :
    (he ▸ trace).noPop ↔ trace.noPop := by cases he; rfl

theorem lateDup_of_prefix_bound (old : Stack) (value : Value) (trace : Trace spills source current)
    (h : trace.noPop) (hlarge : 16 ≤ oldCount old source) (habsent : value ∉ old) :
    ∀ (tail : Trace spills current target), tail.noPop →
      oldCount old (target.take cut) ≤ oldCount old source - 16 → LateDup cut value trace := by
  induction trace with
  | Lit => intro _ _ _; trivial
  | Pop _ _ => exact False.elim h
  | @Swap previous depth hlen hlo hhi trace ih =>
      intro tail ht hb
      let step := Trace.Swap depth hlen hlo hhi (.Lit (spills := spills) previous)
      exact ih h (step.concat tail) (step.noPop_concat tail (by trivial) ht) hb
  | @Dup previous depth hlen hlo hhi trace ih =>
      intro tail ht hb
      let step := Trace.Dup depth hlen hlo hhi (.Lit (spills := spills) previous)
      refine ⟨ih h (step.concat tail) (step.noPop_concat tail (by trivial) ht) hb, ?_⟩
      intro he
      have heStack : previous ++ [previous[previous.length - depth]'(by omega)] =
          previous ++ [value] := by rw [he]
      let tail' : Trace spills (previous ++ [value]) target := heStack ▸ tail
      have htail' : tail'.noPop := (noPop_cast_source heStack tail).mpr ht
      exact no_early_dup old value trace h hlarge habsent depth hlen hlo hhi he tail' htail' hb
  | @Push previous added hfree trace ih =>
      intro tail ht hb
      let step := Trace.Push added hfree (.Lit (spills := spills) previous)
      exact ih h (step.concat tail) (step.noPop_concat tail (by trivial) ht) hb
  | @Load previous id hspill trace ih =>
      intro tail ht hb
      let step := Trace.Load id hspill (.Lit (spills := spills) previous)
      exact ih h (step.concat tail) (step.noPop_concat tail (by trivial) ht) hb

end Shuffler.Optimality.PrefixIntroduction
