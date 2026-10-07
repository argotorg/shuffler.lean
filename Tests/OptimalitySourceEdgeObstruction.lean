import Shuffler

namespace Tests.OptimalitySourceEdgeObstruction

open Shuffler Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Equiv.Perm (Fin 7) := List.formPerm [0, 6, 2, 1, 5, 3]
private def d : Equiv.Perm (Fin 7) := List.formPerm [1, 6, 3]
private def b : Equiv.Perm (Fin 7) := List.formPerm [1, 5, 3]
private def c : Equiv.Perm (Fin 7) := List.formPerm [0, 6, 3]
private def e : Equiv.Perm (Fin 7) := List.formPerm [1, 6, 2]

#guard List.ofFn (fun i => (a i).val) = [6, 5, 1, 0, 4, 3, 2]
#guard List.ofFn (fun i => (d i).val) = [0, 6, 2, 1, 4, 5, 3]

private def value : Value := .Var ⟨42⟩
private def source : Stack := List.replicate 5 value
private theorem edges (index : Fin 7) :
    ([a index, d index, index] : Multiset (Fin 7)) =
      ([b index, c index, e index] : Multiset (Fin 7)) := by
  fin_cases index <;> decide

private theorem cost_balance (weights : Fin 7 → Fin 7 → ℚ) :
    (∑ i, weights i (a i)) + (∑ i, weights i (d i)) + (∑ i, weights i i) =
    (∑ i, weights i (b i)) + (∑ i, weights i (c i)) + (∑ i, weights i (e i)) := by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  have he := congrArg (fun xs : Multiset (Fin 7) => (xs.map (weights index)).sum) (edges index)
  simpa [add_assoc] using he

private def target : Stack := List.replicate 7 value
private def missing : Multiset Value := ([value, value] : Stack)
private def wb := (replayExact ∅ source target missing [.dup 1, .swap 2, .swap 4, .dup 1]).get (by decide)
private def wc := (replayExact ∅ source target missing [.dup 1, .dup 1, .swap 3, .swap 6]).get (by decide)
private def we := (replayExact ∅ source target missing [.dup 1, .dup 1, .swap 4, .swap 5]).get (by decide)

private theorem assignment_b : traceAssignment wb.trace wb.noPop = b := by
  apply Equiv.ext
  intro index
  fin_cases index <;> decide +kernel
private theorem assignment_c : traceAssignment wc.trace wc.noPop = c := by
  apply Equiv.ext
  intro index
  fin_cases index <;> decide +kernel
private theorem assignment_e : traceAssignment we.trace we.noPop = e := by
  apply Equiv.ext
  intro index
  fin_cases index <;> decide +kernel
private theorem swaps_b : wb.trace.swapCount = 2 := by decide
private theorem swaps_c : wc.trace.swapCount = 2 := by decide
private theorem swaps_e : we.trace.swapCount = 2 := by decide
private theorem potential_a : sourcePotential a 5 (by decide) = 9 := by decide +kernel
private theorem potential_d : sourcePotential d 5 (by decide) = 4 := by decide +kernel
private theorem potential_id : sourcePotential (1 : Equiv.Perm (Fin 7)) 5 (by decide) = 0 := by decide +kernel

private theorem target_value (index : Nat) (hi : index < target.length) : target[index] = value := by
  simp only [target, List.getElem_replicate]

private def plan (f : Equiv.Perm (Fin 7)) : SourcePlan ∅ source target where
  source_length := by decide
  assignment := f
  source_values := by
    simp only [prefixValues, birthWord, Fin.getElem_fin, target_value, List.ofFn_const]
    rfl
  deadlines := by
    intro index
    have hi := index.isLt
    change index.val < 7 at hi
    change index.val ≤ (f index).val + 16
    omega
  source_frozen := by
    intro index h
    change index.val + 17 < 5 at h
    omega
  method := fun _ => .dup
  available := by
    intro index
    simp only [BirthAvailable, birthWord, Fin.getElem_fin, target_value, List.ofFn_const]
    fin_cases index <;> decide

-- All assignments are valid source plans for this one equal-value instance.
theorem no_edge_additive_sandwich (weights : Fin 7 → Fin 7 → ℚ)
    (lower : ∀ p : SourcePlan ∅ source target,
      (sourcePotential p.assignment source.length p.source_length : ℚ) ≤
        ∑ i, weights i (p.assignment i))
    (upper : ∀ trace : Trace ∅ source target, ∀ hpop : trace.noPop,
      (∑ i, weights i (traceAssignment trace hpop i)) ≤ 2 * (trace.swapCount : ℚ)) : False := by
  have ha : (sourcePotential a 5 (by decide) : ℚ) ≤ ∑ i, weights i (a i) := lower (plan a)
  have hd : (sourcePotential d 5 (by decide) : ℚ) ≤ ∑ i, weights i (d i) := lower (plan d)
  have hi : (sourcePotential (1 : Equiv.Perm (Fin 7)) 5 (by decide) : ℚ) ≤
      ∑ i, weights i ((1 : Equiv.Perm (Fin 7)) i) := lower (plan 1)
  rw [potential_a] at ha
  rw [potential_d] at hd
  rw [potential_id] at hi
  have hb := upper wb.trace wb.noPop
  have hc := upper wc.trace wc.noPop
  have he := upper we.trace we.noPop
  rw [assignment_b, swaps_b] at hb
  rw [assignment_c, swaps_c] at hc
  rw [assignment_e, swaps_e] at he
  have hlo := add_le_add (add_le_add ha hd) hi
  simp only [Equiv.Perm.one_apply] at hlo
  rw [cost_balance weights] at hlo
  have hbad := hlo.trans (add_le_add (add_le_add hb hc) he)
  exact (by decide +kernel : ¬((9 : ℚ) + 4 + 0 ≤ 2 * 2 + 2 * 2 + 2 * 2)) hbad

-- The future rows can change the required bound while all old rows stay fixed.
private def t : Equiv.Perm (Fin 7) := List.formPerm [0, 6, 3] * List.formPerm [1, 5, 2]
private def wt := (replayExact ∅ source target missing
  [.dup 1, .swap 3, .swap 4, .dup 1, .swap 3, .swap 6]).get (by decide)

private theorem assignment_t : traceAssignment wt.trace wt.noPop = t := by
  apply Equiv.ext
  intro index
  fin_cases index <;> decide +kernel
private theorem swaps_t : wt.trace.swapCount = 4 := by decide
private theorem support_a : a.support.card = 6 := by decide +kernel
private theorem support_t : t.support.card = 6 := by decide +kernel
private theorem potential_t : sourcePotential t 5 (by decide) = 8 := by decide +kernel

private def oldRows (f : Equiv.Perm (Fin 7)) : List Nat :=
  List.ofFn fun index : Fin 5 => (f ⟨index.val, by have := index.isLt; omega⟩).val

private theorem same_oldRows : oldRows a = oldRows t := by decide +kernel

theorem no_old_rows_surrogate (score : Nat → List Nat → ℚ)
    (lower : ∀ p : SourcePlan ∅ source target,
      (sourcePotential p.assignment source.length p.source_length : ℚ) ≤
        score p.assignment.support.card (oldRows p.assignment))
    (upper : ∀ trace : Trace ∅ source target, ∀ hpop : trace.noPop,
      score (traceAssignment trace hpop).support.card (oldRows (traceAssignment trace hpop)) ≤
        2 * (trace.swapCount : ℚ)) : False := by
  have ha : (sourcePotential a 5 (by decide) : ℚ) ≤ score a.support.card (oldRows a) := lower (plan a)
  have ht := upper wt.trace wt.noPop
  rw [potential_a, support_a, same_oldRows] at ha
  rw [assignment_t] at ht
  change score t.support.card (oldRows t) ≤ 2 * (wt.trace.swapCount : ℚ) at ht
  rw [support_t, swaps_t] at ht
  exact (by decide +kernel : ¬((9 : ℚ) ≤ 2 * 4)) (ha.trans ht)

/-- info: 'Tests.OptimalitySourceEdgeObstruction.no_edge_additive_sandwich' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_edge_additive_sandwich

/-- info: 'Tests.OptimalitySourceEdgeObstruction.no_old_rows_surrogate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_old_rows_surrogate

end Tests.OptimalitySourceEdgeObstruction
