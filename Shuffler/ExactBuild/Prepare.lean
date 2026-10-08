import Shuffler.ExactBuild.Steps

namespace Shuffler.ExactBuild

open Shuffler.Placement

structure PreparedProblem (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) where
  fixed : Stack
  working : Stack
  tail : Stack
  trace : Trace spills source (fixed ++ working)
  noPop : trace.noPop
  additions : trace.additions = 0
  target_eq : target = fixed ++ tail
  small : working.length ≤ MAX_SWAP_DEPTH + 1
  space : missing ≠ 0 → working.length ≤ MAX_DUP_DEPTH + 1
  balance : (tail : Multiset Value) = (working : Multiset Value) + missing
  seeds : Shuffler.Placement.seeds spills missing ≤ (working : Multiset Value)

private theorem noPop_cast_source (h : source = other)
    (trace : Trace spills source target) :
    (h ▸ trace).noPop ↔ trace.noPop := by cases h; rfl

private theorem additions_cast_source (h : source = other)
    (trace : Trace spills source target) :
    (h ▸ trace).additions = trace.additions := by cases h; rfl

-- Keep the initially frozen prefix. Before any required growth from a full
-- seventeen-slot window, place its reserved output and retain all seeds.
def prepare (spills : SpillSet) (source target : Stack) (missing : Multiset Value)
    (h : Reserve spills source target missing) :
    PreparedProblem spills source target missing := by
  let count := frozen source
  let fixed := source.take count
  let working := source.drop count
  let tail := target.drop count
  have hsource : fixed ++ working = source := List.take_append_drop _ _
  have htarget : target = fixed ++ tail := by
    calc
      target = target.take count ++ target.drop count := (List.take_append_drop _ _).symm
      _ = fixed ++ tail := by rw [h.2.1]
  have hsmall : working.length ≤ MAX_SWAP_DEPTH + 1 := by
    simp only [working, List.length_drop, count, frozen]
    omega
  have hbalance : (tail : Multiset Value) = (working : Multiset Value) + missing := by
    have hb := h.1
    rw [htarget, ← hsource] at hb
    simp only [← Multiset.coe_add, add_assoc] at hb
    exact add_left_cancel hb
  have hseeds : seeds spills missing ≤ (working : Multiset Value) :=
    (Multiset.le_add_left _ _).trans h.2.2
  let initialTrace : Trace spills source (fixed ++ working) := hsource.symm ▸ .Lit source
  let unchanged (hspace : missing ≠ 0 → working.length ≤ MAX_DUP_DEPTH + 1) :
      PreparedProblem spills source target missing := {
    fixed := fixed
    working := working
    tail := tail
    trace := initialTrace
    noPop := (Trace.noPop_cast _ _).mpr trivial
    additions := by rw [Trace.additions_cast]; rfl
    target_eq := htarget
    small := hsmall
    space := hspace
    balance := hbalance
    seeds := hseeds
  }
  if hzero : missing = 0 then
    exact unchanged (fun hne => False.elim (hne hzero))
  else if hspace : working.length ≤ MAX_DUP_DEPTH + 1 then
    exact unchanged (fun _ => hspace)
  else
    have hlarge : MAX_SWAP_DEPTH + 1 ≤ source.length := by
      have hw : working.length ≤ source.length := by
        simp only [working, List.length_drop]
        omega
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    have hcard := congrArg Multiset.card h.1
    simp only [Multiset.card_add, Multiset.coe_card] at hcard
    have hindex : count < target.length := by
      dsimp [count, frozen]
      unfold MAX_SWAP_DEPTH at hlarge ⊢
      omega
    let value := target[count]'hindex
    let rest := target.drop (count + 1)
    have hboundary : boundary source target missing = {value} := by
      simp [boundary, hzero, hlarge, count, value, List.getElem?_eq_getElem hindex]
    have hreserve : {value} + seeds spills missing ≤ (working : Multiset Value) := by
      simpa only [hboundary, working, count, window] using h.2.2
    have hvalue : value ∈ working := Multiset.mem_of_le hreserve (by simp)
    let step := placeExisting spills fixed working value hsmall hvalue
    have hstepBalance : {value} + (step.remaining : Multiset Value) =
        (working : Multiset Value) := by simpa only [add_zero] using step.balance
    have hstepCard := congrArg Multiset.card hstepBalance
    simp only [Multiset.card_add, Multiset.card_singleton, Multiset.coe_card] at hstepCard
    have hremaining : step.remaining.length ≤ MAX_DUP_DEPTH + 1 := by
      unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
      omega
    have htail : tail = value :: rest := List.drop_eq_getElem_cons hindex
    refine {
      fixed := fixed ++ [value]
      working := step.remaining
      tail := rest
      trace := hsource ▸ step.trace
      noPop := (noPop_cast_source _ _).mpr step.noPop
      additions := (additions_cast_source _ _).trans step.additions
      target_eq := ?_
      small := ?_
      space := fun _ => hremaining
      balance := ?_
      seeds := ?_
    }
    · rw [htarget, htail]
      simp only [List.append_assoc, List.singleton_append]
    · unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
      omega
    · rw [htail] at hbalance
      change {value} + (rest : Multiset Value) = (working : Multiset Value) + missing at hbalance
      rw [← hstepBalance, add_assoc] at hbalance
      exact add_left_cancel hbalance
    · rw [← hstepBalance] at hreserve
      exact (add_le_add_iff_left ({value} : Multiset Value)).mp hreserve

end Shuffler.ExactBuild
