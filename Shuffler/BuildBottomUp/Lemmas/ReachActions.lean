import Shuffler.BuildBottomUp.Lemmas.Reachability

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

def NoBlocked (result : Except Error α) : Prop :=
  match result with
  | .error (.blocked _) => False
  | _ => True

def noBlockedErrors : EPost⟨Error → Prop⟩ :=
  epost⟨fun | .blocked _ => False | .assertion _ => True⟩

def Succeeds (result : Except Error α) (post : α → Prop) : Prop :=
  ∃ value, result = .ok value ∧ post value

theorem Succeeds.of_triple (result : Except Error α) (post : α → Prop)
    (h : ⦃True⦄ result ⦃post⦄) : Succeeds result post := by
  have hp := h.le_wp trivial
  cases result with
  | ok value => exact ⟨value, rfl, hp⟩
  | error err => simp [wp, WP.wpTrans, EPost.Cons.head_bot] at hp

-- A triple under `noBlockedErrors` excludes blocked errors.
theorem noBlocked_of_triple {result : Except Error α}
    (h : ⦃True⦄ result ⦃fun _ => True; noBlockedErrors⦄) : NoBlocked result := by
  have hp := h.le_wp trivial
  cases result with
  | ok value => trivial
  | error err => cases err with
    | blocked excess => exact False.elim hp
    | assertion reason => trivial

theorem Spec.success {result : Except Error α} {post : α → Prop}
    (h : Spec result post) (hn : NoBlocked result) : Succeeds result post := by
  cases result with
  | ok value => exact ⟨value, rfl, h⟩
  | error err => cases err <;> contradiction

theorem Succeeds.bind {result : Except Error α} {pre : α → Prop} {next : α → Except Error β}
    {post : β → Prop} (h : Succeeds result pre)
    (step : ∀ value, pre value → Succeeds (next value) post) :
    Succeeds (result >>= next) post := by
  obtain ⟨value, rfl, hv⟩ := h
  exact step value hv

theorem Succeeds.mono {result : Except Error α} {pre post : α → Prop}
    (h : Succeeds result pre) (step : ∀ value, pre value → post value) : Succeeds result post := by
  obtain ⟨value, heq, hv⟩ := h
  exact ⟨value, heq, step value hv⟩

theorem State.reachable.filtered {state : State source target spills} (h : state.reachable)
    (dest : Fin target.length) (hdest : state.mapping.symm dest = none)
    (hgen : ¬(target[dest].can_be_freely_generated ∨ spills.is_spilled target[dest])) :
    ∃ copy, (state.stack.shallowestCopyPosition target[dest]).filter
      (fun pos => state.stack.isDupReachable pos) = some copy := by
  have hc : Stack.hasCopy state.stack target[dest] := by
    rcases h dest hdest with hfree | hspill | hcopy
    · exact (hgen (Or.inl hfree)).elim
    · exact (hgen (Or.inr hspill)).elim
    · exact hcopy
  obtain ⟨copy, heq, hreach⟩ := hc.shallowest
  exact ⟨copy, by simpa [hreach] using heq⟩

theorem generate_noBlocked (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (h : state.reachable) :
    NoBlocked (state.generate dest.val) := by
  have hfilter := h.filtered dest
  apply noBlocked_of_triple
  vcgen [State.generate, State.produce, State.push, State.dup, State.swapDestinations,
    State.swapWith, requires, index, slotAt, State.isSwapReachable, State.depthOf]
  all_goals simp_all [noBlockedErrors]

theorem generate_success (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest)
    (h : state.reachable) :
    Succeeds (state.generate dest.val) (fun next => Generation state next dest) :=
  (generate_contract state dest hbound havailable).success (generate_noBlocked state dest hbound h)

theorem Growth.final_swapped {state produced next : State source target spills}
    {dest : Fin target.length} (h : Growth state produced dest pending)
    {pos : Fin produced.stack.length} (hpos : pos.val = dest.val) (hs : Swapped produced next pos) :
    ∃ h, next.isFinal ⟨dest, h⟩ :=
  hs.final dest hpos (by simpa [h.size] using h.bound)

theorem Growth.final_at_exit {state produced : State source target spills}
    {dest : Fin target.length} (h : Growth state produced dest pending)
    (hle : dest.val ≤ state.stack.length)
    (hexit : dest.val + 1 < produced.stack.length → ∃ h, produced.isFinal ⟨dest, h⟩) :
    ∃ h, produced.isFinal ⟨dest, h⟩ := by
  by_cases hlt : dest.val + 1 < produced.stack.length
  · exact hexit hlt
  · apply (produced.isFinal_of_bound_val_iff dest _ h.bound).mpr
    have := h.size
    omega

theorem Growth.swap_reachable {state produced : State source target spills}
    {dest : Fin target.length} (h : Growth state produced dest pending)
    (hreach : state.stack.length - dest.val ≤ MAX_SWAP_DEPTH)
    (pos : Fin produced.stack.length) (hpos : pos.val = dest.val) :
    produced.stack.isSwapReachable pos := by
  rw [Stack.isSwapReachable_iff_length]
  have := h.size
  have := pos.isLt
  omega

theorem generate_final (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest)
    (hle : dest.val ≤ state.stack.length)
    (hreach : state.stack.length - dest.val ≤ MAX_SWAP_DEPTH) :
    Spec (state.generate dest.val) (fun next => ∃ h, next.isFinal ⟨dest, h⟩) := by
  apply (spec_iff_triple _ _).mpr
  vcgen [State.generate]
  all_goals try simp only [Fin.val_inj] at *
  all_goals subst_vars
  all_goals try assumption
  all_goals try simp_all
  all_goals first
    | exact Growth.final_swapped (by assumption) rfl (by assumption)
    | exact Growth.final_swapped (by assumption) rfl (Swapped.retag _ _ (by assumption))
    | exact Growth.final_at_exit (by assumption) hle (fun hlt => absurd hlt (by omega))
    | exact Growth.swap_reachable (by assumption) (by omega) _ rfl
    | exact State.not_isFinal_of_val_eq (by assumption) (by assumption)
    | exact State.isFinal_of_val_eq (by assumption) (by assumption)
    | omega
    | (have := (‹Growth _ _ _ _›).size
       simp only [State.isSwapReachable, State.depthOf, Stack.offsetToDepth] at *; omega)

theorem generate_reachable (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest)
    (hr : state.withinReach cursor) (hcursor : cursor ≤ dest.val) (hready : Ready state dest) :
    Succeeds (state.generate dest.val) (fun next =>
      Generation state next dest ∧ next.reachable ∧
      (dest.val ≤ state.stack.length → ∃ h, next.isFinal ⟨dest, h⟩)) := by
  obtain ⟨next, heq, hg⟩ := generate_success state dest hbound havailable hr.copies
  have hf (hle : dest.val ≤ state.stack.length) : ∃ h, next.isFinal ⟨dest, h⟩ := by
    have hreach : state.stack.length - dest.val ≤ MAX_SWAP_DEPTH := by have := hr.width; omega
    have hs := generate_final state dest hbound havailable hle hreach
    simpa [heq, Spec] using hs
  exact ⟨next, heq, hg, hg.reachable hr hcursor hready hbound hf, hf⟩

theorem swap_noBlocked (state : State source target spills) (offset : ℕ) :
    NoBlocked (state.swapWith offset) := by
  apply noBlocked_of_triple
  vcgen [State.swapWith, index, requires]
  all_goals simp_all [noBlockedErrors]

theorem swap_success (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hnfinal : ¬ state.isFinal pos) :
    Succeeds (state.swapWith pos.val) (fun next => Swapped state next pos) :=
  (swap_spec state pos hbelow hreach hnfinal).success (swap_noBlocked state pos.val)

theorem Placement.swap_final_success {state : State source target spills} {dest : Fin target.length}
    (h : Placement dest state) (hr : state.withinReach dest.val)
    (hbelow : dest.val + 1 < state.stack.length) (hnfinal : ¬ ∃ h, state.isFinal ⟨dest, h⟩) :
    Succeeds (state.swapWith dest.val) (fun next =>
      next.invariant (dest.val + 1) ∧ next.withinReach (dest.val + 1)) := by
  let pos : Fin state.stack.length := ⟨dest.val, h.in_bounds⟩
  apply (swap_success state pos hbelow (hr.swap_reachable pos le_rfl) (fun hf => hnfinal ⟨_, hf⟩)).mono
  intro next hs
  exact ⟨(hs.invariant h.toInvariant le_rfl).advance
    (hs.final dest rfl (h.position.resolve_left hnfinal)), (hr.swap pos le_rfl hs).advance⟩

theorem State.invariant.swap_bound_success {state : State source target spills} {dest : Fin target.length}
    (h : state.invariant dest.val) (hr : state.withinReach dest.val)
    (pos : Fin state.stack.length) (hbound : state.mapping.symm dest = some pos)
    (hbelow : pos.val + 1 < state.stack.length) (hne : pos.val ≠ dest.val) :
    Succeeds (state.swapWith pos.val) (fun next =>
      (Placement dest next ∧ ¬ ∃ h, next.isFinal ⟨dest, h⟩) ∧ next.withinReach dest.val) := by
  have hge := h.processed.bound_ge dest pos hbound le_rfl
  apply (swap_success state pos hbelow (hr.swap_reachable pos hge)
    (state.boundNotFinal dest pos hbound hne)).mono
  intro next hs
  have htop := hs.bound_top dest hbound
  have hlen := hs.size
  refine ⟨⟨⟨hs.invariant h hge, by omega, Or.inr htop⟩, ?_⟩, hr.swap pos hge hs⟩
  apply (next.isFinal_of_bound_val_iff dest _ htop).not.mpr
  omega

end Shuffler.BuildBottomUp
