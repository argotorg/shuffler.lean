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

def Success (result : Except Error α) (post : α → Prop) : Prop :=
  ∃ value, result = .ok value ∧ post value

theorem Success.of_triple (action : Action source target spills α)
    (state : State source target spills) (post : α → State source target spills → Prop)
    (h : ⦃fun s => s = state⦄ action ⦃post⦄) :
    Success (action.run state) (fun result => post result.1 result.2) := by
  have hp := h.le_wp state rfl
  rw [StateT.wp_apply_eq] at hp
  cases heq : action.run state with
  | ok result =>
    rw [heq] at hp
    exact ⟨result, rfl, hp⟩
  | error err =>
    rw [heq] at hp
    simp [wp, WP.wpTrans, EPost.Cons.head_bot] at hp

theorem Spec.success {result : Except Error α} {post : α → Prop}
    (h : Spec result post) (hn : NoBlocked result) : Success result post := by
  cases result with
  | ok value => exact ⟨value, rfl, h⟩
  | error err => cases err <;> contradiction

theorem Success.bind {result : Except Error α} {pre : α → Prop} {next : α → Except Error β}
    {post : β → Prop} (h : Success result pre)
    (step : ∀ value, pre value → Success (next value) post) :
    Success (result >>= next) post := by
  obtain ⟨value, rfl, hv⟩ := h
  exact step value hv

theorem Success.mono {result : Except Error α} {pre post : α → Prop}
    (h : Success result pre) (step : ∀ value, pre value → post value) : Success result post := by
  obtain ⟨value, heq, hv⟩ := h
  exact ⟨value, heq, step value hv⟩

theorem Reachable.filtered {state : State source target spills} (h : Reachable state)
    (dest : Fin target.length) (hdest : state.mapping.symm dest = none)
    (hgen : ¬(target[dest].can_be_freely_generated ∨ spills.is_spilled target[dest])) :
    ∃ copy, (state.stack.shallowestCopyPosition target[dest]).filter
      (fun pos => state.stack.isDupReachable pos) = some copy := by
  have hc : HasCopy state.stack target[dest] := by
    rcases h dest hdest with hfree | hspill | hcopy
    · exact (hgen (Or.inl hfree)).elim
    · exact (hgen (Or.inr hspill)).elim
    · exact hcopy
  obtain ⟨copy, heq, hreach⟩ := hc.shallowest
  exact ⟨copy, by simpa [hreach] using heq⟩

theorem generate_noBlocked (state : State source target spills) (dest : Fin target.length)
    (h : Reachable state) : NoBlocked ((generate dest.val).exec state) := by
  have hfilter := h.filtered dest
  have hs : ⦃fun s => s = state⦄ generate dest.val
      ⦃fun _ _ => True; noBlockedErrors⦄ := by
    vcgen [generate, produce, push, dup, swapDestinations, swapWith,
      ensure, requires, index, slotAt, State.isSwapReachable, State.depthOf]
    all_goals subst_vars
    all_goals simp_all [noBlockedErrors]
  have hp := hs.le_wp state rfl
  rw [StateT.wp_apply_eq] at hp
  cases heq : (generate dest.val).run state with
  | error err =>
    rw [heq] at hp
    cases err with
    | blocked excess => exact False.elim hp
    | assertion reason => simp [NoBlocked, Action.exec, heq]
  | ok result => simp [NoBlocked, Action.exec, heq]

theorem generate_success (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest)
    (h : Reachable state) :
    Success ((generate dest.val).exec state) (fun next => Generation state next dest) :=
  (generate_contract state dest hbound havailable).success (generate_noBlocked state dest h)

theorem Growth.final_swapped {state produced next : State source target spills}
    {dest : Fin target.length} (h : Growth state produced dest pending)
    {pos : Fin produced.stack.length} (hpos : pos.val = dest.val) (hs : Swapped produced next pos) :
    next.isFinal dest :=
  hs.final dest hpos (by simpa [h.size] using h.bound)

theorem Growth.final_at_exit {state produced : State source target spills}
    {dest : Fin target.length} (h : Growth state produced dest pending)
    (hle : dest.val ≤ state.stack.length)
    (hexit : dest.val + 1 < produced.stack.length → produced.isFinal dest) :
    produced.isFinal dest := by
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
    Spec ((generate dest.val).exec state) (fun next => next.isFinal dest) := by
  apply Spec.of_action
  vcgen [generate]
  all_goals try simp only [Fin.val_inj] at *
  all_goals subst_vars
  all_goals try assumption
  all_goals try simp_all
  all_goals first
    | exact Growth.final_swapped (by assumption) rfl (by assumption)
    | exact Growth.final_swapped (by assumption) rfl (Swapped.retag _ _ (by assumption))
    | exact Growth.final_at_exit (by assumption) hle (by assumption)
    | exact of_decide_eq_true (Eq.symm (by assumption))
    | exact (show ¬ _ from by assumption) (Growth.swap_reachable (by assumption) hreach _ rfl)
    | omega

theorem generate_reachable (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest)
    (hr : WithinReach cursor state) (hcursor : cursor ≤ dest.val) (hready : Ready state dest) :
    Success ((generate dest.val).exec state) (fun next =>
      Generation state next dest ∧ Reachable next ∧
      (dest.val ≤ state.stack.length → next.isFinal dest)) := by
  obtain ⟨next, heq, hg⟩ := generate_success state dest hbound havailable hr.copies
  have hf (hle : dest.val ≤ state.stack.length) : next.isFinal dest := by
    have hreach : state.stack.length - dest.val ≤ MAX_SWAP_DEPTH := by have := hr.width; omega
    have hs := generate_final state dest hbound havailable hle hreach
    simpa [heq, Spec] using hs
  exact ⟨next, heq, hg, hg.reachable hr hcursor hready hbound hf, hf⟩

theorem swap_noBlocked (state : State source target spills) (offset : ℕ) :
    NoBlocked ((swapWith offset).exec state) := by
  have hs : ⦃fun s => s = state⦄ swapWith offset ⦃fun _ _ => True; noBlockedErrors⦄ := by
    vcgen [swapWith, index, requires, ensure]
    all_goals simp_all [noBlockedErrors]
  have hp := hs.le_wp state rfl
  rw [StateT.wp_apply_eq] at hp
  cases heq : (swapWith offset).run state with
  | error err =>
    rw [heq] at hp
    cases err with
    | blocked excess => exact False.elim hp
    | assertion reason => simp [NoBlocked, Action.exec, heq]
  | ok result => simp [NoBlocked, Action.exec, heq]

theorem swap_success (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hnfinal : ¬ state.isFinal pos.val) :
    Success ((swapWith pos.val).exec state) (fun next => Swapped state next pos) :=
  (swap_spec state pos hbelow hreach hnfinal).success (swap_noBlocked state pos.val)

theorem Placement.swap_final_success {state : State source target spills} {dest : Fin target.length}
    (h : Placement dest state) (hr : WithinReach dest.val state)
    (hbelow : dest.val + 1 < state.stack.length) (hnfinal : ¬state.isFinal dest) :
    Success ((swapWith dest.val).exec state) (fun next =>
      Invariant (dest.val + 1) next ∧ WithinReach (dest.val + 1) next) := by
  let pos : Fin state.stack.length := ⟨dest.val, h.in_bounds⟩
  apply (swap_success state pos hbelow (hr.swap_reachable pos le_rfl) hnfinal).mono
  intro next hs
  exact ⟨(hs.invariant h.toInvariant le_rfl).advance
    (hs.final dest rfl (h.position.resolve_left hnfinal)), (hr.swap pos le_rfl hs).advance⟩

theorem Invariant.swap_bound_success {state : State source target spills} {dest : Fin target.length}
    (h : Invariant dest.val state) (hr : WithinReach dest.val state)
    (pos : Fin state.stack.length) (hbound : state.mapping.symm dest = some pos)
    (hbelow : pos.val + 1 < state.stack.length) (hne : pos.val ≠ dest.val) :
    Success ((swapWith pos.val).exec state) (fun next =>
      (Placement dest next ∧ ¬next.isFinal dest) ∧ WithinReach dest.val next) := by
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
