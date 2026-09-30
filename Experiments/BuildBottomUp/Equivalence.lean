import Experiments.BuildBottomUp.ScanEquivalence
import Experiments.BuildBottomUp.FiniteExecution

namespace BuildBottomUpExperiments.Checked

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem result_cases (r : Except ε α) :
    (∃ e, r = .error e) ∨ (∃ a, r = .ok a) := by
  cases r with
  | error e => exact Or.inl ⟨e, rfl⟩
  | ok a => exact Or.inr ⟨a, rfl⟩

theorem attach_ok {r : Except ε α} {a : α} (h : r = .ok a) :
    r.attach = .ok ⟨a, h⟩ := by subst r; rfl

theorem attach_error {r : Except ε α} {e : ε} (h : r = .error e) :
    r.attach = .error e := by subst r; rfl

theorem ensure_true (reason : String) : ensure True reason = .ok () := rfl

theorem swapDestinations_eq (state : State source target spills)
    (a b : Fin state.stack.length) :
    swapDestinations state a.val b.val =
      .ok { state with mapping := state.mapping.swapDestinations a b } := by
  simp [swapDestinations, index, a.isLt, b.isLt, bind, Except.bind, pure, Except.pure]

theorem and_cases {P Q : Prop} (h : P ∧ Q) (k : P → Q → α) :
    And.casesOn h k = k h.1 h.2 := by cases h; rfl

-- Normalize the administrative binds introduced by the two do blocks.
macro "resume_with " h:term : tactic => `(tactic|
  simpa only [buildWith, finishLoop, liftResult, Except.mapError, bind, Except.bind,
    ne_eq, pure_bind, bind_assoc, pure, Except.pure, ↓reduceIte, ↓reduceDIte,
    Option.isNone_iff_eq_none, and_assoc, and_true, true_and, and_false,
    false_and, not_false_eq_true, not_true_eq_false, eq_self,
    Bool.false_eq_true, Bool.true_eq_false] using $h)

-- This is the common final placement phase. The state and its placement proof
-- are explicit parameters; each successful path uses the induction hypothesis.
-- Unfold the old definition's generated matcher for the placement proof pair.
set_option linter.auxLemma false in
macro "finish_placement " c:term ", " st:term ", " hp:term ", " hn:term ", " advance:term : tactic => `(tactic| (
  unfold build_bottom_up.match_20
  simp only [and_cases]
  have hnf := $hn
  try dsimp +zetaDelta only at hnf
  try simp +zetaDelta only [hnf, not_false_eq_true, ensure_true, bind, Except.bind]
  by_cases hnotTop : $c ≠ ($st).stack.length - 1
  · try dsimp +zetaDelta only at hnotTop
    try simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte, ↓reduceDIte]
    let pos : Fin ($st).stack.length := ⟨$c, ($hp).in_bounds⟩
    have hbelow := Stack.below_of_not_top ($st).stack pos hnotTop
    by_cases hr : ($st).stack.is_swap_reachable pos
    · try dsimp +zetaDelta only at hr
      try simp +zetaDelta only [hr, show isSwapReachable $st pos.val from hr,
        not_true_eq_false, ↓reduceIte, ↓reduceDIte]
      rw [swapWith_eq $st pos hbelow hr hnf]
      try simp +zetaDelta only [bind, Except.bind, pure, Except.pure]
      resume_with ($advance _ (($hp).swap_final hbelow hr hnf))
    · try dsimp +zetaDelta only at hr
      try simp +zetaDelta only [hr, show ¬ isSwapReachable $st pos.val from hr, not_false_eq_true,
        ↓reduceIte, ↓reduceDIte]
      rfl
  · try dsimp +zetaDelta only at hnotTop
    try simp +zetaDelta only [hnotTop, ↓reduceIte, ↓reduceDIte, bind, Except.bind,
      pure, Except.pure]
    resume_with ($advance $st (($hp).finish_at_top (not_not.mp hnotTop)))))

theorem complete_size (state : State source target spills)
    (inv : BuildBottomUpInvariant cursor state) (hdone : target.length ≤ cursor) :
    state.stack.length = target.length := by
  have hs := inv.size
  apply Nat.le_antisymm (by omega)
  by_contra h
  have hl : state.stack.length < target.length := by omega
  have hf := inv.processed ⟨state.stack.length, hl⟩ (by simpa using (show state.stack.length < cursor by omega))
  have := state.is_final_lt ⟨state.stack.length, hl⟩ hf
  change state.stack.length < state.stack.length at this
  omega

-- Compare one iteration under the old function's well-founded induction.
-- The loop interpreter is a parameter so this proof also establishes finite
-- execution, independently of the logical value assigned to a divergent loop.
theorem buildWith_eq
    (loop : Frame source target spills → M (Frame source target spills))
    (unfold_loop : ∀ frame, loop frame = (do
      match ← (loopParts source target spills).val () frame with
      | .done out => pure out
      | .yield next => loop next))
    (cursor : ℕ) (state : State source target spills)
    (hi : LoopInvariant cursor state)
    (hs : state.stack.length + state.pending_generations = target.length)
    (hp : state.mapping.unmapped_target_slots = state.pending_generations)
    (ha : ∀ i, state.is_available i) :
    buildWith loop cursor state = liftResult (build_bottom_up cursor state hi hs hp ha) := by
  induction cursor, state, hi, hs, hp, ha using build_bottom_up.induct
  case case1 cursor state hi hs hp ha hd =>
    have hsize := complete_size state ⟨hi, hs, hp, ha⟩ hd
    rw [buildWith, unfold_loop, build_bottom_up.eq_def]
    dsimp only [loopParts, finishLoop]
    simp [show ¬cursor < target.length by omega, hd, hsize, ensure_true, liftResult,
      pure, Except.pure, Except.mapError, bind, Except.bind]
  case case2 cursor state hi hs hp ha hd dest hf ih =>
    have hskip : cursor < state.stack.length ∧ state.is_final cursor := hf
    rw [buildWith, unfold_loop, build_bottom_up.eq_def]
    dsimp only [loopParts, finishLoop]
    simp only [show cursor < target.length by omega, hd, hskip,
      and_self, ↓reduceIte, ↓reduceDIte, pure_bind]
    simpa only [buildWith, finishLoop] using ih
  case case3 cursor state hi hs hp ha hd dest hskip hnfinal hz ht hc =>
    have hskip' : ¬ (cursor < state.stack.length ∧ state.is_final cursor) := hskip
    rw [buildWith, unfold_loop, build_bottom_up.eq_def]
    dsimp only [loopParts, finishLoop]
    simp only [show cursor < target.length by omega, hd, hskip', hz,
      ↓reduceIte, ↓reduceDIte,
      bind_assoc]
    simp only [requires, dite_eq_left (And.intro hc.1 hc.2), pure_bind]
    cases hperm : Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hc.1 hc.2) with
    | error err => cases err; rfl
    | ok result => cases result; rfl
  case case4 cursor state hi hs hp ha hd dest hskip hnfinal hz advance placed genPlaced top urgent =>
    have hskip' : ¬ (cursor < state.stack.length ∧ state.is_final cursor) := hskip
    have inv : BuildBottomUpInvariant cursor state := ⟨hi, hs, hp, ha⟩
    rw [buildWith, unfold_loop, build_bottom_up.eq_def]
    dsimp only [loopParts, finishLoop]
    simp only [hd, hskip', hz, ↓reduceDIte]
    erw [← newUrgent.eq_def cursor state, ← oldUrgent.eq_def cursor state]
    simp only [show cursor < target.length by omega, ↓reduceIte,
      pure_bind, bind_assoc]
    rw [urgent_eq cursor state]
    cases hscan : oldUrgent cursor state with
    | error err =>
      cases err
      rfl
    | ok choice =>
      simp only [liftMap_ok, bind, Except.bind]
      cases choice
      case' some u =>
        have hu : u.val.val ≠ cursor ↔ u.val ≠ dest := by simp [dest, Fin.ext_iff]
        simp only [Option.map_some, Option.isNone_some, Option.isSome_some, Bool.false_eq_true,
          ne_eq, Option.some.injEq, Option.get_some, true_and,
          not_true_eq_false, false_and, ↓reduceIte, ↓reduceDIte]
        by_cases hurg : u.val ≠ dest ∧ state.stack.length - cursor < MAX_SWAP_DEPTH
        case pos =>
          dsimp only [dest] at hu hurg
          simp only [hu, ne_eq, hurg.1, hurg.2, not_false_eq_true, and_self, ↓reduceIte]
          rw [generate_eq state u.val u.property (ha u.val)]
          rcases result_cases (state.generate u.val u.property (ha u.val)) with ⟨err, hgen⟩ | ⟨next, hgen⟩
          · cases err
            conv_lhs => rw [hgen]
            erw [attach_error hgen]
            rfl
          · conv_lhs => rw [hgen]
            erw [attach_ok hgen]
            simp only [liftResult, Except.mapError, pure, Except.pure]
            simpa only [buildWith, finishLoop, liftResult, Except.mapError, Except.attach,
              bind, Except.bind, pure_bind, bind_assoc,
              pure, Except.pure, ↓reduceIte, ↓reduceDIte]
              using urgent u next hgen
        case' neg =>
          dsimp only [dest] at hu hurg
          have htop : state.stack.length < target.length := by omega
          simp only [hu, hurg, htop, ↓reduceIte, ↓reduceDIte]
      case' none =>
        simp only [Option.map_none, Option.isNone_none, Option.isSome_none, Bool.false_eq_true,
          eq_self, not_false_eq_true, true_and, false_and, ↓reduceDIte]
        have htop : state.stack.length < target.length := by omega
        let topDest : Fin target.length := ⟨state.stack.length, htop⟩
        have hposition : positionOf state state.stack.length = (state.mapping.symm topDest).map Fin.val := by
          simp [positionOf, htop, topDest]
        rw [hposition]
        simp only [htop, Option.isNone_map, Option.isNone_iff_eq_none, true_and, ↓reduceDIte]
        by_cases hgen : state.stack.length > cursor ∧ state.mapping.symm topDest = none ∧
            state.stack.length - cursor < MAX_SWAP_DEPTH
        case pos =>
          dsimp only [topDest] at hgen ⊢
          simp only [hgen.1, hgen.2.1, hgen.2.2, and_true, ↓reduceIte, ↓reduceDIte]
          rw [generate_eq state topDest hgen.2.1 (ha topDest)]
          rcases result_cases (state.generate topDest hgen.2.1 (ha topDest)) with ⟨err, hresult⟩ | ⟨next, hresult⟩
          · cases err
            conv_lhs => rw [hresult]
            erw [attach_error hresult]
            rfl
          · conv_lhs => rw [hresult]
            erw [attach_ok hresult]
            simp only [liftResult, Except.mapError, pure, Except.pure]
            simpa only [buildWith, finishLoop, liftResult, Except.mapError, bind, Except.bind,
              pure_bind, bind_assoc,
              pure, Except.pure, ↓reduceIte, ↓reduceDIte, Option.isNone_iff_eq_none, and_assoc]
              using top none htop ⟨by simp, hgen.1, hgen.2.1, hgen.2.2⟩ next hresult
        case' neg =>
          dsimp only [topDest] at hgen ⊢
          simp only [hgen, ↓reduceIte, ↓reduceDIte]
      all_goals
        have hcursor : cursor < target.length := by omega
        have hposition : positionOf state cursor = (state.mapping.symm dest).map Fin.val := by
          simp [positionOf, hcursor, dest]
        rw [hposition]
        by_cases hb : (state.mapping.symm dest).isSome
        case' pos =>
          let carrier := (state.mapping.symm dest).get hb
          have hbound : state.mapping.symm dest = some carrier := (Option.some_get hb).symm
          have hge : cursor ≤ carrier.val := hi.bound_ge dest carrier hbound le_rfl
          have hcurrent : cursor < state.stack.length := lt_of_le_of_lt hge carrier.isLt
          let current : Fin state.stack.length := ⟨cursor, hcurrent⟩
          have hslot : slotAt state.stack cursor = .ok state.stack[current] := slotAt_eq _ current
          conv_lhs => rw [hbound, Option.map_some]
          dsimp only [dest] at hb
          simp only [hb, eq_self, ↓reduceDIte, hge,
            ensure_true, hslot, slotAt_eq]
          by_cases hequal : state.stack[current] = state.stack[carrier]
          · have hequal' := hequal
            simp only [Fin.getElem_fin] at hequal' ⊢
            dsimp only [current, carrier, dest]
            dsimp +zetaDelta only at hequal'
            simp only [hequal', ↓reduceIte, ↓reduceDIte, eq_self, ensure_true]
            rw [swapDestinations_eq state current carrier]
            simp only [pure, Except.pure]
            let chosen : state.MovableCopy carrier := ⟨current, hequal, hnfinal⟩
            obtain ⟨hretag, hdest⟩ := inv.retag_copy (dest := dest) chosen hbound
            let retag := { state with mapping := state.mapping.swapDestinations chosen carrier }
            have hf := (State.is_final_of_bound_iff retag dest chosen hdest).mpr
              (show chosen.val = dest.val from rfl)
            resume_with (advance _ (hretag.advance hf))
          · have hequal' := hequal
            simp only [Fin.getElem_fin] at hequal' ⊢
            dsimp only [current, carrier, dest]
            dsimp +zetaDelta only at hequal'
            simp only [hequal', ↓reduceIte, ↓reduceDIte]
            let initial : state.MovableCopy carrier :=
              ⟨carrier, rfl, state.bound_not_final_of_not_final dest carrier hbound hnfinal⟩
            have hcopies := copy_eq state carrier initial
            simp only [newCopy, slotAt_eq, bind, Except.bind] at hcopies
            erw [hcopies, ← oldCopy.eq_def state carrier initial]
            cases hsearch : oldCopy state carrier initial with
            | error err => cases err; rfl
            | ok chosen =>
              simp only [liftMap_ok]
              rw [slotAt_eq state.stack chosen.toFin]
              have heq := chosen.equal
              simp only [Fin.getElem_fin] at heq ⊢
              dsimp only [carrier, dest] at heq ⊢
              simp only [heq, eq_self, ensure_true]
              rw [swapDestinations_eq state chosen.toFin carrier]
              simp only [pure, Except.pure]
              obtain ⟨hretag, hdest⟩ := inv.retag_copy (dest := dest) chosen hbound
              let retag := { state with mapping := state.mapping.swapDestinations chosen carrier }
              by_cases hplaced : chosen.val = cursor
              · simp only [hplaced, eq_self, ↓reduceIte, ↓reduceDIte]
                have hf := (State.is_final_of_bound_iff retag dest chosen hdest).mpr hplaced
                resume_with (advance retag (hretag.advance hf))
              · simp only [hplaced, ↓reduceIte, ↓reduceDIte]
                by_cases hnotTop : chosen.val ≠ retag.stack.length - 1
                · dsimp +zetaDelta only at hnotTop
                  simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte, ↓reduceDIte]
                  have hbelow := Stack.below_of_not_top retag.stack chosen hnotTop
                  by_cases hr : retag.stack.is_swap_reachable chosen.toFin
                  · dsimp +zetaDelta only at hr
                    simp +zetaDelta only [hr, show isSwapReachable retag chosen.val from hr, not_true_eq_false,
                      ↓reduceIte, ↓reduceDIte]
                    have hnf := retag.bound_not_final dest chosen hdest hplaced
                    rw [swapWith_eq retag chosen.toFin hbelow hr hnf]
                    have hplace := hretag.swap_bound chosen hdest hbelow hr hplaced
                    finish_placement cursor, (retag.swapWith chosen hbelow hr hnf), hplace.1, hplace.2, advance
                  · dsimp +zetaDelta only at hr
                    simp +zetaDelta only [hr, show ¬ isSwapReachable retag chosen.val from hr,
                      not_false_eq_true, ↓reduceIte, ↓reduceDIte]
                    rfl
                · dsimp +zetaDelta only at hnotTop
                  simp only [hnotTop, ↓reduceIte, ↓reduceDIte]
                  have hplace := hretag.bound_at_top chosen hdest (not_not.mp hnotTop) hplaced
                  finish_placement cursor, retag, hplace.1, hplace.2, advance
        case' neg =>
          have hbound : state.mapping.symm dest = none := by simpa using hb
          conv_lhs => rw [hbound, Option.map_none]
          dsimp only [dest] at hb
          simp only [hb, Bool.false_eq_true, ↓reduceDIte]
          rw [generate_eq state dest hbound (ha dest)]
          rcases result_cases (state.generate dest hbound (ha dest)) with ⟨err, hresult⟩ | ⟨next, hresult⟩
          · cases err
            conv_lhs => rw [hresult]
            erw [attach_error hresult]
            rfl
          · conv_lhs => rw [hresult]
            erw [attach_ok hresult]
            simp only [liftResult, Except.mapError, pure, Except.pure]
            have hplace := inv.generate_placement hbound hresult
            by_cases hfinal : next.is_final cursor
            case pos =>
              simp only [hfinal, ↓reduceIte, ↓reduceDIte]
              simpa only [buildWith, finishLoop, liftResult, Except.mapError, bind, Except.bind,
                pure_bind, bind_assoc,
                pure, Except.pure, ↓reduceIte, ↓reduceDIte, Option.isNone_iff_eq_none, and_assoc]
                using advance next (hplace.toBuildBottomUpInvariant.advance hfinal)
            case' neg =>
              simp only [hfinal, ↓reduceIte, ↓reduceDIte]
              finish_placement cursor, next, hplace, hfinal, advance

-- Exact equality of the dependent result: stack, trace, and error excess.
theorem buildBottomUp_eq (cursor : ℕ) (state : State source target spills)
    (hi : LoopInvariant cursor state)
    (hs : state.stack.length + state.pending_generations = target.length)
    (hp : state.mapping.unmapped_target_slots = state.pending_generations)
    (ha : ∀ i, state.is_available i) :
    buildBottomUp cursor state = liftResult (build_bottom_up cursor state hi hs hp ha) := by
  rw [buildBottomUp_as_loop]
  apply buildWith_eq _ ?_ cursor state hi hs hp ha
  intro frame
  rw [loop_unfold]
  cases hstep : (loopParts source target spills).val () frame with
  | error e => rfl
  | ok step => cases step <;> rfl

-- The finite-execution claim is separate from equality of Lean values.
-- The same induction works for an interpreter that reports nontermination as
-- an assertion error. Equality to the old result rules out that error.
theorem buildBottomUp_terminates (cursor : ℕ) (state : State source target spills)
    (hi : LoopInvariant cursor state)
    (hs : state.stack.length + state.pending_generations = target.length)
    (hp : state.mapping.unmapped_target_slots = state.pending_generations)
    (ha : ∀ i, state.is_available i) :
    ∃ r, LoopRuns (loopParts source target spills).val (none, state, cursor) r := by
  by_contra h
  have heq := buildWith_eq (loopOr (.assertion "loop has no finite execution") (loopParts source target spills).val)
    (fun frame => by
      rw [loopOr_unfold]
      cases hstep : (loopParts source target spills).val () frame with
      | error e => rfl
      | ok step => cases step <;> rfl)
    cursor state hi hs hp ha
  simp only [buildWith, loopOr, h, ↓reduceDIte, bind, Except.bind] at heq
  cases hresult : build_bottom_up cursor state hi hs hp ha with
  | error err => cases err; simp [hresult, liftResult, Except.mapError] at heq
  | ok result => simp [hresult, liftResult, Except.mapError] at heq

theorem buildBottomUp_noAssertion (cursor : ℕ) (state : State source target spills)
    (inv : BuildBottomUpInvariant cursor state) (reason : String) :
    buildBottomUp cursor state ≠ .error (.assertion reason) := by
  rw [buildBottomUp_eq cursor state inv.processed inv.size inv.pending inv.available]
  cases build_bottom_up cursor state inv.processed inv.size inv.pending inv.available with
  | error err => cases err; simp [liftResult, Except.mapError]
  | ok result => simp [liftResult, Except.mapError]

-- A finite loop execution, followed by the unchanged return code, produces
-- exactly the old result. This combines termination and result equality.
theorem buildBottomUp_total (cursor : ℕ) (state : State source target spills)
    (inv : BuildBottomUpInvariant cursor state) :
    ∃ r, LoopRuns (loopParts source target spills).val (none, state, cursor) r ∧
      (r >>= finishLoop) =
        liftResult (build_bottom_up cursor state inv.processed inv.size inv.pending inv.available) := by
  obtain ⟨r, hr⟩ := buildBottomUp_terminates cursor state
    inv.processed inv.size inv.pending inv.available
  refine ⟨r, hr, ?_⟩
  have heq := buildBottomUp_eq cursor state inv.processed inv.size inv.pending inv.available
  rw [buildBottomUp_as_loop, buildWith, hr.result_eq] at heq
  exact heq

def buildBottomUpVerified (cursor : ℕ) (state : State source target spills)
    (inv : BuildBottomUpInvariant cursor state) : Except ShuffleErr (Result source spills) :=
  restoreResult (buildBottomUp cursor state) (buildBottomUp_noAssertion cursor state inv)

theorem liftResult_injective : Function.Injective (liftResult (α := α)) := by
  intro a b h
  cases a with
  | error a => cases a; cases b with
    | error b => cases b; simpa [liftResult, Except.mapError] using h
    | ok b => simp [liftResult, Except.mapError] at h
  | ok a => cases b with
    | error b => cases b; simp [liftResult, Except.mapError] at h
    | ok b => simpa [liftResult, Except.mapError] using h

theorem buildBottomUpVerified_eq (cursor : ℕ) (state : State source target spills)
    (inv : BuildBottomUpInvariant cursor state) :
    buildBottomUpVerified cursor state inv =
      build_bottom_up cursor state inv.processed inv.size inv.pending inv.available := by
  apply liftResult_injective
  rw [buildBottomUpVerified, restoreResult_eq,
    buildBottomUp_eq cursor state inv.processed inv.size inv.pending inv.available]

/-- info: 'BuildBottomUpExperiments.Checked.buildBottomUp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_eq

/-- info: 'BuildBottomUpExperiments.Checked.buildBottomUp_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_terminates

/-- info: 'BuildBottomUpExperiments.Checked.buildBottomUp_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_total

/-- info: 'BuildBottomUpExperiments.Checked.buildBottomUpVerified_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUpVerified_eq

end BuildBottomUpExperiments.Checked
