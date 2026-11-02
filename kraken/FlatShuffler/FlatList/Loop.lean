module

public import FlatShuffler.FlatList.Step
import all FlatShuffler.FlatList.Step

@[expose] public section

/-!
The loop of the flat model against the loop of the list model. The final permutation is a
hypothesis here: `Permute.lean` proves it.
-/

namespace FlatShuffler.Flat

/-! ## Unfolding of the flat `loop` -/

theorem floop_ret {fs : St} {t : Word} {r : EmissionOutcome × St} (ht : t < fs.targetSize)
    (h : body fs t = .ret r) : loop fs t = r := by
  rw [loop, ite_eq_left ht]
  split <;> simp_all

theorem floop_cont {fs fs' : St} {t t' : Word} (ht : t < fs.targetSize)
    (h : body fs t = .cont fs' t') : loop fs t = loop fs' (t' + 1) := by
  rw [loop, ite_eq_left ht]
  split <;> simp_all

theorem floop_ge {fs : St} {t : Word} (ht : ¬t < fs.targetSize) :
    loop fs t = if fs.size ≠ fs.targetSize then (.assertionExit, fs) else (.done, fs) := by
  rw [loop, ite_eq_right ht]

/-! ## The loop -/

-- The final permutation of the flat model holds the final permutation of the list model.
def PermR (e : Env) : Prop :=
  ∀ fs st t, Sim e fs st → InvS e st t → st.pendingGenerations = 0 → st.len = e.n →
    SimR e (permuteMapping fs) (finish st)

theorem Sim.size_eq_iff {e : Env} {fs : St} {st : FlatShuffler.St} (hs : Sim e fs st) :
    fs.size = fs.targetSize ↔ st.len = e.n := by
  rw [hs.n, ← hs.size]
  exact ⟨congrArg BitVec.toNat, eq_of_toNat⟩

theorem sim_loop {e : Env} (hfin : PermR e) (fs : St) (st : FlatShuffler.St) (k : Nat)
    (hs : Sim e fs st) (hi : InvS e st k) (hk : k ≤ st.len) :
    SimR e (loop fs (BitVec.ofNat 64 k)) (FlatShuffler.loop finish e st k) := by
  have hn := hs.n
  have hle : e.n ≤ maxStackSize := hs.n ▸ hs.n_le
  have hkn := hi.t_le
  have hkw : (BitVec.ofNat 64 k).toNat = k := toNat_ofNat_of_lt (by unfold maxStackSize at hle; omega)
  by_cases ht : k < e.n
  · have ht' : BitVec.ofNat 64 k < fs.targetSize := by bv_omega
    have hb := sim_body hs (t := BitVec.ofNat 64 k) (by rw [hkw]; exact hi)
      (by rw [hkw]; exact ht) (by rw [hkw]; exact hk)
    rw [hkw] at hb
    cases h : step e st k with
    | error err =>
      rw [loop_error ht h]
      rw [h] at hb
      cases hx : body fs (BitVec.ofNat 64 k) with
      | ret r => rw [hx] at hb; rw [floop_ret ht' hx]; exact hb
      | cont fs' t' => rw [hx] at hb; exact (hb : False).elim
    | ok r =>
      obtain ⟨st', nx⟩ := r
      cases nx with
      | finish =>
        obtain ⟨hst, hp⟩ := step_finish h
        rw [hst] at h
        rw [loop_finish ht h]
        rw [h] at hb
        cases hx : body fs (BitVec.ofNat 64 k) with
        | cont fs' t' => rw [hx] at hb; exact (hb : False).elim
        | ret r =>
          rw [hx] at hb
          rw [floop_ret ht' hx]
          obtain ⟨fs', hs', ha, hb'⟩ := hb
          by_cases hl : st.len = e.n
          · rw [ite_eq_left hl, hb' (hs'.size_eq_iff.mpr hl)]
            exact hfin fs' st k hs' hi hp hl
          · rw [ite_eq_right hl, ha (fun h => hl (hs'.size_eq_iff.mp h))]
            exact rfl
      | next k' =>
        have hprog := step_progress h
        rw [loop_next ht h]
        rw [h] at hb
        cases hx : body fs (BitVec.ofNat 64 k) with
        | ret r => rw [hx] at hb; exact (hb : False).elim
        | cont fs' t' =>
          rw [hx] at hb
          obtain ⟨hk', hs'⟩ := hb
          rw [floop_cont ht' hx, hk']
          exact sim_loop hfin fs' st' k' hs' (step_invS hi ht h) (step_le_len hi.pos h hk)
  · rw [floop_ge (by bv_omega), loop_ge ht]
    by_cases hl : st.len = e.n
    · rw [ite_eq_right (c := fs.size ≠ fs.targetSize) (fun h => h (hs.size_eq_iff.mpr hl)),
        ite_eq_left hl]
      exact ⟨rfl, hs⟩
    · rw [ite_eq_left (c := fs.size ≠ fs.targetSize) (fun h => hl (hs.size_eq_iff.mp h)),
        ite_eq_right hl]
      exact rfl
termination_by (e.n - k, st.pendingGenerations)
decreasing_by
  rcases hprog with h' | ⟨h', hp⟩
  · exact Prod.Lex.left _ _ (by omega)
  · subst h'; exact Prod.Lex.right _ hp

/-! ## The result of `build_bottom_up` -/

-- The word and the state that `build_bottom_up` gives for the result `r` of the loop.
def outOf (r : EmissionOutcome × St) : Word × Option St :=
  match r.1 with
  | .done => (.ofNat 64 r.2.trace.length, some { r.2 with blockedOffset := 0, blockedExcess := 0 })
  | .blocked => (.ofNat 64 r.2.trace.length, some r.2)
  | .assertionExit => (-2, some r.2)

theorem rel_outOf {e : Env} {r : EmissionOutcome × St} {m : M FlatShuffler.St} (h : SimR e r m) :
    Rel (outOf r) m := by
  match m, h with
  | .ok st, ⟨h1, h2⟩ =>
    refine ⟨{ r.2 with blockedOffset := 0, blockedExcess := 0 }, ?_, ?_⟩
    · unfold outOf; rw [h1, h2.trace]
    · exact ⟨h2.trace, h2.slots, rfl, rfl⟩
  | .error (.blocked p x s), ⟨h1, h2⟩ =>
    refine ⟨r.2, ?_, h2.holds⟩
    unfold outOf; rw [h1, h2.sim.trace]
  | .error .assertion, h1 =>
    show (outOf r).1 = -2#64
    unfold outOf; rw [h1]; rfl

end FlatShuffler.Flat
