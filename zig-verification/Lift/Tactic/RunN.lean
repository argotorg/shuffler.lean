module

public import Lift.Sem.Reaches
public import Lift.P2.Total.Memory

@[expose] public section

/-! `Reaches` from one equation for a run of `n` steps.

`runN step n s` is the effect tree of `n` steps of `step` from `s`: the trees of the steps are
composed with `Effects.andThen`. A block row (`Reaches step policy Q s` for the states of one basic
block) follows from an equation `runN step n s = e` that `simp` proves, and from the statement that
each result of the tree `e` is a next state in `Q`. -/

/-- Sequential composition of effect trees: run `e`, then `k` from each state that `e` gives. -/
def Effects.andThen : Effects → (MachineState → Effects) → Effects
  | .done a, k => k a
  | .unimplemented m, _ => .unimplemented m
  | .gp_unaligned a w, _ => .gp_unaligned a w
  | .fault f, _ => .fault f
  | .nonmem_load m a w r, k => .nonmem_load m a w fun v m' => (r v m').andThen k
  | .nonmem_store m a v r, k => .nonmem_store m a v fun m' => (r m').andThen k
  | @Effects.undefined α inst r, k => @Effects.undefined α inst fun v => (r v).andThen k
  | .require_read_access a w ok, k => .require_read_access a w fun u => (ok u).andThen k
  | .require_write_access a w ok, k => .require_write_access a w fun u => (ok u).andThen k
  | .require_exec_access p ok, k => .require_exec_access p fun u => (ok u).andThen k

namespace Lift.Tactic

open Lift.P2.Total Lift.Sem

/-- `n` steps of `step` from `s`. -/
def runN (step : MachineState → Effects) : Nat → MachineState → Effects
  | 0, s => .done s
  | n + 1, s => (step s).andThen (runN step n)

theorem runN_zero (step : MachineState → Effects) (s : MachineState) :
    runN step 0 s = .done s := rfl

theorem runN_succ (step : MachineState → Effects) (n : Nat) (s : MachineState) :
    runN step (n + 1) s = (step s).andThen (runN step n) := rfl

theorem andThen_load (D : MachineData) (a : BitVec 64) (w : Width)
    (r : w.type → MachineData → Effects) (k : MachineState → Effects) :
    (D.load a w r).andThen k = D.load a w (fun v s => (r v s).andThen k) := by
  unfold MachineData.load
  simp only [Effects.andThen]
  split <;> rfl

theorem andThen_store (D : MachineData) (a : BitVec 64) (w : Width) (v : w.type)
    (r : MachineData → Effects) (k : MachineState → Effects) :
    (D.store a v r).andThen k = D.store a v (fun s => (r s).andThen k) := by
  unfold MachineData.store
  simp only [Effects.andThen]
  split <;> rfl

theorem andThen_ite (c : Prop) [Decidable c] (x y : Effects) (k : MachineState → Effects) :
    (if c then x else y).andThen k = if c then x.andThen k else y.andThen k := by
  split <;> rfl

end Lift.Tactic

namespace Lift.P2.Total

/-- The next state of a result, if there is one. -/
def StepResult.next? {M : Type} : StepResult M → Option MachineState
  | .next t => some t
  | .failure _ _ => none

/-- The prior memory enters a result only in a failure: the kind of the result does not depend on it. -/
theorem Handled.shift_prior {M : Type} {policy : CpuPolicy} {visible : DataMem → M}
    {p : DataMem} {e : Effects} {r : StepResult M} (h : Handled policy visible p e r) (q : DataMem) :
    ∃ r', Handled policy visible q e r' ∧ r'.next? = r.next? := by
  induction h with
  | done s => exact ⟨_, .done s, rfl⟩
  | fault tag => exact ⟨_, .fault tag, rfl⟩
  | unaligned a b => exact ⟨_, .unaligned a b, rfl⟩
  | unsupported m => exact ⟨_, .unsupported m, rfl⟩
  | unmappedRead m a w k => exact ⟨_, .unmappedRead m a w k, rfl⟩
  | unmappedWrite m a w v k => exact ⟨_, .unmappedWrite m a w v k, rfl⟩
  | choice value _ ih => obtain ⟨r', h', e'⟩ := ih; exact ⟨r', .choice value h', e'⟩
  | readAllow access _ ih => obtain ⟨r', h', e'⟩ := ih; exact ⟨r', .readAllow access h', e'⟩
  | readDeny access => exact ⟨_, .readDeny access, rfl⟩
  | writeAllow access _ ih => obtain ⟨r', h', e'⟩ := ih; exact ⟨r', .writeAllow access h', e'⟩
  | writeDeny access => exact ⟨_, .writeDeny access, rfl⟩
  | execAllow access _ ih => obtain ⟨r', h', e'⟩ := ih; exact ⟨r', .execAllow access h', e'⟩
  | execDeny access => exact ⟨_, .execDeny access, rfl⟩

/-- A failure of `e` is a failure of `e.andThen k`. -/
theorem Handled.andThen_failure {M : Type} {policy : CpuPolicy} {visible : DataMem → M}
    {p : DataMem} {e : Effects} {r : StepResult M} (h : Handled policy visible p e r)
    (hr : r.next? = none) (k : MachineState → Effects) :
    ∃ r', Handled policy visible p (e.andThen k) r' ∧ r'.next? = none := by
  induction h with
  | done s => simp [StepResult.next?] at hr
  | fault tag => exact ⟨_, .fault tag, rfl⟩
  | unaligned a b => exact ⟨_, .unaligned a b, rfl⟩
  | unsupported m => exact ⟨_, .unsupported m, rfl⟩
  | unmappedRead m a w k' => exact ⟨_, .unmappedRead m a w _, rfl⟩
  | unmappedWrite m a w v k' => exact ⟨_, .unmappedWrite m a w v _, rfl⟩
  | choice value _ ih => obtain ⟨r', h', e'⟩ := ih hr; exact ⟨r', .choice value h', e'⟩
  | readAllow access _ ih => obtain ⟨r', h', e'⟩ := ih hr; exact ⟨r', .readAllow access h', e'⟩
  | readDeny access => exact ⟨_, .readDeny access, rfl⟩
  | writeAllow access _ ih => obtain ⟨r', h', e'⟩ := ih hr; exact ⟨r', .writeAllow access h', e'⟩
  | writeDeny access => exact ⟨_, .writeDeny access, rfl⟩
  | execAllow access _ ih => obtain ⟨r', h', e'⟩ := ih hr; exact ⟨r', .execAllow access h', e'⟩
  | execDeny access => exact ⟨_, .execDeny access, rfl⟩

/-- If `e` gives the state `t` and `k t` gives `r'` (from another prior memory), then `e.andThen k`
gives a result of the same kind as `r'`. -/
theorem Handled.andThen_next {M : Type} {policy : CpuPolicy} {visible : DataMem → M}
    {p q : DataMem} {e : Effects} {t : MachineState} (h : Handled policy visible p e (.next t))
    (k : MachineState → Effects) {r' : StepResult M} (hk : Handled policy visible q (k t) r') :
    ∃ r, Handled policy visible p (e.andThen k) r ∧ r.next? = r'.next? := by
  generalize hr : StepResult.next t = r at h
  induction h with
  | done s =>
    cases hr
    exact hk.shift_prior _
  | fault tag => cases hr
  | unaligned a b => cases hr
  | unsupported m => cases hr
  | unmappedRead m a w k' => cases hr
  | unmappedWrite m a w v k' => cases hr
  | choice value _ ih => obtain ⟨r, h', e'⟩ := ih hr; exact ⟨r, .choice value h', e'⟩
  | readAllow access _ ih => obtain ⟨r, h', e'⟩ := ih hr; exact ⟨r, .readAllow access h', e'⟩
  | readDeny access => cases hr
  | writeAllow access _ ih => obtain ⟨r, h', e'⟩ := ih hr; exact ⟨r, .writeAllow access h', e'⟩
  | writeDeny access => cases hr
  | execAllow access _ ih => obtain ⟨r, h', e'⟩ := ih hr; exact ⟨r, .execAllow access h', e'⟩
  | execDeny access => cases hr

/-- A load that `readRam` permits and that reads `v`, with any prior memory: in a run of several
steps the prior memory of the tree is the memory of the start state, not of the state of the load
(`Lift.Spike.Sites.load_iff` has `d.dmem` as the prior memory). -/
theorem Handled.load_ok_iff {M : Type} {policy : CpuPolicy} (visible : DataMem → M) (p : DataMem)
    (d : MachineData) (a : BitVec 64) (w : Width) (k : w.type → MachineData → Effects)
    (result : StepResult M) {v : w.type} (hread : readRam policy d.dmem a w = .ok v) :
    Handled policy visible p (d.load a w k) result ↔ Handled policy visible p (k v d) result := by
  unfold readRam at hread
  by_cases allow : policy.permits (.read a w) = true
  · simp only [allow, ite_true] at hread
    cases loaded : Mem.loadInt d.dmem a w.bytes with
    | none => simp [loaded] at hread
    | some value =>
      simp only [loaded, Except.ok.injEq] at hread
      subst hread
      unfold MachineData.load
      rw [Handled.read_iff _ _ _ _ _ _ _ allow]
      simp only [loaded]
  · simp [allow] at hread

/-- A store that `writeRam` permits and that gives the memory `m`, with any prior memory. -/
theorem Handled.store_ok_iff {M : Type} {policy : CpuPolicy} (visible : DataMem → M) (p : DataMem)
    (d : MachineData) (a : BitVec 64) (w : Width) (v : w.type) (k : MachineData → Effects)
    (result : StepResult M) {m : DataMem} (hwrite : writeRam policy d.dmem a w v = .ok m) :
    Handled policy visible p (d.store a v k) result ↔
      Handled policy visible p (k { d with dmem := m }) result := by
  unfold writeRam at hwrite
  by_cases allow : policy.permits (.write a w) = true
  · simp only [allow, ite_true] at hwrite
    cases loaded : Mem.loadInt d.dmem a w.bytes with
    | none => simp [loaded] at hwrite
    | some old =>
      simp only [loaded, Except.ok.injEq] at hwrite
      subst hwrite
      unfold MachineData.store
      rw [Handled.write_iff _ _ _ _ _ _ _ allow]
      simp only [loaded]
  · simp [allow] at hwrite

end Lift.P2.Total

namespace Lift.Sem

open Lift.P2.Total Lift.Tactic

/-- `n` steps from `s` reach `Q` if each result of the tree of the run is a next state in `Q`.
There is no condition on the intermediate states: `Reaches` passes each of them by one step. -/
theorem Reaches.of_runN_aux {step : MachineState → Effects} {policy : CpuPolicy}
    {Q : MachineState → Prop} (n : Nat) :
    ∀ s : MachineState,
      (∀ r, Handled policy id s.data.dmem (runN step n s) r → ∃ t, r = .next t ∧ Q t) →
      Reaches step policy Q s := by
  induction n with
  | zero =>
    intro s h
    obtain ⟨t, e, hq⟩ := h _ (.done s)
    cases e
    exact .done hq
  | succ n ih =>
    intro s h
    refine .step (fun r hr => ?_) (fun t ht => ih t fun r hr => ?_)
    · cases r with
      | next t => exact ⟨t, rfl⟩
      | failure f m =>
        obtain ⟨r', h', hn⟩ := hr.andThen_failure rfl (runN step n)
        obtain ⟨t, e, _⟩ := h r' h'
        subst e
        cases hn
    · obtain ⟨r', h', hn⟩ := ht.andThen_next (runN step n) hr
      obtain ⟨t', e, hq⟩ := h r' h'
      subst e
      cases r with
      | next t'' => cases hn; exact ⟨_, rfl, hq⟩
      | failure f m => cases hn

/-- A block row from one equation: `runN step n s = e` (proved by `simp` with the site equations),
and each result of the tree `e` is a next state in `Q`. -/
theorem Reaches.of_runN {step : MachineState → Effects} {policy : CpuPolicy}
    {Q : MachineState → Prop} {n : Nat} {s : MachineState} {e : Effects}
    (heq : runN step n s = e)
    (h : ∀ r, Handled policy id s.data.dmem e r → ∃ t, r = .next t ∧ Q t) :
    Reaches step policy Q s :=
  Reaches.of_runN_aux n s (heq ▸ h)

end Lift.Sem
