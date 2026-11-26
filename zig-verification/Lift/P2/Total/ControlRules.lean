module

public import Lift.P2.Total.Control

@[expose] public section

namespace Lift.P2.Total

/-- Observe one control edge without copying the full system into a bounded path. -/
theorem program_step_nf {F : Type} (program : Program F) (root : F) (s t : Config program root) :
    (program.system root).step s t ↔ Transition program s t := Iff.rfl

theorem program_stop_nf {F : Type} (program : Program F) (root : F) (s : Config program root)
    (out : Outcome (program.result root) DataMem) :
    (program.system root).stop s out ↔ match s with
      | .running _ _ _ => False
      | .returned value memory => out = .returned value memory
      | .failed reason memory => out = .failure reason memory := Iff.rfl

def successors {F : Type} (program : Program F) {root : F} (f : F)
    (state : program.locals f) (k : Continuation program root f)
    (target : Config program root) : Prop :=
  match program.body f state with
  | .next next => target = .running f next k
  | .call callee args memory resume =>
      target = .running callee (program.enter callee args memory) (.call resume k)
  | .returned value memory => match k with
      | .root => target = .returned value memory
      | .call resume rest => target = .running _ (resume value memory) rest
  | .failed reason memory => target = .failed reason memory
  | @Command.choose _ _ _ _ _ A _ resume => ∃ value : A, target = .running f (resume value) k

theorem transition_iff_successors {F : Type} (program : Program F) {root : F}
    (f : F) (state : program.locals f) (k : Continuation program root f)
    (target : Config program root) :
    Transition program (.running f state k) target ↔ successors program f state k target := by
  constructor
  · intro edge
    cases edge with
    | next body => simp only [successors, body]
    | call body => simp only [successors, body]
    | returned body => simp only [successors, body]
    | resume body => simp only [successors, body]
    | failed body => simp only [successors, body]
    | choose body value =>
      simp only [successors, body]
      exact ⟨value, rfl⟩
  · intro h
    cases body : program.body f state with
    | next next =>
      simp only [successors, body] at h
      subst target
      exact .next body
    | call callee args memory resume =>
      simp only [successors, body] at h
      subst target
      exact .call body
    | returned value memory =>
      cases k with
      | root =>
        simp only [successors, body] at h
        subst target
        exact .returned body
      | call resume rest =>
        simp only [successors, body] at h
        subst target
        exact .resume body
    | failed reason memory =>
      simp only [successors, body] at h
      subst target
      exact .failed body
    | choose resume =>
      simp only [successors, body] at h
      obtain ⟨value, rfl⟩ := h
      exact .choose body value

theorem transition_returned {F : Type} (program : Program F) {root : F}
    (value : program.result root) (memory : DataMem) (target : Config program root) :
    ¬ Transition program (.returned value memory) target := by
  intro h; cases h

theorem transition_failed {F : Type} (program : Program F) {root : F}
    (reason : Failure) (memory : DataMem) (target : Config program root) :
    ¬ Transition program (.failed reason memory) target := by
  intro h; cases h

end Lift.P2.Total
