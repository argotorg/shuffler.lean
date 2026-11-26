module

public import Lift.P2.Total.Calls

@[expose] public section

namespace Lift.P2.Total

/-- Add an outer typed continuation without changing any local computation. -/
def Continuation.extend {F : Type} {program : Program F} {root outer : F}
    (context : Continuation program outer root) {f : F} :
    Continuation program root f → Continuation program outer f
  | .root => context
  | .call resume rest => .call resume (Continuation.extend context rest)

def Continuation.finish {F : Type} {program : Program F} {root outer : F}
    (context : Continuation program outer root) (value : program.result root)
    (memory : DataMem) : Config program outer :=
  match context with
  | .root => .returned value memory
  | .call resume rest => .running _ (resume value memory) rest

def Config.inContext {F : Type} {program : Program F} {root outer : F}
    (context : Continuation program outer root) : Config program root → Config program outer
  | .running f state k => .running f state (Continuation.extend context k)
  | .returned value memory => context.finish value memory
  | .failed reason memory => .failed reason memory

/-- Each leaf step is still one step under an outer continuation, including
the step that supplies the leaf result to its caller. -/
theorem Transition.inContext {F : Type} {program : Program F} {root outer : F}
    {s t : Config program root} (edge : Transition program s t)
    (context : Continuation program outer root) :
    Transition program (s.inContext context) (t.inContext context) := by
  cases edge with
  | next body => exact .next body
  | call body => exact .call body
  | returned body =>
    cases context with
    | root => exact .returned body
    | call resume rest => exact .resume body
  | resume body => exact .resume body
  | failed body => exact .failed body
  | choose body value => exact .choose body value

/-- Before the leaf returns, every outer step is also a leaf step.
The result and fault cases are preserved; no termination bound is used. -/
theorem transition_context_iff {F : Type} (program : Program F) {root outer f : F}
    (state : program.locals f) (k : Continuation program root f)
    (context : Continuation program outer root) (target : Config program outer) :
    Transition program ((Config.running f state k).inContext context) target ↔
      ∃ next : Config program root,
        Transition program (.running f state k) next ∧ next.inContext context = target := by
  cases body : program.body f state with
  | next next =>
    simp [Config.inContext, transition_iff_successors, successors, body, eq_comm]
  | call callee args memory resume =>
    simp [Config.inContext, transition_iff_successors, successors, body, eq_comm,
      Continuation.extend]
  | returned value memory =>
    cases k with
    | root =>
      cases context <;>
        simp [Config.inContext, transition_iff_successors, successors, body, eq_comm,
          Continuation.extend, Continuation.finish]
    | call resume rest =>
      simp [Config.inContext, transition_iff_successors, successors, body, eq_comm,
        Continuation.extend]
  | failed reason memory =>
    simp [Config.inContext, transition_iff_successors, successors, body, eq_comm]
  | choose resume =>
    simp only [Config.inContext, transition_iff_successors, successors, body]
    constructor
    · rintro ⟨value, rfl⟩
      exact ⟨_, ⟨value, rfl⟩, rfl⟩
    · rintro ⟨next, ⟨value, rfl⟩, rfl⟩
      exact ⟨value, rfl⟩

/-- Actual infinite leaf traces remain infinite in their caller context. -/
theorem divergence_inContext {F : Type} (program : Program F) {root outer : F}
    (context : Continuation program outer root) (state : Config program root)
    (diverges : (program.system root).Diverges state) :
    (program.system outer).Diverges (state.inContext context) := by
  obtain ⟨trace, start, edges⟩ := diverges
  refine ⟨fun n => (trace n).inContext context, ?_, ?_⟩
  · exact congrArg (Config.inContext context) start
  · intro n
    exact (edges n).inContext context

end Lift.P2.Total
