import Shuffler.BuildBottomUp.Lemmas.Termination

open Std.Internal.Do

namespace Shuffler.BuildBottomUp

/-- No infinite chain of continuing steps starts at `((none, 0), state)`.
Runtime termination also requires each body call to finish; see README.md.
Errors count as exits. Exclusion of assertion errors is proved separately below. -/
theorem buildBottomUp_terminates (state : State source target spills)
    (inv : Invariant 0 state) :
    Acc (Continues (loopBody source target spills).val) ((none, 0), state) :=
  Lemmas.loop_terminates 0 state inv

/-- Only allowed errors can be returned. This claim does not establish runtime termination. -/
theorem buildBottomUp_triple (state : State source target spills)
    (inv : Invariant 0 state) :
    ⦃True⦄ buildBottomUp state ⦃fun _ => True; allowedErrors⦄ := by
  rw [(loopBody source target spills).property state]
  apply (spec_iff_triple _ _).mp
  have h := (build_action_triple (source := source) (target := target) (spills := spills) 0).le_wp state inv
  have hs := (spec_iff_triple _ _).mpr (Triple.intro (fun (_ : True) => h))
  rw [StateT.run'_eq]
  exact hs.bind (fun _ _ => trivial)

/-- Under the input invariant, no returned error is an assertion error. -/
theorem buildBottomUp_noAssertion (state : State source target spills)
    (inv : Invariant 0 state) (reason : String) :
    buildBottomUp state ≠ .error (.assertion reason) := by
  exact ((spec_iff_triple _ _).mpr (buildBottomUp_triple state inv)).noAssertion reason

/-- Expose the body without the equality proof, which refers to the outer loop.
The equality below checks that this is the actual body. -/
def bodyForTerminationCheck (source target : Stack) (spills : SpillSet) :
    Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills)) := by
  run_tac
    let args ← #[`source, `target, `spills].mapM fun name => do
      return (← Lean.Meta.getLocalDeclFromUserName name).toExpr
    let extracted ← Lean.Meta.mkAppM ``loopBody args
    let value ← Lean.Meta.mkAppM ``Subtype.val #[extracted]
    let value ← Lean.Meta.whnf value
    Lean.Elab.Tactic.closeMainGoal `bodyForTerminationCheck value

example (source target : Stack) (spills : SpillSet) :
    bodyForTerminationCheck source target spills = (loopBody source target spills).val := rfl

-- All other dependencies use Lean's checked definitions. String append is a runtime primitive.
-- This audits logical definitions, not compiler replacements or the runtime itself.
-- It cannot inspect function values supplied in the input, such as mapping lookups.
/-- info: 'Shuffler.BuildBottomUp.bodyForTerminationCheck' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques bodyForTerminationCheck

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_terminates

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_triple

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_noAssertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_noAssertion

end Shuffler.BuildBottomUp
