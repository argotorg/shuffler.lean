module

public import Lift.P2.Total.Block
public import Lift.P2.Total.Spec

@[expose] public section

namespace Lift.P2.Total

/-- Move a local choice before its exact successor state. This does not
enumerate choices whose values do not affect the next block relation. -/
theorem exists_choice_state {A B : Type} (state : B → A) (predicate : A → Prop) :
    (∃ value, (∃ choice, value = state choice) ∧ predicate value) ↔
      ∃ choice, predicate (state choice) := by
  constructor
  · rintro ⟨_, ⟨choice, rfl⟩, h⟩; exact ⟨choice, h⟩
  · rintro ⟨choice, h⟩; exact ⟨state choice, ⟨choice, rfl⟩, h⟩

/-- Finite expansion checks one block at a time. Pending states must be
excluded before the finite certificate can prove anything about the model. -/
theorem BlockMatch.of_unroll {A B O : Type} (x : System A O) (y : System B O)
    (cutX : A → Prop) (cutY : B → Prop) (relation : A → B → Prop)
    (leftDepth : A → Nat) (rightDepth : B → Nat)
    (cuts : ∀ a b, relation a b → cutX a ∧ cutY b)
    (leftClosed : ∀ a b, relation a b → BlockClosed x cutX (leftDepth a) a)
    (rightClosed : ∀ a b, relation a b → BlockClosed y cutY (rightDepth b) b)
    (forward : ∀ a b next, relation a b →
      unroll (blockSystem x cutX) (leftDepth a) a (.finished (.next next)) →
      ∃ target, unroll (blockSystem y cutY) (rightDepth b) b (.finished (.next target)) ∧
        relation next target)
    (backward : ∀ a b next, relation a b →
      unroll (blockSystem y cutY) (rightDepth b) b (.finished (.next next)) →
      ∃ target, unroll (blockSystem x cutX) (leftDepth a) a (.finished (.next target)) ∧
        relation target next)
    (terminal : ∀ a b out, relation a b →
      (unroll (blockSystem x cutX) (leftDepth a) a (.finished (.finished out)) ↔
        unroll (blockSystem y cutY) (rightDepth b) b (.finished (.finished out)))) :
    BlockMatch x y cutX cutY relation := by
  refine ⟨fun h => cuts _ _ h, fun h => ⟨_, leftClosed _ _ h⟩,
    fun h => ⟨_, rightClosed _ _ h⟩, ?_, ?_, ?_⟩
  · intro a b next related path
    have expanded := unroll_finished_complete (blockSystem x cutX) (leftDepth a) a
      (leftClosed a b related) (.next next) path
    obtain ⟨target, matched, targetRelated⟩ := forward a b next related expanded
    exact ⟨target, unroll_finished_sound _ _ _ _ matched, targetRelated⟩
  · intro a b next related path
    have expanded := unroll_finished_complete (blockSystem y cutY) (rightDepth b) b
      (rightClosed a b related) (.next next) path
    obtain ⟨target, matched, targetRelated⟩ := backward a b next related expanded
    exact ⟨target, unroll_finished_sound _ _ _ _ matched, targetRelated⟩
  · intro a b out related
    constructor
    · intro path
      have expanded := unroll_finished_complete (blockSystem x cutX) (leftDepth a) a
        (leftClosed a b related) (.finished out) path
      exact unroll_finished_sound _ _ _ _ ((terminal a b out related).mp expanded)
    · intro path
      have expanded := unroll_finished_complete (blockSystem y cutY) (rightDepth b) b
        (rightClosed a b related) (.finished out) path
      exact unroll_finished_sound _ _ _ _ ((terminal a b out related).mpr expanded)

/-- The exact P1 theorem enters only here. Local block checks can use the
shallow step function; the result states behavior equality for the assembly. -/
theorem P2Spec.of_blocks {A V M : Type} (asm : _root_.Executable)
    (step : MachineState → Effects) (exact : Lift.P1.L1Spec asm step)
    (policy : CpuPolicy) (boundary : Boundary V M) (contract : MachineState → Prop)
    (model : Model A V M) (cutSource : MachineState → MachineState → Prop)
    (cutTarget : MachineState → A → Prop)
    (relation : MachineState → MachineState → A → Prop)
    (certificate : ∀ initial, contract initial →
      BlockMatch (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
        model.system (cutSource initial) (cutTarget initial) (relation initial))
    (entry : ∀ initial, contract initial → relation initial initial (model.entry initial)) :
    P2Spec asm policy boundary contract model := by
  apply P2Spec.of_L1 asm step exact policy boundary contract model
  intro initial valid
  exact (certificate initial valid).equivalent (entry initial valid)

/-- The ABI check includes any returned state inside a block. A generator can
choose every return boundary as a cut to make this check use only cut states. -/
theorem CallSpec.of_blocks {A V M : Type} (asm : _root_.Executable)
    (step : MachineState → Effects) (exact : Lift.P1.L1Spec asm step)
    (policy : CpuPolicy) (boundary : Boundary V M) (contract : MachineState → Prop)
    (model : Model A V M) (cutSource : MachineState → MachineState → Prop)
    (cutTarget : MachineState → A → Prop)
    (relation : MachineState → MachineState → A → Prop)
    (certificate : ∀ initial, contract initial →
      BlockMatch (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
        model.system (cutSource initial) (cutTarget initial) (relation initial))
    (entry : ∀ initial, contract initial → relation initial initial (model.entry initial))
    (exit : ∀ initial, contract initial → ∀ root a final value,
      relation initial root a →
      InteriorPath (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
        (cutSource initial) root final →
      boundary.returned initial final = some value → AbiRestored initial final) :
    CallSpec asm policy boundary contract model := by
  refine ⟨P2Spec.of_blocks asm step exact policy boundary contract model
    cutSource cutTarget relation certificate entry, ?_⟩
  intro initial valid final value path returned
  have path' : (cpuSystem step policy (boundary.returned initial)
      (boundary.visible initial)).Reaches initial final := by
    rw [cpuSystem_of_L1Spec asm step exact]
    exact path
  obtain ⟨a, _, root, related, interior⟩ :=
    (certificate initial valid).forward_simulation.reaches
      ⟨initial, entry initial valid, .refl _⟩ path'
  exact exit initial valid root a final value related interior returned

theorem InteriorPath.eq_of_cut {S O : Type} {m : System S O} {cut : S → Prop}
    {s t : S} (path : InteriorPath m cut s t) (target : cut t) : s = t := by
  cases path with
  | refl => rfl
  | tail _ _ interior => exact (interior target).elim

/-- When return boundaries are cuts, the ABI law only needs the relation at a
cut. The local path cannot cross another cut before it ends. -/
theorem CallSpec.of_blocks_at_returns {A V M : Type} (asm : _root_.Executable)
    (step : MachineState → Effects) (exact : Lift.P1.L1Spec asm step)
    (policy : CpuPolicy) (boundary : Boundary V M) (contract : MachineState → Prop)
    (model : Model A V M) (cutSource : MachineState → MachineState → Prop)
    (cutTarget : MachineState → A → Prop)
    (relation : MachineState → MachineState → A → Prop)
    (certificate : ∀ initial, contract initial →
      BlockMatch (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
        model.system (cutSource initial) (cutTarget initial) (relation initial))
    (entry : ∀ initial, contract initial → relation initial initial (model.entry initial))
    (returnCut : ∀ initial, contract initial → ∀ final value,
      boundary.returned initial final = some value → cutSource initial final)
    (exit : ∀ initial, contract initial → ∀ final a value,
      relation initial final a →
      boundary.returned initial final = some value → AbiRestored initial final) :
    CallSpec asm policy boundary contract model := by
  apply CallSpec.of_blocks asm step exact policy boundary contract model
    cutSource cutTarget relation certificate entry
  intro initial valid root a final value related path returned
  have equal := path.eq_of_cut (returnCut initial valid final value returned)
  subst root
  exact exit initial valid final a value related returned

end Lift.P2.Total
