module

public import Lift.P2.Total.BlockFinite

@[expose] public section

namespace Lift.P2.Total

/-- A finite prefix has one successor at each step and no terminal outcome
before its endpoint. A proposed endpoint cannot remove a choice or fault. -/
def PurePrefix {S O : Type} (m : System S O) : Nat → S → S → Prop
  | 0, source, target => source = target
  | depth + 1, source, target => ∃ next,
      m.step source next ∧
      (∀ other, m.step source other → other = next) ∧
      (∀ out, ¬ m.stop source out) ∧ PurePrefix m depth next target

theorem System.equivalent_next {S O : Type} (m : System S O) (s t : S)
    (edge : m.step s t) (only : ∀ other, m.step s other → other = t)
    (noStop : ∀ out, ¬ m.stop s out) : Equivalent m m s t := by
  intro behavior
  cases behavior with
  | finish out =>
    constructor
    · rintro ⟨last, path, terminal⟩
      rcases path.head with equal | ⟨next, first, rest⟩
      · subst last
        exact (noStop out terminal).elim
      · obtain rfl := only next first
        exact ⟨last, rest, terminal⟩
    · rintro ⟨last, path, terminal⟩
      exact ⟨last, (System.Reaches.tail (.refl _) edge).trans path, terminal⟩
  | diverge =>
    constructor
    · rintro ⟨trace, start, steps⟩
      refine ⟨fun n => trace (n + 1), ?_, fun n => steps (n + 1)⟩
      apply only
      simpa only [start] using steps 0
    · rintro ⟨trace, start, steps⟩
      refine ⟨fun n => match n with | 0 => s | n + 1 => trace n, rfl, ?_⟩
      intro n
      cases n with
      | zero => simpa only [start] using edge
      | succ n => exact steps n

theorem PurePrefix.equivalent {S O : Type} {m : System S O} {n : Nat} {s t : S}
    (hprefix : PurePrefix m n s t) : Equivalent m m s t := by
  induction n generalizing s with
  | zero =>
    change s = t at hprefix
    subst t
    exact fun _ => Iff.rfl
  | succ n ih =>
    obtain ⟨next, edge, only, noStop, rest⟩ := hprefix
    intro behavior
    exact (m.equivalent_next s next edge only noStop behavior).trans (ih rest behavior)

/-- The relation starts after a checked pure target prefix. The public model
retains its original entry state and its full transition system. -/
theorem CallSpec.of_blocks_at_returns_prefix {A V M : Type} (asm : _root_.Executable)
    (step : MachineState → Effects) (exact : Lift.P1.L1Spec asm step)
    (policy : CpuPolicy) (boundary : Boundary V M) (contract : MachineState → Prop)
    (model : Model A V M) (cutSource : MachineState → MachineState → Prop)
    (cutTarget : MachineState → A → Prop)
    (relation : MachineState → MachineState → A → Prop)
    (entryTarget : MachineState → A) (entryDepth : Nat)
    (certificate : ∀ initial, contract initial →
      BlockMatch (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
        model.system (cutSource initial) (cutTarget initial) (relation initial))
    (hprefix : ∀ initial, contract initial →
      PurePrefix model.system entryDepth (model.entry initial) (entryTarget initial))
    (entry : ∀ initial, contract initial → relation initial initial (entryTarget initial))
    (returnCut : ∀ initial, contract initial → ∀ final value,
      boundary.returned initial final = some value → cutSource initial final)
    (exit : ∀ initial, contract initial → ∀ final a value,
      relation initial final a →
      boundary.returned initial final = some value → AbiRestored initial final) :
    CallSpec asm policy boundary contract model := by
  refine ⟨?_, ?_⟩
  · apply P2Spec.of_L1 asm step exact policy boundary contract model
    intro initial valid behavior
    exact ((certificate initial valid).equivalent (entry initial valid) behavior).trans
      ((hprefix initial valid).equivalent behavior).symm
  · intro initial valid final value path returned
    have path' : (cpuSystem step policy (boundary.returned initial)
        (boundary.visible initial)).Reaches initial final := by
      rw [cpuSystem_of_L1Spec asm step exact]
      exact path
    obtain ⟨a, _, root, related, interior⟩ :=
      (certificate initial valid).forward_simulation.reaches
        ⟨initial, entry initial valid, .refl _⟩ path'
    have equal := interior.eq_of_cut (returnCut initial valid final value returned)
    subst root
    exact exit initial valid final a value related returned

end Lift.P2.Total
