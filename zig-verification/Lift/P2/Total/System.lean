module

public import Init.Classical

@[expose] public section

namespace Lift.P2.Total

/-- Internal transitions and observable terminal outcomes. Choices are relations. -/
structure System (S O : Type) where
  step : S → S → Prop
  stop : S → O → Prop

inductive Behavior (O : Type) where
  | finish (outcome : O)
  | diverge

namespace System

inductive Reaches {S O : Type} (m : System S O) : S → S → Prop
  | refl (s : S) : Reaches m s s
  | tail {s t u : S} (path : Reaches m s t) (edge : m.step t u) : Reaches m s u

/-- A real infinite execution, not failure to find a return within some fuel. -/
def Diverges {S O : Type} (m : System S O) (s : S) : Prop :=
  ∃ trace : Nat → S, trace 0 = s ∧ ∀ n, m.step (trace n) (trace (n + 1))

def Behaves {S O : Type} (m : System S O) (s : S) : Behavior O → Prop
  | .finish out => ∃ t, m.Reaches s t ∧ m.stop t out
  | .diverge => m.Diverges s

end System

def Equivalent {A B O : Type} (x : System A O) (y : System B O) (a : A) (b : B) : Prop :=
  ∀ behavior, x.Behaves a behavior ↔ y.Behaves b behavior

/-- A progress-preserving one-step simulation. No source step can disappear. -/
structure Simulation {A B O : Type} (x : System A O) (y : System B O)
    (r : A → B → Prop) : Prop where
  stop : ∀ {a b out}, r a b → x.stop a out → y.stop b out
  step : ∀ {a a' b}, r a b → x.step a a' → ∃ b', y.step b b' ∧ r a' b'

theorem Simulation.reaches {A B O : Type} {x : System A O} {y : System B O}
    {r : A → B → Prop} (sim : Simulation x y r) {a a' : A} {b : B}
    (hr : r a b) (path : x.Reaches a a') : ∃ b', y.Reaches b b' ∧ r a' b' := by
  induction path with
  | refl => exact ⟨b, .refl b, hr⟩
  | tail path edge ih =>
    obtain ⟨t, ht, hrt⟩ := ih
    obtain ⟨u, hu, hru⟩ := sim.step hrt edge
    exact ⟨u, .tail ht hu, hru⟩

theorem Simulation.diverges {A B O : Type} {x : System A O} {y : System B O}
    {r : A → B → Prop} (sim : Simulation x y r) {a : A} {b : B}
    (hr : r a b) (div : x.Diverges a) : y.Diverges b := by
  classical
  obtain ⟨trace, start, next⟩ := div
  have initial : r (trace 0) b := start ▸ hr
  let matched : (n : Nat) → { t : B // r (trace n) t } :=
    Nat.rec ⟨b, initial⟩ (fun n prev =>
      ⟨Classical.choose (sim.step prev.property (next n)),
       (Classical.choose_spec (sim.step prev.property (next n))).2⟩)
  refine ⟨fun n => (matched n).val, rfl, fun n => ?_⟩
  exact (Classical.choose_spec (sim.step (matched n).property (next n))).1

theorem Simulation.behaves {A B O : Type} {x : System A O} {y : System B O}
    {r : A → B → Prop} (sim : Simulation x y r) {a : A} {b : B}
    (hr : r a b) (behavior : Behavior O) : x.Behaves a behavior → y.Behaves b behavior := by
  cases behavior with
  | finish out =>
    rintro ⟨t, path, stop⟩
    obtain ⟨u, target, related⟩ := sim.reaches hr path
    exact ⟨u, target, sim.stop related stop⟩
  | diverge => exact sim.diverges hr

structure Bisimulation {A B O : Type} (x : System A O) (y : System B O)
    (r : A → B → Prop) : Prop where
  forward : Simulation x y r
  backward : Simulation y x (fun b a => r a b)

theorem Bisimulation.equivalent {A B O : Type} {x : System A O} {y : System B O}
    {r : A → B → Prop} (sim : Bisimulation x y r) {a : A} {b : B}
    (hr : r a b) : Equivalent x y a b :=
  fun behavior => ⟨sim.forward.behaves hr behavior, sim.backward.behaves hr behavior⟩

end Lift.P2.Total
