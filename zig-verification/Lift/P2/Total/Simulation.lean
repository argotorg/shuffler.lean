module

public import Lift.P2.Total.Spec
public import Lift.P2.Total.Ranked

@[expose] public section

namespace Lift.P2.Total

/-- The two directions use one state relation and separate progress ranks. -/
structure Coupling {A B O : Type} (x : System A O) (y : System B O) where
  relation : A → B → Prop
  forwardRank : A → B → Nat
  backwardRank : B → A → Nat
  forward : RankedSimulation x y relation forwardRank
  backward : RankedSimulation y x (fun b a => relation a b) backwardRank

def Coupling.ofLeftEq {A B O : Type} {x x2 : System A O} {y : System B O}
    (equal : x = x2) (coupling : Coupling x2 y) : Coupling x y where
  relation := coupling.relation
  forwardRank := coupling.forwardRank
  backwardRank := coupling.backwardRank
  forward := by cases equal; exact coupling.forward
  backward := by cases equal; exact coupling.backward

theorem Coupling.equivalent {A B O : Type} {x : System A O} {y : System B O}
    (coupling : Coupling x y) {a : A} {b : B} (entry : coupling.relation a b) :
    Equivalent x y a b :=
  fun behavior => ⟨coupling.forward.behaves entry behavior, coupling.backward.behaves entry behavior⟩

theorem P2Spec.of_coupling {A V M : Type} (asm : _root_.Executable) (policy : CpuPolicy)
    (boundary : Boundary V M) (contract : MachineState → Prop) (model : Model A V M)
    (coupling : ∀ initial, contract initial → Coupling (source asm policy boundary initial) model.system)
    (entry : ∀ initial valid, (coupling initial valid).relation initial (model.entry initial)) :
    P2Spec asm policy boundary contract model :=
  fun initial valid => (coupling initial valid).equivalent (entry initial valid)

theorem CallSpec.of_coupling {A V M : Type} (asm : _root_.Executable) (policy : CpuPolicy)
    (boundary : Boundary V M) (contract : MachineState → Prop) (model : Model A V M)
    (coupling : ∀ initial, contract initial → Coupling (source asm policy boundary initial) model.system)
    (entry : ∀ initial valid, (coupling initial valid).relation initial (model.entry initial))
    (exit : ∀ initial valid final a value,
      (coupling initial valid).relation final a →
      boundary.returned initial final = some value → AbiRestored initial final) :
    CallSpec asm policy boundary contract model := by
  refine ⟨P2Spec.of_coupling asm policy boundary contract model coupling entry, ?_⟩
  intro initial valid final value path returned
  obtain ⟨a, _, related⟩ := (coupling initial valid).forward.reaches (entry initial valid) path
  exact exit initial valid final a value related returned

end Lift.P2.Total
