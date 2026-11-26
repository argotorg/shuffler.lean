module

public import Lift.P2.Total.Unroll

@[expose] public section

namespace Lift.P2.Total

/-- A finite function needs local expansion certificates on both sides and a
check of the ABI at every visited return. Bounds occur only in the certificate. -/
theorem CallSpec.of_finite {A V M : Type} (asm : _root_.Executable)
    (step : MachineState → Effects) (exact : Lift.P1.L1Spec asm step)
    (policy : CpuPolicy) (boundary : Boundary V M) (contract : MachineState → Prop)
    (model : Model A V M) (sourceDepth targetDepth : Nat)
    (leftClosed : ∀ initial, contract initial → ∀ t,
      ¬ unroll (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
        sourceDepth initial (.pending t))
    (rightClosed : ∀ initial, contract initial → ∀ t,
      ¬ unroll model.system targetDepth (model.entry initial) (.pending t))
    (summary : ∀ initial, contract initial → ∀ out,
      unroll (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
          sourceDepth initial (.finished out) ↔
        unroll model.system targetDepth (model.entry initial) (.finished out))
    (exit : ∀ initial, contract initial → ∀ final value,
      visits (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
        sourceDepth initial final →
      boundary.returned initial final = some value → AbiRestored initial final) :
    CallSpec asm policy boundary contract model := by
  constructor
  · apply P2Spec.of_L1 asm step exact policy boundary contract model
    intro initial valid
    exact equivalent_of_unroll _ _ sourceDepth targetDepth _ _
      (leftClosed initial valid) (rightClosed initial valid) (summary initial valid)
  · intro initial valid final value path returned
    have path' : (cpuSystem step policy (boundary.returned initial)
        (boundary.visible initial)).Reaches initial final := by
      rw [cpuSystem_of_L1Spec asm step exact]
      exact path
    exact exit initial valid final value
      (reaches_visits _ _ initial (leftClosed initial valid) path') returned

end Lift.P2.Total
