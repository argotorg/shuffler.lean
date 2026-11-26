module

public import Lift.P2.Total.Calls
public meta import Lean
public meta import Lift.P2.Total.CheckedCmd

public meta section

open Lean Elab Command

namespace Lift.P2.Total

/-- Check a proposed direct-call pattern against the supplied exact L1 step.
No assembly syntax or caller facts enter the trusted proof. -/
elab "#p2_call " step:ident " at " pc:num " next " nextPC:num
    " target " targetPC:num " as " output:ident : command =>
  withScope (fun scope => { scope with opts := scope.opts.insert `maxRecDepth (.ofNat 20000) }) do
    let effectsName := mkIdent (output.getId ++ `effects)
    let handledName := mkIdent (output.getId ++ `handled)
    let proof ← `(theorem $effectsName (data : MachineData) :
      $step ⟨data, $pc⟩ = Lift.P2.Total.Stack.callEffects data $pc $nextPC $targetPC := by
      rfl)
    let handled ← `(theorem $handledName {M : Type}
        (policy : Lift.P2.Total.CpuPolicy) (visible : DataMem → M)
        (data : MachineData) (result : Lift.P2.Total.StepResult M) :
        Lift.P2.Total.Handled policy visible data.dmem ($step ⟨data, $pc⟩) result ↔
          Lift.P2.Total.Stack.callResult policy visible data $pc $nextPC $targetPC result := by
      rw [$effectsName:ident]
      exact Lift.P2.Total.Stack.callEffects_correct _ _ _ _ _ _ _)
    generateChecked #[proof, handled] #[((← getCurrNamespace) ++ output.getId ++ `handled)]

elab "#p2_return " step:ident " at " pc:num " next " nextPC:num
    " as " output:ident : command =>
  withScope (fun scope => { scope with opts := scope.opts.insert `maxRecDepth (.ofNat 20000) }) do
    let effectsName := mkIdent (output.getId ++ `effects)
    let handledName := mkIdent (output.getId ++ `handled)
    let proof ← `(theorem $effectsName (data : MachineData) :
      $step ⟨data, $pc⟩ = Lift.P2.Total.Stack.returnEffects data $pc $nextPC := by
      rfl)
    let handled ← `(theorem $handledName {M : Type}
        (policy : Lift.P2.Total.CpuPolicy) (visible : DataMem → M)
        (data : MachineData) (result : Lift.P2.Total.StepResult M) :
        Lift.P2.Total.Handled policy visible data.dmem ($step ⟨data, $pc⟩) result ↔
          Lift.P2.Total.Stack.returnResult policy visible data $pc $nextPC result := by
      rw [$effectsName:ident]
      exact Lift.P2.Total.Stack.returnEffects_correct _ _ _ _ _ _)
    generateChecked #[proof, handled] #[((← getCurrNamespace) ++ output.getId ++ `handled)]

end Lift.P2.Total
