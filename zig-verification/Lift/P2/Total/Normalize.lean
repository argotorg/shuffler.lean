module

public import Lift.P2.Total.Finite
public import Lift.P2.Total.Primitive
public import Lift.P2.Total.WordRules
public import Lift.P2.Total.GuardedFootprint
public import Lift.P2.Total.ConditionalFootprint
public meta import Lean
public meta import Lift.P1.Command

@[expose] public section

namespace Lift.P2.Total

theorem Handled.exec_all_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (p : Std.Rco Int64) (k : Unit → Effects) (result : StepResult M) :
    Handled policy visible prior (.require_exec_access p k) result ↔
      if policy.permits (.execute p.lower p.upper) then
        Handled policy visible prior (k ()) result
      else result = .failure (.denied (.execute p.lower p.upper)) (visible prior) := by
  cases allow : policy.permits (.execute p.lower p.upper) with
  | true => simp only [↓reduceIte]; exact Handled.exec_iff _ _ _ _ _ _ allow
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h
      cases h with
      | execAllow allowed _ => simp [allow] at allowed
      | execDeny _ => rfl
    · intro h; subst result; exact .execDeny allow

theorem Handled.load_normalize {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (data : MachineData) (address : BitVec 64) (width : Width)
    (k : width.type → MachineData → Effects) (result : StepResult M)
    (same : prior = data.dmem) :
    Handled policy visible prior (data.load address width k) result ↔
      match readRam policy data.dmem address width with
      | .ok value => Handled policy visible data.dmem (k value data) result
      | .error (reason, memory) => result = .failure reason (visible memory) := by
  rw [same, readRam_correct]
  rfl

theorem Handled.store_normalize {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (data : MachineData) (address : BitVec 64) (width : Width)
    (value : width.type) (k : MachineData → Effects) (result : StepResult M)
    (same : prior = data.dmem) :
    Handled policy visible prior (data.store address value k) result ↔
      match writeRam policy data.dmem address width value with
      | .ok memory => Handled policy visible data.dmem (k { data with dmem := memory }) result
      | .error (reason, memory) => result = .failure reason (visible memory) := by
  rw [same, writeRam_correct]
  rfl

theorem int64_eq_comm (a b : Int64) : (a = b) ↔ (b = a) := eq_comm

theorem exists_unit_iff (predicate : Unit → Prop) :
    (∃ value, predicate value) ↔ predicate () := by
  constructor
  · rintro ⟨⟨⟩, proof⟩; exact proof
  · intro proof; exact ⟨(), proof⟩

@[simp] theorem addressSize64 (value : BitVec 64) :
    @BitVec.toAddressSize ⟨.W64⟩ value = value := by
  simp [BitVec.toAddressSize, BitVec.take, Width.bits]

@[simp] theorem bitVec_drop_zero (width : Nat) (value : BitVec width) :
    value.drop 0 = value := by
  simp [BitVec.drop]

@[simp] theorem bitVec_take_self (width : Nat) (value : BitVec width) :
    value.take width = value := by
  simp [BitVec.take]

@[simp] theorem ofInt_signed64 (value : BitVec 64) :
    BitVec.ofInt 64 value.signed = value := by
  simp [BitVec.signed]

/-- A mapped and permitted read is exact. Other reads remain available for case splitting. -/
theorem readRam_mapped (policy : CpuPolicy) (memory : DataMem) (address : BitVec 64)
    (width : Width) (value : Int)
    (allowed : policy.permits (.read address width) = true)
    (mapped : Mem.loadInt memory address width.bytes = some value) :
    readRam policy memory address width = .ok (BitVec.ofInt width.bits value) := by
  simp only [readRam, allowed, ↓reduceIte, mapped]

/-- A successful write has this exact memory, so later access rules can use its bytes. -/
theorem writeRam_memory (policy : CpuPolicy) (memory memory' : DataMem)
    (address : BitVec 64) (width : Width) (value : width.type)
    (stored : writeRam policy memory address width value = .ok memory') :
    memory' = Mem.storeInt memory address width.bytes value.toInt := by
  unfold writeRam at stored
  split at stored
  · split at stored
    · exact (Except.ok.inj stored).symm
    · cases stored
  · cases stored

/-- System projections expose one observed edge without unfolding the system under unroll. -/
theorem cpu_step_nf {V M : Type} (machineStep : MachineState → Effects) (policy : CpuPolicy)
    (returned : MachineState → Option V) (visible : DataMem → M) (s t : MachineState) :
    (cpuSystem machineStep policy returned visible).step s t ↔
      returned s = none ∧ Handled policy visible s.data.dmem (machineStep s) (.next t) := Iff.rfl

theorem cpu_stop_nf {V M : Type} (machineStep : MachineState → Effects) (policy : CpuPolicy)
    (returned : MachineState → Option V) (visible : DataMem → M) (s : MachineState) (out : Outcome V M) :
    (cpuSystem machineStep policy returned visible).stop s out ↔
      (∃ value, returned s = some value ∧ out = .returned value (visible s.data.dmem)) ∨
      (returned s = none ∧ ∃ reason mem,
        Handled policy visible s.data.dmem (machineStep s) (.failure reason mem) ∧ out = .failure reason mem) := Iff.rfl

/-- Move a machine choice outside its edge continuation before substituting the next state. -/
theorem exists_choice_relation {A B : Type} (relation : A → B → Prop) (predicate : A → Prop) :
    (∃ value, (∃ choice, relation value choice) ∧ predicate value) ↔
      ∃ choice value, relation value choice ∧ predicate value := by
  constructor
  · rintro ⟨value, ⟨choice, related⟩, h⟩
    exact ⟨choice, value, related, h⟩
  · rintro ⟨choice, value, related, h⟩
    exact ⟨value, ⟨choice, related⟩, h⟩

theorem exists_choice_state {A B : Type} (state : B → A) (predicate : A → Prop) :
    (∃ value, (∃ choice, value = state choice) ∧ predicate value) ↔
      ∃ choice, predicate (state choice) := by
  constructor
  · rintro ⟨_, ⟨choice, rfl⟩, h⟩
    exact ⟨choice, h⟩
  · rintro ⟨choice, h⟩
    exact ⟨state choice, ⟨choice, rfl⟩, h⟩

end Lift.P2.Total

public meta section

open Lean Elab Command Meta

namespace Lift.P2.Total

/-- Derive a shallow site equation from exact L1. No compiler fact is an axiom. -/
elab "#p2_step_eq " step:ident " at " pc:num " as " output:ident : command =>
  withScope (fun scope => { scope with opts := scope.opts.insert `maxRecDepth (.ofNat 20000) }) do
  let stepName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo step
  let outputName := (← getCurrNamespace) ++ output.getId
  let (statement, proof) ← liftTermElabM do
    let address ← Term.elabTerm pc.raw (some (mkConst ``Int64))
    withLocalDeclD `data (mkConst ``MachineData) fun data => do
      let state ← mkAppM ``MachineState.mk #[data, address]
      let lhs := mkApp (mkConst stepName) state
      let rhs ← withTransparency .all <| whnf lhs
      let statement ← mkForallFVars #[data] (← mkEq lhs rhs)
      let proof ← mkLambdaFVars #[data] (← mkEqRefl lhs)
      return (statement, proof)
  Lift.P1.addTheorem outputName statement proof

/-- Split one concrete RAM operation. Its error branch keeps the fault memory.
A successful write exposes the exact byte store for later separation rules. -/
elab "p2_ram_split" : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
  let findOperation := fun expression : Expr => expression.find? (fun e => !e.hasLooseBVars &&
    (e.isAppOfArity ``readRam 4 || e.isAppOfArity ``writeRam 5))
  let mut selected := findOperation target
  for declaration in ← getLCtx do
    if selected.isSome then break
    unless declaration.isImplementationDetail do
      let type ← instantiateMVars declaration.type
      -- A previous case equation records an operation already split.
      unless type.isAppOf ``Eq || type.isForall do
        selected := findOperation type
  let some operation := selected | throwError "p2_ram_split: no RAM operation"
  let operationSyntax ← Term.exprToSyntax operation
  if operation.isAppOf ``writeRam then
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      (rcases ramResult : $operationSyntax with ⟨reason, memory⟩ | memory
       all_goals try (have memoryEq := writeRam_memory _ _ _ _ _ _ ramResult; cases memoryEq))))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      rcases ramResult : $operationSyntax with ⟨reason, memory⟩ | value))

/-- Expose a symbolic path before expanding the register restoration conjunction. -/
elab "p2_path_split" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in ← getLCtx do
    unless declaration.isLet do
      let type ← instantiateMVars declaration.type
      let term ← Term.exprToSyntax declaration.toExpr
      let hypothesis ← `(Lean.Parser.Tactic.elimTarget| $term:term)
      let discardOriginal : Lean.Elab.Tactic.TacticM Unit := do
        Lean.Elab.Tactic.setGoals (← (← Lean.Elab.Tactic.getGoals).mapM
          (fun goal => goal.tryClear declaration.fvarId))
      if type.isAppOf ``Or then
        Lean.Elab.Tactic.evalTactic (← `(tactic| rcases $hypothesis with path | path))
        discardOriginal
        return
      if type.isAppOf ``And then
        Lean.Elab.Tactic.evalTactic (← `(tactic| rcases $hypothesis with ⟨left, right⟩))
        discardOriginal
        return
      if type.isAppOfArity ``Eq 3 && (type.getArg! 0).isConstOf ``MachineState then
        let left := type.getArg! 1
        let right := type.getArg! 2
        if (left.isFVar && right.isAppOf ``MachineState.mk) ||
            (right.isFVar && left.isAppOf ``MachineState.mk) then
          Lean.Elab.Tactic.evalTactic (← `(tactic| cases $hypothesis))
          discardOriginal
          return
      if type.isAppOf ``Exists then
        Lean.Elab.Tactic.evalTactic (← `(tactic| rcases $hypothesis with ⟨witness, path⟩))
        discardOriginal
        return
  throwError "p2_path_split: no path hypothesis"

/-- Split a closed branch condition after path and memory normalization. -/
elab "p2_condition_split" : tactic => Lean.Elab.Tactic.withMainContext do
  let findCondition := fun expression : Expr => do
    let branch ← expression.find? (fun e =>
      (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && !(e.getArg! 1).hasLooseBVars)
    return branch.getArg! 1
  let mut selected := findCondition (← instantiateMVars (← Lean.Elab.Tactic.getMainTarget))
  for declaration in ← getLCtx do
    if selected.isSome then break
    unless declaration.isImplementationDetail do
      let type ← instantiateMVars declaration.type
      unless type.isForall do
        selected := findCondition type
  let some condition := selected | throwError "p2_condition_split: no closed condition"
  let conditionSyntax ← Term.exprToSyntax condition
  Lean.Elab.Tactic.evalTactic (← `(tactic| by_cases branchCondition : $conditionSyntax))

/-- Expand one layer of each local proof path before normalizing its edge. -/
elab "p2_expand" : tactic => Lean.Elab.Tactic.withMainContext do
  -- Expose one visited state before opening later paths whose state is unknown.
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      let type ← instantiateMVars declaration.type
      if type.isAppOf ``visits then
        let term ← Term.exprToSyntax declaration.toExpr
        let hypothesis ← `(Lean.Parser.Tactic.locationHyp| $term:term)
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [visits] at $hypothesis))
        return
  let hasExpansion := fun expression : Expr =>
    (expression.find? (fun e => e.isAppOf ``unroll || e.isAppOf ``visits)).isSome
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if hasExpansion (← instantiateMVars declaration.type) then
        let hypothesis := mkIdent declaration.userName
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          first
          | conv at $hypothesis:ident => pattern (unroll _ _ _ _); rw [unroll]
          | conv at $hypothesis:ident => pattern (visits _ _ _ _); rw [visits]))
        return
  unless hasExpansion (← instantiateMVars (← Lean.Elab.Tactic.getMainTarget)) do
    throwError "p2_expand: no local expansion"
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    first
    | conv => pattern (unroll _ _ _ _); rw [unroll]
    | conv => pattern (visits _ _ _ _); rw [visits]))

/-- Normalize a finite correspondence goal, including failed byte accesses.
The caller supplies checked site equations and the definitions of its model. -/
macro "p2_nf" "[" extra:ident,* "]" : tactic => do
  let mut ruleNames : Array (TSyntax `ident) := #[]
  for name in extra.getElems do
    if name.getId == `Program.system || name.getId == `Lift.P2.Total.Program.system then
      ruleNames := ruleNames.push (mkIdent `Lift.P2.Total.program_step_nf)
      ruleNames := ruleNames.push (mkIdent `Lift.P2.Total.program_stop_nf)
    else
      ruleNames := ruleNames.push name
  let rules ← ruleNames.mapM fun name => `(Lean.Parser.Tactic.simpLemma| $name:ident)
  let normalize ← `(tactic| (simp (config := {failIfUnchanged := false, contextual := true})
    [*, -Bool.exists_bool, -Bool.forall_bool,
    cpu_step_nf, cpu_stop_nf, pureSystem,
    Handled.exec_all_iff, Handled.choice_iff, Handled.load_normalize, Handled.store_normalize,
    Handled.done_iff, Handled.fault_iff, exists_and_left,
    exists_and_right, and_assoc, int64_eq_comm, exists_unit_iff,
    exists_choice_relation, exists_choice_state, or_and_right, exists_or,
    readRam_mapped, loadInt_storeInt_separate, BitVec.ofInt_add, BitVec.add_comm, $[$rules],*] at *))
  `(tactic| (
      intros
      $normalize:tactic
      repeat' ((first | p2_guarded_footprint | p2_conditional_footprint | p2_ram_split | p2_condition_split | p2_path_split | p2_expand) <;> (intros; $normalize:tactic))
      all_goals try simp_all [AbiRestored]))

end Lift.P2.Total
