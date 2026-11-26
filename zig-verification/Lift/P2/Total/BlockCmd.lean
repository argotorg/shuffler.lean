module

public import Lift.P2.Total.BlockEntry
public import Lift.P2.Total.BlockNormalize
public import Lift.P2.Total.Normalize
public meta import Lean
public meta import Lift.P2.Total.CheckedCmd
public meta import Lift.P2.Total.BlockStage
public meta import Lift.P2.Total.ChunkStage
public meta import Lift.P2.Total.CallsSpecialize
public meta import Lift.P2.Total.BlockSafetyTactic

public meta section

open Lean Elab Command Meta

namespace Lift.P2.Total

/-- Equation indexed by the constructor form exposed when a PC equality is
substituted. The numeral and constructor forms are definitionally equal, but
the simplifier can index them by different expression heads. -/
elab "#p2_block_step_eq " step:ident " at " pc:num " as " output:ident : command =>
  withScope (fun scope => { scope with opts := scope.opts.insert `maxRecDepth (.ofNat 20000) }) do
    let stepName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo step
    let outputName := (← getCurrNamespace) ++ output.getId
    let (statement, proof) ← liftTermElabM do
      let literal : TSyntax `term := ⟨pc.raw⟩
      let addressSyntax ← `(term| ({toUInt64 := $literal} : Int64))
      let address ← Term.elabTerm addressSyntax (some (mkConst ``Int64))
      withLocalDeclD `data (mkConst ``MachineData) fun data => do
        let state ← mkAppM ``MachineState.mk #[data, address]
        let lhs := mkApp (mkConst stepName) state
        let rhs ← withTransparency .all <| whnf lhs
        let statement ← mkForallFVars #[data] (← mkEq lhs rhs)
        let proof ← mkLambdaFVars #[data] (← mkEqRefl lhs)
        return (statement, proof)
    Lift.P1.addTheorem outputName statement proof

/-- Specialize a block root before expanding its bounded local paths. -/
elab "p2_block_roots " relation:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let relationName ← realizeGlobalConstNoOverloadWithInfo relation
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      let type ← instantiateMVars declaration.type
      if type.isAppOf relationName then
        let term ← Term.exprToSyntax declaration.toExpr
        let hypothesis ← `(Lean.Parser.Tactic.location| at $term:term)
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $relation $hypothesis:location))
  Lean.Elab.Tactic.evalTactic (← `(tactic| repeat' p2_path_split))
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try subst_vars))

elab "p2_block_expand_hyp" : tactic => Lean.Elab.Tactic.withMainContext do
  let hasUnroll := fun e : Expr => (e.find? (·.isAppOf ``unroll)).isSome
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if hasUnroll declaration.type then
        let term ← Term.exprToSyntax declaration.toExpr
        let location ← `(Lean.Parser.Tactic.location| at $term:term)
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          first | rw [unroll_block_pending] $location:location |
            rw [unroll_block_next] $location:location |
            simp (config := {singlePass := true}) only [unroll] $location:location))
        return
  throwError "p2_block_expand_hyp: no local expansion"

elab "p2_block_expand" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    first
    | p2_block_expand_hyp
    | rw [unroll_block_pending]
    | rw [unroll_block_next]
    | simp (config := {singlePass := true}) only [unroll]))

/-- Use exact successful reads to check the remaining relation obligations. -/
elab "p2_block_read_close" "{" normalize:tacticSeq "}" : tactic =>
    Lean.Elab.Tactic.withMainContext do
  let saved ← Lean.Elab.Tactic.saveState
  try
    let mut found := false
    for declaration in ← getLCtx do
      unless declaration.isImplementationDetail do
        let type ← instantiateMVars declaration.type
        if type.isAppOfArity ``Eq 3 then
          let operation := type.getArg! 1
          let result := type.getArg! 2
          if operation.isAppOfArity ``readRam 4 && result.isAppOfArity ``Except.ok 3 then
            let proof ← mkAppM ``readRam_ok_witness
              (operation.getAppArgs ++ #[result.getArg! 2, declaration.toExpr])
            let evidence ← Term.exprToSyntax proof
            Lean.Elab.Tactic.evalTactic (← `(tactic|
              rcases ($evidence:term) with ⟨readWord, readMapped, readAllowed, readValue⟩))
            found := true
    unless found do throwError "p2_block_read_close: no successful read"
    Lean.Elab.Tactic.evalTactic (← `(tactic| ($normalize:tacticSeq)))
    unless (← Lean.Elab.Tactic.getGoals).isEmpty do
      throwError "p2_block_read_close: relation remains open"
  catch error =>
    saved.restore
    throw error

/-- Expand one bounded layer, then normalize its edge before the next layer.
This keeps an existential next state from causing symbolic path expansion. -/
macro "p2_block_nf" "[" extra:ident,* "]" : tactic => do
  let rules ← extra.getElems.mapM fun name => `(Lean.Parser.Tactic.simpLemma| $name:ident)
  let normalize ← `(tactic| ((try p2_call_specialize); (try p2_call_read_facts); try simp_all [-Bool.exists_bool, -Bool.forall_bool, visits, cpuSystem, pureSystem,
    Handled.exec_all_iff, Handled.choice_iff, Handled.load_normalize, Handled.store_normalize,
    Handled.done_iff, Handled.fault_iff, exists_and_left,
    exists_and_right, and_assoc, int64_eq_comm, exists_unit_iff,
    exists_choice_state, exists_two_choice_state, shiftLeft_zero_iff_mask, or_and_right, exists_or,
    Except.mapError, readRam_mapped, loadInt_storeInt_separate, BitVec.ofInt_add, BitVec.add_comm, int64_ofBitVec_eq_iff, $[$rules],*]))
  `(tactic| (
    intros
    $normalize:tactic
    repeat' ((first | p2_block_safety_expand | p2_ram_split | p2_condition_split | p2_path_split |
      p2_block_expand) <;>
      (intros; $normalize:tactic))
    all_goals try simp_all [-Bool.exists_bool, -Bool.forall_bool, AbiRestored]
    all_goals try p2_block_read_close { $normalize:tactic }
    all_goals try p2_block_safety_close { $normalize:tactic }))

/-- Inspect proposition structure only. Function types inside state witnesses
are part of a path expression, not quantified facts that must stay closed. -/
private partial def hasQuantifiedFact (type : Expr) : Bool :=
  if type.isForall then true
  else if type.isAppOfArity ``And 2 || type.isAppOfArity ``Or 2 then
    hasQuantifiedFact (type.getArg! 0) || hasQuantifiedFact (type.getArg! 1)
  else false

/-- Keep systems opaque inside later unrolls, and expose only their projections. -/
elab "p2_block_context_simp" "[" extra:ident,* "]" : tactic =>
    Lean.Elab.Tactic.withMainContext do
  let rules ← extra.getElems.mapM fun name => `(Lean.Parser.Tactic.simpLemma| $name:ident)
  let simpSyntax ← `(tactic| simp (config := {failIfUnchanged := false, contextual := true})
    [-Bool.exists_bool, -Bool.forall_bool, $[$rules],*])
  let settings ← Lean.Elab.Tactic.mkSimpContext simpSyntax (eraseLocal := false)
  let mut context := settings.ctx
  for fvar in ← getPropHyps do
    let type := (← fvar.getDecl).type
    if type.isAppOf ``GuardedFootprint.RangeProof ||
        type.isAppOfArity ``Calls.ReadBridge 6 || hasQuantifiedFact type then
      context := context.setSimpTheorems
        (context.simpTheorems.eraseTheorem (.fvar fvar))
  let (result?, _) ← callIndexedSimpAll (← Lean.Elab.Tactic.getMainGoal) context
    (simprocs := settings.simprocs)
  match result? with
  | none => Lean.Elab.Tactic.replaceMainGoal []
  | some goal => Lean.Elab.Tactic.replaceMainGoal [goal]

/-- Extract one logical witness without making a second proof path. -/
elab "p2_block_unpack" : tactic => do
  let saved ← Lean.Elab.Tactic.saveState
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| p2_path_split))
    if (← Lean.Elab.Tactic.getGoals).length > 1 then
      throwError "p2_block_unpack: path branches"
  catch error =>
    saved.restore
    throw error

/-- Return branch goals to the checked chunk driver before more machine actions. -/
elab "p2_block_until_branch " count:num "{" action:tacticSeq "}"
    "{" clean:tacticSeq "}" : tactic => do
  let cleanTactic ← `(tactic| ($clean:tacticSeq))
  let actionTactic ← `(tactic| ($action:tacticSeq))
  Lean.Elab.Tactic.evalTactic cleanTactic
  for _ in [:count.getNat] do
    unless (← Lean.Elab.Tactic.getGoals).length == 1 do return
    let saved ← Lean.Elab.Tactic.saveState
    try
      Lean.Elab.Tactic.evalTactic actionTactic
    catch _ =>
      saved.restore
      return
    unless (← Lean.Elab.Tactic.getGoals).length == 1 do return
    Lean.Elab.Tactic.evalTactic cleanTactic

private def blockPathTactic (extra : Array (TSyntax `ident)) (expand : TSyntax `tactic)
    (bounded : Bool := false) (steps : Nat := 32) : MacroM (TSyntax `tactic) := do
  let hasProgram := extra.any fun name =>
    [`Program.system, `Lift.P2.Total.Program.system].contains name.getId.eraseMacroScopes
  let mut ruleNames := extra.filter fun name => ![
    `blockSystem, `Lift.P2.Total.blockSystem,
    `cpuSystem, `Lift.P2.Total.cpuSystem,
    `Program.system, `Lift.P2.Total.Program.system].contains name.getId.eraseMacroScopes
  if hasProgram then
    ruleNames := ruleNames ++ #[mkIdent `Lift.P2.Total.program_step_nf,
      mkIdent `Lift.P2.Total.program_stop_nf]
  let rules := ruleNames
  let normalize ← `(tactic| ((try p2_call_specialize); (try p2_call_read_facts); p2_block_context_simp [
    visits, block_step_nf, block_stop_nf,
    cpu_step_nf, cpu_stop_nf, pureSystem,
    Handled.exec_all_iff, Handled.choice_iff, Handled.load_normalize, Handled.store_normalize,
    Handled.done_iff, Handled.fault_iff, exists_and_left,
    exists_and_right, and_assoc, int64_eq_comm, exists_unit_iff,
    exists_choice_state, exists_two_choice_state, shiftLeft_zero_iff_mask, or_and_right, exists_or,
    Except.mapError, readRam_mapped, loadInt_storeInt_separate,
    BitVec.ofInt_add, BitVec.add_comm, int64_ofBitVec_eq_iff, $[$rules],*]))
  let actions := #[← `(tactic| p2_block_safety_expand), ← `(tactic| p2_ram_split),
    ← `(tactic| p2_path_split), expand, ← `(tactic| p2_condition_split)]
  let unpack ← `(tactic| (intros; repeat' (p2_block_unpack; intros)))
  let clean ← if bounded then `(tactic| (
    $unpack:tactic
    $normalize:tactic
    repeat' ((p2_block_unpack; $unpack:tactic) <;> $normalize:tactic)
    try (p2_path_split <;> $unpack:tactic)))
    else `(tactic| (
      intros
      $normalize:tactic
      repeat' (p2_path_split <;> (intros; $normalize:tactic))))
  let step ← `(tactic| ((first $[| $actions:tactic]*) <;> $clean:tactic))
  let count : TSyntax `num := ⟨Syntax.mkNumLit (toString steps)⟩
  if bounded then
    return ← `(tactic| p2_block_until_branch $count:num
      { first $[| $actions:tactic]* } { $clean:tactic })
  let paths ← `(tactic| repeat' $step:tactic)
  let finish ← if bounded then `(tactic| skip)
    else `(tactic| all_goals try simp_all [-Bool.exists_bool, -Bool.forall_bool, AbiRestored])
  `(tactic| (
    $clean:tactic
    $paths:tactic
    $finish:tactic))

/-- Expose an initial part of each hypothesis path. The checked path helpers
expand the remaining layers in separate declarations. -/
macro "p2_block_prepare" "[" extra:ident,* "]" : tactic => do
  blockPathTactic extra.getElems (← `(tactic| p2_block_expand_hyp)) true

/-- Limit one proof chunk to the proposed number of path actions. -/
macro "p2_block_prepare" steps:num "[" extra:ident,* "]" : tactic => do
  blockPathTactic extra.getElems (← `(tactic| p2_block_expand_hyp)) true steps.getNat

/-- Continue either a hypothesis path or the matching path in one checked chunk. -/
macro "p2_block_chunk" "[" extra:ident,* "]" : tactic => do
  blockPathTactic extra.getElems (← `(tactic| p2_block_expand)) true 4

/-- Select the action count for a checked continuation chunk. -/
macro "p2_block_chunk" steps:num "[" extra:ident,* "]" : tactic => do
  blockPathTactic extra.getElems (← `(tactic| p2_block_expand)) true steps.getNat

/-- Normalize path evidence once per expanded layer. The output relation stays
opaque until all local paths have been exposed. -/
macro "p2_block_path_nf" "[" extra:ident,* "]" : tactic => do
  blockPathTactic extra.getElems (← `(tactic| p2_block_expand))

/-- Generate each finite block obligation and check the complete declaration.
The proposed systems, cuts, relation and local depths remain untrusted input. -/
elab "#p2_blocks " "(" left:ident "," right:ident ")"
    " cuts " "(" leftCut:ident "," rightCut:ident ")" " via " relation:ident
    " depths " "(" leftDepth:num "," rightDepth:num ")"
    " unfold " "[" extra:ident,* "]"    " as " output:ident : command => do
  for rule in extra.getElems do
    discard <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo rule
  let sourceTerm : TSyntax `term := ⟨leftDepth.raw⟩
  let targetTerm : TSyntax `term := ⟨rightDepth.raw⟩
  let rules := extra.getElems
  let generated ← `(theorem $output : Lift.P2.Total.BlockMatch $left $right
      $leftCut $rightCut $relation := by
    apply Lift.P2.Total.BlockMatch.of_unroll $left $right $leftCut $rightCut $relation
      (fun _ => $sourceTerm) (fun _ => $targetTerm)
    all_goals
      intros
      p2_block_roots $relation
      all_goals p2_block_nf [Lift.P2.Total.BlockClosed, Lift.P2.Total.blockSystem, $rules,*]
      all_goals first | rfl | grind)
  generateChecked #[generated] #[((← getCurrNamespace) ++ output.getId)]

declare_syntax_cat p2BlockEntry
syntax "entry_prefix " ident " (" num ")" : p2BlockEntry

declare_syntax_cat p2BlockChunks
syntax "chunks " "(" num "," num ")" : p2BlockChunks

declare_syntax_cat p2BlockFacts
syntax "facts " "[" ident,* "]" : p2BlockFacts

declare_syntax_cat p2BlockPathFacts
syntax "path_facts " "[" ident,* "]" : p2BlockPathFacts

declare_syntax_cat p2BlockRootPathFact
syntax ident " => " "[" ident,* "]" : p2BlockRootPathFact

declare_syntax_cat p2BlockRootPathFacts
syntax "root_path_facts " "[" p2BlockRootPathFact,* "]" : p2BlockRootPathFacts

declare_syntax_cat p2BlockObligation
syntax "cuts" : p2BlockObligation
syntax ident : p2BlockObligation

declare_syntax_cat p2BlockReuse
syntax p2BlockObligation ident " => " ident : p2BlockReuse

declare_syntax_cat p2BlockReuses
syntax "reuse " "[" p2BlockReuse,* "]" : p2BlockReuses

declare_syntax_cat p2BlockTask
syntax "#p2_block_call " : p2BlockTask
syntax "#p2_block_obligation " p2BlockObligation ident : p2BlockTask

/-- Generate a call theorem from local block certificates. Each proposed cut
and relation can depend on the initial call, policy and return word.
The obligation command checks one root proof and emits no call theorem. -/
elab task:p2BlockTask asm:ident " with " "(" step:ident "," exactProof:ident ")"
    " using " "(" boundary:ident "," contract:ident "," model:ident ")"
    " cuts " "(" sourceCut:ident "," targetCut:ident ")" " via " relation:ident
    " roots " "[" roots:ident,* "]" entryOptions:(p2BlockEntry)?
    factsOption:(p2BlockFacts)? pathFactsOption:(p2BlockPathFacts)?
    rootPathFactsOption:(p2BlockRootPathFacts)?
    reusesOption:(p2BlockReuses)?
    " depths " "(" sourceDepth:num "," targetDepth:num ")" chunksOption:(p2BlockChunks)?
    " sites " "[" sites:num,* "]" " unfold " "[" extra:ident,* "]"
    " as " output:ident : command => do
  for rule in extra.getElems do
    discard <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo rule
  let (chunkStages, chunkActions) ← match chunksOption with
    | some option => do
      let `(p2BlockChunks| chunks ($stageCount:num, $actionCount:num)) := option |
        throwError "block proof chunks"
      if stageCount.getNat == 0 || actionCount.getNat == 0 then
        throwError "block proof chunks require positive stages and actions"
      pure (stageCount, actionCount)
    | none => pure (⟨Syntax.mkNumLit "12"⟩, ⟨Syntax.mkNumLit "4"⟩)
  let initialFacts ← match factsOption with
    | some option => do
      let `(p2BlockFacts| facts [$helpers:ident,*]) := option | throwError "block facts"
      helpers.getElems.mapM fun helper => `(tactic| have := $helper policy word initial valid)
    | none => pure #[]
  let initialPrelude ← if initialFacts.isEmpty then `(tactic| skip)
    else `(tactic| ($[$initialFacts:tactic]*))
  let pathFacts ← match pathFactsOption with
    | some option => do
      let `(p2BlockPathFacts| path_facts [$helpers:ident,*]) := option | throwError "block path facts"
      helpers.getElems.mapM fun helper => `(tactic| have := $helper policy word initial valid)
    | none => pure #[]
  let allPathFacts := initialFacts ++ pathFacts
  let rootNames ← roots.getElems.mapM fun root =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let parseObligation := fun (kind : TSyntax `p2BlockObligation) => do
    match kind with
    | `(p2BlockObligation| cuts) => pure `cuts
    | `(p2BlockObligation| $name:ident) => pure name.getId.eraseMacroScopes
    | _ => throwError "block obligation name"
  let obligationNames := #[`cuts, `leftClosed, `rightClosed, `forward, `backward,
    `terminal, `entry, `returnCut, `exit]
  let selection ← match task with
    | `(p2BlockTask| #p2_block_call) => pure none
    | `(p2BlockTask| #p2_block_obligation $kind:p2BlockObligation $root:ident) => do
      let kind ← parseObligation kind
      unless obligationNames.contains kind do
        throwError "block obligation selection has an unknown obligation"
      let rootName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
      unless rootNames.contains rootName do
        throwError "block obligation selection names a relation outside roots"
      pure <| some (kind, rootName)
    | _ => throwError "block proof task"
  let rootPathFacts ← match rootPathFactsOption with
    | some option => do
      let `(p2BlockRootPathFacts| root_path_facts [$entries:p2BlockRootPathFact,*]) := option |
        throwError "block root path facts"
      let mut parsed : Array (Name × Array (TSyntax `ident)) := #[]
      for entry in entries.getElems do
        let `(p2BlockRootPathFact| $root:ident => [$helpers:ident,*]) := entry |
          throwError "block root path fact"
        let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
        unless rootNames.contains name do
          throwError "root path facts name a relation outside roots"
        if parsed.any (fun (prior, _) => prior == name) then
          throwError "root path facts repeat a relation"
        parsed := parsed.push (name, helpers.getElems)
      pure parsed
    | none => pure #[]
  let reuses ← match reusesOption with
    | some option => do
      let `(p2BlockReuses| reuse [$entries:p2BlockReuse,*]) := option |
        throwError "block obligation reuse"
      let mut parsed : Array (Name × Name × TSyntax `ident) := #[]
      for entry in entries.getElems do
        let `(p2BlockReuse| $kind:p2BlockObligation $root:ident => $proof:ident) := entry |
          throwError "block obligation reuse"
        let kind ← parseObligation kind
        unless obligationNames.contains kind do
          throwError "block obligation reuse has an unknown obligation"
        let rootName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
        unless rootNames.contains rootName do
          throwError "block obligation reuse names a relation outside roots"
        if parsed.any (fun (priorKind, priorRoot, _) =>
            priorKind == kind && priorRoot == rootName) then
          throwError "block obligation reuse repeats an obligation and relation"
        let proofName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo proof
        let proofInfo ← liftCoreM <| getConstInfo proofName
        -- Module imports expose theorem signatures as axioms. Their recorded
        -- dependencies distinguish them from declarations of new axioms.
        let exportedTheorem ← if proofInfo.isAxiom then do
          let axioms ← liftCoreM <| collectAxioms proofName
          pure <| (← getEnv).isImportedConst proofName && !axioms.contains proofName
        else pure false
        unless proofInfo.isTheorem || exportedTheorem do
          throwError "block obligation reuse requires a theorem: {proofName}"
        parsed := parsed.push (kind, rootName, proof)
      pure parsed
    | none => pure #[]
  let relationRules := #[relation] ++ roots.getElems
  let mut rules := extra.getElems.filter fun name =>
    !relationRules.any (fun rule => rule.getId == name.getId)
  let mut commands : Array (TSyntax `command) := #[]
  for pc in sites.getElems, index in [:sites.getElems.size] do
    let name := mkIdent (output.getId ++ Name.mkSimple s!"site{index}")
    let expanded := mkIdent (output.getId ++ Name.mkSimple s!"siteExpanded{index}")
    commands := commands.push (← `(#p2_step_eq $step at $pc as $name))
    commands := commands.push (← `(#p2_block_step_eq $step at $pc as $expanded))
    rules := rules.push name
    rules := rules.push expanded
  let theoremName := mkIdent (output.getId ++ `spec)
  let sourceTerm : TSyntax `term := ⟨sourceDepth.raw⟩
  let targetTerm : TSyntax `term := ⟨targetDepth.raw⟩
  let source ← `(Lift.P2.Total.cpuSystem $step policy
    (($boundary word).returned initial) (($boundary word).visible initial))
  let target ← `(($model policy).system)
  let (entryTarget, prefixDepth) ← match entryOptions with
    | some option => do
      let `(p2BlockEntry| entry_prefix $point:ident ($depth:num)) := option | throwError "entry prefix"
      let target ← `($point policy word initial)
      pure (target, (⟨depth.raw⟩ : TSyntax `term))
    | none => do
      let target ← `(($model policy).entry initial)
      pure (target, (← `(term| 0)))
  let prefixProof := mkIdent (output.getId ++ `entryPrefix)
  if selection.isNone then
    commands := commands.push (← `(theorem $prefixProof (policy : Lift.P2.Total.CpuPolicy)
      (word : Int) (initial : MachineState) (valid : $contract policy word initial) :
      Lift.P2.Total.PurePrefix $target $prefixDepth (($model policy).entry initial) $entryTarget := by
    $initialPrelude:tactic
    rcases initial with ⟨data, pc⟩
    try cases valid
    p2_block_nf [Lift.P2.Total.PurePrefix, $rules,*]
    all_goals first | rfl | grind))
  let makeObligations := fun (rootRelation : TSyntax `ident) => do
    let obligations : Array (Name × TSyntax `term) := #[
    (`cuts, ← `(∀ a b, $rootRelation policy word initial a b →
      $sourceCut policy word initial a ∧ $targetCut policy word initial b)),
    (`leftClosed, ← `(∀ a b, $rootRelation policy word initial a b →
      Lift.P2.Total.BlockClosed $source ($sourceCut policy word initial) $sourceTerm a)),
    (`rightClosed, ← `(∀ a b, $rootRelation policy word initial a b →
      Lift.P2.Total.BlockClosed $target ($targetCut policy word initial) $targetTerm b)),
    (`forward, ← `(∀ a b next, $rootRelation policy word initial a b →
      Lift.P2.Total.unroll (Lift.P2.Total.blockSystem $source ($sourceCut policy word initial))
        $sourceTerm a (.finished (.next next)) →
      ∃ matched, Lift.P2.Total.unroll
        (Lift.P2.Total.blockSystem $target ($targetCut policy word initial))
        $targetTerm b (.finished (.next matched)) ∧ $relation policy word initial next matched)),
    (`backward, ← `(∀ a b next, $rootRelation policy word initial a b →
      Lift.P2.Total.unroll (Lift.P2.Total.blockSystem $target ($targetCut policy word initial))
        $targetTerm b (.finished (.next next)) →
      ∃ matched, Lift.P2.Total.unroll
        (Lift.P2.Total.blockSystem $source ($sourceCut policy word initial))
        $sourceTerm a (.finished (.next matched)) ∧ $relation policy word initial matched next)),
    (`terminal, ← `(∀ a b out, $rootRelation policy word initial a b →
      (Lift.P2.Total.unroll (Lift.P2.Total.blockSystem $source ($sourceCut policy word initial))
        $sourceTerm a (.finished (.finished out)) ↔
      Lift.P2.Total.unroll (Lift.P2.Total.blockSystem $target ($targetCut policy word initial))
        $targetTerm b (.finished (.finished out))))),
    (`entry, ← `($relation policy word initial initial $entryTarget)),
    (`returnCut, ← `(∀ final value, ($boundary word).returned initial final = some value →
      $sourceCut policy word initial final)),
    (`exit, ← `(∀ final a value, $rootRelation policy word initial final a →
      ($boundary word).returned initial final = some value → Lift.P2.Total.AbiRestored initial final))]
    return obligations
  let obligations ← makeObligations relation
  let mut audit : Array Name := #[]
  for (suffix, obligation) in obligations, obligationIndex in [:obligations.size] do
    if selection.any (fun (kind, _) => kind != suffix) then continue
    let helper := mkIdent (output.getId ++ suffix)
    let mut rootHelpers : Array (TSyntax `ident) := #[]
    for rootRelation in roots.getElems, rootIndex in [:roots.getElems.size] do
      let rootName := rootNames[rootIndex]!
      if selection.any (fun (_, root) => root != rootName) then continue
      let rootHelper := mkIdent (output.getId ++ suffix ++ Name.mkSimple s!"root{rootIndex}")
      audit := audit.push ((← getCurrNamespace) ++ rootHelper.getId)
      rootHelpers := rootHelpers.push rootHelper
      let rootObligations ← makeObligations rootRelation
      let rootObligation := rootObligations[obligationIndex]!.2
      if let some (_, _, reuseProof) := reuses.find? (fun (kind, root, _) =>
          kind == suffix && root == rootName) then
        commands := commands.push (← `(theorem $rootHelper :
            ∀ (policy : Lift.P2.Total.CpuPolicy) (word : Int) (initial : MachineState)
              (valid : $contract policy word initial), $rootObligation := $reuseProof))
      else if [`leftClosed, `rightClosed, `forward, `backward, `terminal].contains suffix then
        let rootFactHelpers := (rootPathFacts.find? (fun (name, _) => name == rootName)).map
          (fun (_, helpers) => helpers) |>.getD #[]
        let rootFacts ← rootFactHelpers.mapM fun helper =>
          `(tactic| have := $helper policy word initial valid)
        let rootInitialFacts := if [`forward, `backward, `terminal].contains suffix
          then allPathFacts ++ rootFacts else initialFacts
        let rootPathPrelude ← if rootInitialFacts.isEmpty then `(tactic| skip)
          else `(tactic| ($[$rootInitialFacts:tactic]*))
        let splitTerminal ← if suffix == `terminal then `(tactic| constructor) else `(tactic| skip)
        commands := commands.push (← `(#p2_chunked $rootHelper :
            ∀ (policy : Lift.P2.Total.CpuPolicy) (word : Int) (initial : MachineState)
              (valid : $contract policy word initial), $rootObligation stages $chunkStages:num
          prepare {
            intros policy word initial valid
            $rootPathPrelude:tactic
            rcases initial with ⟨data, pc⟩
            try cases valid
            intros
            p2_block_roots $rootRelation
            all_goals try p2_block_safety $targetDepth
            all_goals $splitTerminal:tactic
            all_goals p2_block_prepare $chunkActions:num [Lift.P2.Total.BlockClosed, Lift.P2.Total.blockSystem, $rules,*]
          }
          continue {
            p2_block_chunk $chunkActions:num [Lift.P2.Total.BlockClosed, Lift.P2.Total.blockSystem, $rules,*]
          }
          complete {
            p2_block_path_nf [Lift.P2.Total.BlockClosed, Lift.P2.Total.blockSystem, $rules,*]
            all_goals p2_block_nf [Lift.P2.Total.WordRules.take_eq_setWidth, $relationRules,*, $rules,*]
            all_goals first
            | rfl
            | grind
            | run_tac do
                let goal ← Lean.Elab.Tactic.getMainGoal
                Lean.throwError (α := Unit) m!"P2 block residual:\n{← Lean.Meta.ppGoal goal}"
          }))
      else
        commands := commands.push (← `(theorem $rootHelper (policy : Lift.P2.Total.CpuPolicy)
            (word : Int) (initial : MachineState) (valid : $contract policy word initial) :
            $rootObligation := by
          $initialPrelude:tactic
          rcases initial with ⟨data, pc⟩
          try cases valid
          intros
          p2_block_roots $rootRelation
          all_goals p2_block_path_nf [Lift.P2.Total.BlockClosed, Lift.P2.Total.blockSystem, $rules,*]
          all_goals p2_block_nf [Lift.P2.Total.WordRules.take_eq_setWidth, $relationRules,*, $rules,*]
          all_goals first | rfl | grind))
    if selection.isSome then continue
    let rootRules ← rootHelpers.mapM fun name =>
      `(Lean.Parser.Tactic.SolveByElim.arg| $name:term)
    commands := commands.push (← `(theorem $helper (policy : Lift.P2.Total.CpuPolicy)
        (word : Int) (initial : MachineState) (valid : $contract policy word initial) :
        $obligation := by
      intros
      first
      | solve_by_elim [$[$rootRules],*]
      | p2_block_roots $relation
        all_goals solve_by_elim [$[$rootRules],*]))
  if selection.isSome then
    generateChecked commands audit
    return
  let cutsProof := mkIdent (output.getId ++ `cuts)
  let leftClosed := mkIdent (output.getId ++ `leftClosed)
  let rightClosed := mkIdent (output.getId ++ `rightClosed)
  let forward := mkIdent (output.getId ++ `forward)
  let backward := mkIdent (output.getId ++ `backward)
  let terminal := mkIdent (output.getId ++ `terminal)
  let entryProof := mkIdent (output.getId ++ `entry)
  let returnCut := mkIdent (output.getId ++ `returnCut)
  let exit := mkIdent (output.getId ++ `exit)
  commands := commands.push (← `(theorem $theoremName (policy : Lift.P2.Total.CpuPolicy)
      (word : Int) : Lift.P2.Total.CallSpec $asm policy ($boundary word)
        ($contract policy word) ($model policy) := by
    apply Lift.P2.Total.CallSpec.of_blocks_at_returns_prefix _ _ $exactProof _ _ _ _
      ($sourceCut policy word) ($targetCut policy word) ($relation policy word)
      (fun initial => $entryTarget) $prefixDepth
    · intro initial valid
      exact Lift.P2.Total.BlockMatch.of_unroll _ _ _ _ _
        (fun _ => $sourceTerm) (fun _ => $targetTerm)
        ($cutsProof policy word initial valid) ($leftClosed policy word initial valid)
        ($rightClosed policy word initial valid) ($forward policy word initial valid)
        ($backward policy word initial valid) ($terminal policy word initial valid)
    · exact $prefixProof policy word
    · exact $entryProof policy word
    · exact $returnCut policy word
    · exact $exit policy word))
  generateChecked commands #[((← getCurrNamespace) ++ theoremName.getId)]

end Lift.P2.Total
