module

public import Lift.P1.Spec
public meta import Lift.P1.Spec
public meta import Lean

public meta section

open Lean Elab Command Meta

namespace Lift.P1

/-- Definitions to specialize. Machine arithmetic and memory remain shared primitives. -/
def syntaxReducers : List Name :=
  [``Directives.interp, ``Directive.interp, ``Instr.interp,
   ``Operation.interp, ``AvxOperation.interp,
   ``Reg.interp, ``RegOrMem.interp, ``Operand.interp,
   ``AvxRegOrMem.interp, ``AvxRegOrMem.interpLow32, ``AvxRegOrMem.interpLow64,
   ``AvxOperand.interp, ``RelRegOrMem.interp, ``ConstExpr.interp, ``AddrExpr.interp,
   ``ShiftCountExpr.interp, ``ShiftCountExpr.interpMasked, ``CondCode.interp,
   ``MachineData.set, ``MachineData.setAvx, ``MachineData.setAvxLegacy,
   ``MachineData.setReg, ``MachineData.setAvxReg, ``MachineData.setAvxLegacyReg,
   ``Reg64s.get, ``Reg64s.set, ``Reg64s.get64, ``Reg64s.set64, ``Reg.base, ``Reg.offset,
   ``RegZmms.get, ``RegZmms.set, ``RegZmms.setLegacy, ``RegZmms.get512,
   ``RegZmms.set512, ``AvxReg.base, ``Executable.labels,
   ``RegOrMem.isMem, ``btcBitString, ``addresses, ``labelsFor,
   ``List.takeWhile, ``List.map, ``List.findSome?]

/-- Reject residual syntax and the constants in `forbidden`. A partial specialization is not an
exact shallow lift. -/
def ensureShallow (body : Expr) (forbidden : List Name := []) : MetaM Unit := do
  let syntaxTypes := [``Directive, ``Instr, ``Operation, ``AvxOperation, ``Operand,
    ``AvxOperand, ``RegOrMem, ``AvxRegOrMem, ``RelRegOrMem, ``ConstExpr, ``AddrExpr,
    ``ShiftCountExpr, ``CondCode, ``Kraken.Executable, ``Kraken.Addressable, ``Kraken.Sized,
    ``Labels]
  forEachExpr' body fun e => do
    if (← isProof e) || (← isType e) then return false
    if e.isConst && ((syntaxReducers ++ forbidden).any (·.isPrefixOf e.constName!) ||
        syntaxTypes.any (·.isPrefixOf e.constName!)) then
      throwError "exact P1 could not specialize {e}; assembly syntax remains in the runtime"
    return true

/-- The simp set of `normalizeSite`: the default set, the syntax reducers and `extra` to unfold,
and the rewrite theorems `rules`. -/
def siteTheorems (extra : List Name := []) (rules : List Name := []) : MetaM SimpTheorems := do
  let thms ← (syntaxReducers ++ extra).foldlM (fun s n => s.addDeclToUnfold n) (← getSimpTheorems)
  let thms ← rules.foldlM (fun s n => s.addConst n) thms
  [``List.takeWhile_cons, ``List.map_cons, ``List.findSome?_cons].foldlM
    (fun s n => s.addConst n (post := false)) thms

/-- Simplify one term with `thms` and retain the proof. -/
def normalizeWith (thms : SimpTheorems) (site : Expr) : MetaM Simp.Result := do
  profileitM Exception "exact P1 simplify" (← getOptions) do
    let ctx ← Simp.mkContext (simpTheorems := #[thms])
    return (← simp site ctx #[← Simp.getSimprocs]).1

/-- Simplify one site and retain the proof, so work does not grow into one simp run. -/
def normalizeSite (site : Expr) (extra : List Name := []) : MetaM Simp.Result := do
  normalizeWith (← siteTheorems extra) site

def specialize (body : Expr) (extra : List Name := []) : MetaM Expr := do
  profileitM Exception "exact P1 unfold" (← getOptions) do
    let thms := (syntaxReducers ++ extra).foldl (fun s n => s.addDeclToUnfoldCore n) ({} : SimpTheorems)
    let ctx ← Simp.mkContext (config := { instances := true }) (simpTheorems := #[thms])
    return (← dsimp body ctx).1

def addDefinition (name : Name) (value : Expr) : CommandElabM Unit :=
  liftTermElabM do
    let decl := Declaration.defnDecl (mkDefinitionValEx name [] (← inferType value) value
      (.regular 0) .safe [name])
    addDecl decl (forceExpose := true)
    compileDecl decl
    enableRealizationsForConst name

def addTheorem (name : Name) (type value : Expr) : CommandElabM Unit :=
  liftTermElabM do
    addDecl (.thmDecl { name, levelParams := [], type, value })

/-- Check one table cell at a time; tail proofs are shared declarations. Site `i` simplifies with
`base` and unfolds the definitions `extra i`. No constant of the namespace `out` remains in a
site. -/
partial def generateSites (out : Name) (base : SimpTheorems) (extra : Nat → List Name)
    (rest : Expr) (index : Nat) : CommandElabM (Expr × Expr) := do
  let rest ← liftTermElabM <| withTransparency .all <| whnf rest
  let tailName := out ++ Name.mkSimple s!"tail{index}"
  let proofName := out ++ Name.mkSimple s!"tail{index}_eq"
  if rest.isAppOfArity ``List.nil 1 then
    addDefinition tailName rest
    let type ← liftTermElabM <| mkEq (mkConst tailName) rest
    addTheorem proofName type (← liftTermElabM <| mkEqRefl rest)
    return (mkConst tailName, mkConst proofName)
  unless rest.isAppOfArity ``List.cons 3 do throwError "cannot reduce executable table: {rest}"
  let oldPair ← liftTermElabM <| whnf (rest.getArg! 1)
  let thms ← liftTermElabM <| (extra index).foldlM (fun s n => s.addDeclToUnfold n) base
  let normalized ← liftTermElabM do
    try normalizeWith thms oldPair
    catch e => throwError "exact P1 site {index}: {e.toMessageData}"
  let pair ← liftTermElabM <| whnf normalized.expr
  unless pair.isAppOfArity ``Prod.mk 4 do throwError "cannot reduce executable site"
  let pc := pair.getArg! 2
  let code := pair.getArg! 3
  let name := out ++ Name.mkSimple s!"site{index}"
  -- Unfold instance arguments, then simplify the exposed constant label lookups.
  let unfolded ← liftTermElabM <| specialize code (extra index)
  let unfoldedPair ← liftTermElabM <| mkAppM ``Prod.mk #[pc, unfolded]
  let finalPair ← liftTermElabM <| normalizeWith thms unfoldedPair
  let pair ← liftTermElabM <| whnf finalPair.expr
  let body := pair.getArg! 3
  liftTermElabM do
    try
      ensureShallow body [out]
      ensureShallow pc [out]
    catch e => throwError "exact P1 site {index}: {e.toMessageData}"
  addDefinition name body
  let entry ← liftTermElabM <| mkAppM ``Prod.mk #[pc, mkConst name]
  let (tail, tailProof) ← generateSites out base extra (rest.getArg! 2) (index + 1)
  let cons ← liftTermElabM <| mkAppM ``List.cons #[entry, tail]
  addDefinition tailName cons
  let proof ← liftTermElabM do
    let headProof ← mkEqTrans (← mkEqSymm (← finalPair.getProof' unfoldedPair))
      (← mkEqSymm (← normalized.getProof' oldPair))
    let cons ← mkAppOptM ``List.cons #[some (mkConst ``Site)]
    let h ← mkAppM ``congrArg #[cons, headProof]
    mkCongr h tailProof
  let type ← liftTermElabM <| mkEq (mkConst tailName) rest
  addTheorem proofName type proof
  return (mkConst tailName, mkConst proofName)

/-- Compute only a static list's spine. Keep instruction terms for checked specialization. -/
partial def literalList (term : Expr) : MetaM Expr := withTransparency .all do
  let term ← whnf term
  if term.isAppOfArity ``List.nil 1 then return term
  unless term.isAppOfArity ``List.cons 3 do throwError "exact P1 needs a static directive list"
  let head ← whnf (term.getArg! 1)
  let tail ← literalList (term.getArg! 2)
  return mkAppN term.getAppFn #[term.getArg! 0, head, tail]

/-- The name of a label directive; `none` for another directive. -/
def labelName? (d : Expr) : MetaM (Option String) := withTransparency .all do
  let directive ← whnf (← mkAppM ``Kraken.Sized.directive #[d])
  if directive.isAppOfArity ``Directive.label 1 then
    match ← whnf (directive.getArg! 0) with
    | .lit (.strVal s) => return some s
    | name => throwError "exact P1 needs a literal label name: {name}"
  unless (← isConstructorApp directive) do
    throwError "exact P1 cannot reduce directive {directive}"
  return none

def layoutTailName (index : Nat) : Name := Name.mkSimple s!"layout{index}"

/-- Address one directive per step: `out.layout<index> = addresses pc program`. One simp run sees
one directive, not the program. Also returns the address and label name of each directive. -/
partial def generateLayout (out : Name) (thms : SimpTheorems) (pc program : Expr) (index : Nat) :
    CommandElabM (Expr × Expr × List (Expr × Option String)) := do
  let tailName := out ++ layoutTailName index
  let proofName := out ++ Name.mkSimple s!"layout{index}_eq"
  let lhs ← liftTermElabM <| mkAppM ``addresses #[pc, program]
  let unfolded ← liftTermElabM <| withTransparency .all <| whnf lhs
  if program.isAppOfArity ``List.nil 1 && unfolded.isAppOfArity ``List.nil 1 then
    addDefinition tailName unfolded
    let type ← liftTermElabM <| mkEq (mkConst tailName) lhs
    addTheorem proofName type (← liftTermElabM <| mkEqRefl unfolded)
    return (mkConst tailName, mkConst proofName, [])
  let next := unfolded.getArg! 2
  unless program.isAppOfArity ``List.cons 3 && unfolded.isAppOfArity ``List.cons 3 &&
      next.isAppOfArity ``addresses 2 do
    throwError "exact P1 cannot address directive {index}: {unfolded}"
  let rest := program.getArg! 2
  let headPair := unfolded.getArg! 1
  let nextPc := next.getArg! 0
  let head ← liftTermElabM <| normalizeWith thms headPair
  let advanced ← liftTermElabM <| normalizeWith thms nextPc
  let label ← liftTermElabM <| labelName? (program.getArg! 1)
  let (tail, tailProof, entries) ← generateLayout out thms advanced.expr rest (index + 1)
  let proof ← liftTermElabM do
    let cons ← mkAppOptM ``List.cons #[some (← inferType head.expr)]
    let hTail ← mkCongrArg (mkApp cons head.expr) tailProof
    let hHead ← mkCongrArg cons (← head.getProof' headPair)
    let hNext ← mkCongrFun
      (← mkCongrArg (mkConst ``addresses) (← advanced.getProof' nextPc)) rest
    mkEqTrans hTail (← mkEqSymm (← mkCongr hHead hNext))
  addDefinition tailName (← liftTermElabM <| mkAppM ``List.cons #[head.expr, tail])
  let type ← liftTermElabM <| mkEq (mkConst tailName) lhs
  addTheorem proofName type proof
  return (mkConst tailName, mkConst proofName, (pc, label) :: entries)

/-- The layout tails that site `index` reads: up to the first directive at another address. -/
def siteTails (out : Name) (pcs : Array Expr) (index : Nat) : List Name :=
  let same := ((List.range (pcs.size - index - 1)).takeWhile
    fun i => pcs[index + 1 + i]! == pcs[index]!).length
  (List.range (same + 1)).map fun i => out ++ layoutTailName (index + 1 + i)

/-- The string literals of a term, sorted. -/
def stringLiterals (e : Expr) : MetaM (List String) := do
  let found ← IO.mkRef ({} : Std.HashSet String)
  forEachExpr' e fun
    | .lit (.strVal s) => do found.modify (·.insert s); return false
    | _ => return true
  return (← found.get).toList.mergeSort (· < ·)

/-- A theorem `labels.label s = address` for each name `s`, checked by the kernel. The address of
the first label directive of `s` in `entries` is the value; a name without one has `-1`. -/
def addLabelRules (out labels : Name) (entries : List (Expr × Option String))
    (names : List String) : CommandElabM (List Name) := do
  let absent ← liftTermElabM do
    return (← normalizeSite (← mkAppM ``Neg.neg #[← mkNumeral (mkConst ``Int64) 1])).expr
  (names.zip (List.range names.length)).mapM fun (s, i) => do
    let value := ((entries.find? (·.2 == some s)).map (·.1)).getD absent
    let name := out ++ Name.mkSimple s!"label{i}"
    let type ← liftTermElabM do
      mkEq (← mkAppOptM ``Labels.label #[some (mkConst labels), some (mkStrLit s)]) value
    addTheorem name type (← liftTermElabM <| mkEqRefl value)
    return name

/-- The value of `labelsFor layout` as one simp run normalizes it, built one directive at a time,
and a proof of `value = labelsFor layout`. For each tail `k` (of `count + 1`) a theorem
`out.labels<k>_eq : ∀ l, findSome? (f l) out.layout<k> = r` gives the normal form `r` of the
lookup in that tail, from the one of tail `k + 1`. -/
def generateLabels (out layout : Name) (thms : SimpTheorems) (count : Nat) :
    MetaM (Expr × Expr) := do
  withLocalDeclD `ds (← inferType (mkConst layout)) fun ds => do
  let source ← mkAppM ``labelsFor #[ds]
  let general ← normalizeWith thms source
  let .app mk (.lam n type body bi) := general.expr
    | throwError "exact P1 cannot normalize the labels: {general.expr}"
  withLocalDecl n bi type fun l => do
  let body := body.instantiate1 l
  let some lookup := body.find? fun e => e.isAppOfArity ``List.findSome? 4 && e.appArg! == ds
    | throwError "exact P1 cannot find the label lookup in {body}"
  if (lookup.getArg! 2).containsFVar ds.fvarId! then
    throwError "exact P1 cannot normalize the label lookup {lookup}"
  let find (k : Nat) := mkApp lookup.appFn! (mkConst (out ++ layoutTailName k))
  let mut next : Option (Expr × Expr) := none
  for i in [0:count + 1] do
    let k := count - i
    let term := find k
    let step ← normalizeWith (← thms.addDeclToUnfold (out ++ layoutTailName k)) term
    let (r, proof) ← match next with
      | none => pure (step.expr, ← step.getProof' term)
      | some (r, eq) => do
        let motive ← kabstract step.expr (find (k + 1))
        let h ← mkCongrArg (.lam `x (← inferType term) motive .default) (mkApp eq l)
        pure (motive.instantiate1 r, ← mkEqTrans (← step.getProof' term) h)
    let name := out ++ Name.mkSimple s!"labels{k}_eq"
    let type ← instantiateMVars (← mkForallFVars #[l] (← mkEq term r))
    let value ← instantiateMVars (← mkLambdaFVars #[l] proof)
    addDecl (.thmDecl { name, levelParams := [], type, value })
    next := some (r, mkConst name)
  let some (r, eq) := next | throwError "exact P1 has no label lookup"
  let motive ← kabstract body lookup
  let value := mkApp mk (← mkLambdaFVars #[l] (motive.instantiate1 r))
  let h ← mkCongrArg (.lam `x (← inferType lookup) motive .default) (mkApp eq l)
  let tail ← mkCongrArg mk (← mkFunExt (← mkLambdaFVars #[l] h))
  let general ← instantiateMVars (← general.getProof' source)
  let proof ← mkEqTrans (general.replaceFVar ds (mkConst layout)) tail
  return (value, ← mkEqSymm proof)

/-- Generate shallow sites, their exact table, and an unconditional L1 theorem. -/
def liftExact (asmId outId : Ident) : CommandElabM Unit := do
  let asmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo asmId
  let out := (← getCurrNamespace) ++ outId.getId
  let asm := mkConst asmName
  let (value, ds) ← liftTermElabM do
    unless ← isDefEq (← inferType asm) (mkConst ``_root_.Executable) do
      throwErrorAt asmId "exact P1 needs an Executable with explicit addresses and sizes"
    let value ← withTransparency .all <| whnf asm
    unless value.isAppOfArity ``Kraken.Executable.mk 3 do
      throwErrorAt asmId "exact P1 needs a defined executable"
    let program ← literalList (value.getArg! 2)
    let value := mkAppN value.getAppFn #[value.getArg! 0, value.getArg! 1, program]
    return (value, ← mkAppM ``addresses #[value.getArg! 1, program])
  let pc := value.getArg! 1
  let program := value.getArg! 2
  let layoutName := out ++ `addressed
  let layoutEq := out ++ `addressed_eq
  let thms ← liftTermElabM <| siteTheorems
  let start ← liftTermElabM <| normalizeWith thms pc
  let (layoutTail, layoutTailEq, entries) ← generateLayout out thms start.expr program 0
  addDefinition layoutName layoutTail
  let layoutType ← liftTermElabM <| mkEq (mkConst layoutName) ds
  let layoutProof ← liftTermElabM do
    let hStart ← mkCongrFun
      (← mkCongrArg (mkConst ``addresses) (← start.getProof' pc)) program
    mkEqTrans layoutTailEq (← mkEqSymm hStart)
  addTheorem layoutEq layoutType layoutProof
  let labelsName := out ++ `labels
  let labelsEq := out ++ `labels_eq
  let labelTerm ← liftTermElabM <| mkAppM ``labelsFor #[mkConst layoutName]
  let (labels, labelProof) ← liftTermElabM <|
    generateLabels out layoutName thms entries.length
  addDefinition labelsName labels
  -- The equation `labels = value` that Lean otherwise generates on first use; generation
  -- simplifies the value, whose depth is the number of label directives.
  liftTermElabM do
    let name := mkEqLikeNameFor (← getEnv) labelsName eqn1ThmSuffix
    let type ← mkEq (mkConst labelsName) labels
    addDecl (.thmDecl { name, levelParams := [], type, value := ← mkEqRefl (mkConst labelsName) })
    inferDefEqAttr name
  let labelType ← liftTermElabM <| mkEq (mkConst labelsName) labelTerm
  addTheorem labelsEq labelType labelProof
  let rules ← addLabelRules out labelsName entries (← liftTermElabM <| stringLiterals program)
  let (reference, referenceProof, originalReference) ← liftTermElabM do
    let reference ← mkAppM ``reference #[mkConst labelsName, mkConst layoutName]
    let referenceFor ← withLocalDeclD `ds (← inferType (mkConst layoutName)) fun xs => do
      let labels ← mkAppM ``labelsFor #[xs]
      mkLambdaFVars #[xs] (← mkAppM ``reference #[labels, xs])
    let hLayout ← mkAppM ``congrArg #[referenceFor, ← mkEqSymm (mkConst layoutEq)]
    let hLabels ← mkAppM ``congrArg #[mkConst ``reference, ← mkEqSymm (mkConst labelsEq)]
    let proof ← mkEqTrans hLayout (← mkCongrFun hLabels (mkConst layoutName))
    return (reference, proof, mkApp (mkConst ``structuralReference) value)
  let base ← liftTermElabM <| siteTheorems [] rules
  let (tail, tableProof) ← generateSites out base (siteTails out (entries.map (·.1)).toArray)
    reference 0
  let eqProof ← liftTermElabM do mkEqTrans tableProof (← mkEqSymm referenceProof)
  let table := out ++ `table
  addDefinition table tail
  let eqName := out ++ `table_eq
  let eqType ← liftTermElabM <| mkEq (mkConst table) originalReference
  addTheorem eqName eqType eqProof
  addDefinition (out ++ `step) (mkApp (mkConst ``dispatch) (mkConst table))
  -- `table_eq` states the reference of the unfolded `asm`. The kernel checks that it is `asm`;
  -- `mkAppM` would compare the two programs with a deep `isDefEq`.
  let spec := mkAppN (mkConst ``of_structural_table) #[asm, mkConst table, mkConst eqName]
  let specType ← liftTermElabM <| mkAppM ``L1Spec #[asm, mkConst (out ++ `step)]
  addTheorem (out ++ `spec) specType spec

elab "#lift_exact " asm:ident " as " out:ident : command => liftExact asm out

end Lift.P1
